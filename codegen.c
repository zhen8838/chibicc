#include "chibicc.h"

#define GP_MAX 6
#define FP_MAX 0 // 这里把浮点寄存器的个数改成0.
#define GP_WIDTH 4

/**
 * @brief 检查有符号的imm是否超过12位
 *    NOTE
 * LUI/AUIPC/ADDI/LW/LH/LHU/LB/LBU/SW/SH/SB/BEQ/BNE/BLT/BLTU/BGE/BGEU/JALR
 *         以上offset 必须小于12位.
 * @param value
 * @return true
 * @return false
 */
static bool is_signed_overflow(int imm, int bits) {
  if (imm < 0) {
    // 如果是负数,则判断有效负数的位数小于 bits-1
    int mask = ~((1 << (bits - 1)) - 1);
    if (mask == (imm & mask))
      return false;
    return true;
  }
  // 如果是正数, 当bits为12位, 正数不能超过2048
  return imm > (1 << (bits - 1));
}

/**
 * @brief check imm
 *
 * @return int
 */
int check_imm(imm, bits) {
  if (is_signed_overflow(imm, bits))
    unreachable();
  return (imm);
}

static FILE *output_file;
static int depth;
// static char *argreg8[] = {"%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b"};
// static char *argreg16[] = {"%di", "%si", "%dx", "%cx", "%r8w", "%r9w"};
// static char *argreg32[] = {"%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d"};
// static char *argreg64[] = {"%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"};
static char *argreg32[] = {"R.rdi", "R.rsi", "R.rdx", "R.rcx", "R.r8", "R.r9"};
static Obj *current_fn;

static void gen_expr(Node *node);
static void gen_stmt(Node *node);

__attribute__((format(printf, 1, 2))) static void println(char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vfprintf(output_file, fmt, ap);
  va_end(ap);
  fprintf(output_file, "\n");
}

static int count(void) {
  static int i = 1;
  return i++;
}

/**
 * @brief 默认push是rax
 *
 */
static void push() {
  println("  I.ADDI(R.rsp,R.rsp,-4)");
  println("  I.SW(R.rsp,R.rax,0) # push rax");
  depth++;
}

/**
 * @brief push 一个寄存器
 *
 * @param rs 源寄存器.
 */
static void push_reg(char *rs) {
  println("  I.ADDI(R.rsp,R.rsp,-4)");
  println("  I.SW(R.rsp,%s,0) # push", rs);
}

static void pop(char *rd) {
  println("  I.LW(%s,R.rsp,0)", rd);
  println("  I.ADDI(R.rsp,R.rsp,4) # pop");
  depth--;
}

/**
 * @brief 加载立即数到指定寄存器
 *
 * @param rd
 * @param imm
 */
static void load_imm(char *rd, int imm) {
  if (is_signed_overflow(imm, 12)) {
    uint32_t high_bit = ((imm >> 12) + ((imm >> 11) & 0x1)) & 0xfffff;
    uint32_t low_bit = imm & 0x00000fff;
    println("  I.LUI(%s, %d)", rd, high_bit);
    println("  I.ADDI(%s, %s, %d) # overflow load %d", rd, rd, low_bit, imm);
  } else {
    println("  I.ADDI(%s,R.r0, %d) # load %d", rd, imm, imm);
  }
}

/**
 * @brief 加载uint imm到模型中.
 *
 * @param rd
 * @param imm
 */
static void load_uimm(char *rd, uint32_t imm) {
  if (imm > ((1 << 12) - 1)) {
    uint32_t high_bit = ((imm >> 12) + ((imm >> 11) & 0x1)) & 0xfffff;
    uint32_t low_bit = imm & 0x00000fff;
    println("  I.LUI(%s, %d)", rd, high_bit);
    println("  I.ADDI(%s, %s, %d) # overflow load %d", rd, rd, low_bit, imm);
  } else {
    println("  I.ADDI(%s,R.r0, %d) # load %d", rd, imm, imm);
  }
}

/**
 * @brief lea 是从源寄存器中取数和偏移, 存到新寄存器中
 *      NOTE 源寄存器中的内容请保证为有效地址.
 * @param rd
 * @param rs
 * @param offset
 */
static void lea(char *rd, char *rs, char *name, int offset) {
  if (is_signed_overflow(offset, 12)) {
    unreachable();
  }
  println("  I.ADDI(%s,%s,%d) # lea @%s", rd, rs, offset, name);
}

/**
 * @brief 加载symbol的text地址.到目标寄存器,
 * @param rd
 * @param offset
 */
static void lea_symobl(char *rd, char *symbol_name) {
  // AUIPC(GP_REGISTER rd, Expr imm)
  // NOTE auipc加载的是高20位. 这里的地址得在汇编器里面重新算一下
  println("  I.AUIPC(%s, %d)", rd, 0);
  println("  I.ADDI(%s,%s,8) # pc offset", rd, rd);
  println("  I.ADDI(%s,%s,@%s) # lea", rd, rd,
          symbol_name); // 这里用汇编器取填值
}

/**
 * @brief 从源寄存器内容加偏移的结果地址 加载数据到 目标寄存器
 *
 * @param rd
 * @param rs
 * @param offset
 */
static void mov(char *rd, char *rs, int offset) {
  println("  I.LW(%s,%s,%d)", rd, rs, check_imm(offset, 12));
}

static void pushf(void) {
  // println("  sub $8, %%rsp");
  // println("  movsd %%xmm0, (%%rsp)");
  // depth++;
  unreachable();
}

static void popf(int reg) {
  // println("  movsd (%%rsp), %%xmm%d", reg);
  // println("  add $8, %%rsp");
  // depth--;
  unreachable();
}

// Round up `n` to the nearest multiple of `align`. For instance,
// align_to(5, 8) returns 8 and align_to(11, 8) returns 16.
int align_to(int n, int align) { return (n + align - 1) / align * align; }

/**
 * @brief 根据size获取dx
 *
 * @param sz
 * @return char*
 */
static char *reg_dx(int sz) {
  switch (sz) {
  // case 1:
  //   return "%dl";
  // case 2:
  //   return "%dx";
  // case 4:
  //   return "%edx";
  case 8:
    return "R.rdx";
  }
  unreachable();
}

/**
 * @brief 根据size获取对应的目标寄存器
 *
 * @param sz
 * @return char*
 */
static char *reg_ax(int sz) {
  switch (sz) {
  // case 1:
  //   return "%al";
  // case 2:
  //   return "%ax";
  // case 4:
  //   return "%eax";
  case 8:
    return "R.rax";
  }
  unreachable();
}

// Compute the absolute address of a given node.
// It's an error if a given node does not reside in memory.
static void gen_addr(Node *node) {
  switch (node->kind) {
  case ND_VAR:
    // Variable-length array, which is always local.
    if (node->var->ty->kind == TY_VLA) { // 数组都一定是局部变量的.
      // println("  mov %d(%%rbp), %%rax", node->var->offset);
      mov("R.rax", "R.rbp", node->var->offset);
      return;
    }

    // Local variable 因为他会被push到栈上,因此可以通过偏移取得.
    if (node->var->is_local) {
      // println("  lea %d(%%rbp), %%rax", node->var->offset);
      lea("R.rax", "R.rbp", node->var->name, node->var->offset);
      return;
    }

    if (opt_fpic) {
      unreachable();
      // Thread-local variable
      // if (node->var->is_tls) {
      //   println("  data16 lea %s@tlsgd(%%rip), %%rdi", node->var->name);
      //   println("  .value 0x6666");
      //   println("  rex64");
      //   println("  call __tls_get_addr@PLT");
      //   return;
      // }

      // // Function or global variable
      // println("  mov %s@GOTPCREL(%%rip), %%rax", node->var->name);
      // return;
    }

    // Thread-local variable
    if (node->var->is_tls) {
      unreachable();
      // println("  mov %%fs:0, %%rax");
      // println("  add $%s@tpoff, %%rax", node->var->name);
      // return;
    }

    // Here, we generate an absolute address of a function or a global
    // variable. Even though they exist at a certain address at runtime,
    // their addresses are not known at link-time for the following
    // two reasons.
    // 这里使用相对地址去索引function 和 global var 有以下两个原因
    //  - Address randomization: Executables are loaded to memory as a
    //    whole but it is not known what address they are loaded to.
    //    Therefore, at link-time, relative address in the same
    //    exectuable (i.e. the distance between two functions in the
    //    same executable) is known, but the absolute address is not
    //    known.
    //  - 加载到内存后,相对地址不变,绝对地址会改变
    //  - Dynamic linking: Dynamic shared objects (DSOs) or .so files
    //    are loaded to memory alongside an executable at runtime and
    //    linked by the runtime loader in memory. We know nothing
    //    about addresses of global stuff that may be defined by DSOs
    //    until the runtime relocation is complete.
    //  - 动态链接后不知道dso如何计算地址的.
    // In order to deal with the former case, we use RIP-relative
    // addressing, denoted by `(%rip)`. For the latter, we obtain an
    // address of a stuff that may be in a shared object file from the
    // Global Offset Table using `@GOTPCREL(%rip)` notation.

    // Function
    if (node->ty->kind == TY_FUNC) {
      if (node->var->is_definition) {
        // println("  lea %s(%%rip), %%rax", node->var->name);
        lea_symobl("R.rax", node->var->name);
      } else {
        // println("  mov %s@GOTPCREL(%%rip), %%rax", node->var->name);
        unreachable(); // 暂时不支持调用动态链接
      }
      return;
    }

    // Global variable
    // println("  lea %s(%%rip), %%rax", node->var->name);
    lea_symobl("R.rax", node->var->name);
    return;
  case ND_DEREF:
    gen_expr(node->lhs);
    return;
  case ND_COMMA:
    gen_expr(node->lhs);
    gen_addr(node->rhs);
    return;
  case ND_MEMBER:
    gen_addr(node->lhs);
    // println("  add $%d, %%rax", node->member->offset);

    println("  I.ADDI(R.rax,R.rax,%d) # rax= &%s.%.*s",
            check_imm(node->member->offset, 12), node->lhs->var->name,
            (int)(node->member->name->next->loc - node->member->name->loc),
            node->member->name->loc);
    return;
  case ND_FUNCALL:
    if (node->ret_buffer) {
      gen_expr(node);
      return;
    }
    break;
  case ND_ASSIGN:
  case ND_COND:
    if (node->ty->kind == TY_STRUCT || node->ty->kind == TY_UNION) {
      gen_expr(node);
      return;
    }
    break;
  case ND_VLA_PTR:
    // println("  lea %d(%%rbp), %%rax", node->var->offset);
    lea("R.rax", "R.rbp", node->var->name, node->var->offset);
    return;
  }

  error_tok(node->tok, "not an lvalue");
}

// Load a value from where %rax is pointing to.
static void load(Type *ty) {
  switch (ty->kind) {
  case TY_ARRAY:
  case TY_STRUCT:
  case TY_UNION:
  case TY_FUNC:
  case TY_VLA:
    // If it is an array, do not attempt to load a value to the
    // register because in general we can't load an entire array to a
    // register. As a result, the result of an evaluation of an array
    // becomes not the array itself but the address of the array.
    // This is where "array is automatically converted to a pointer to
    // the first element of the array in C" occurs.
    return;
  case TY_FLOAT:
    // println("  movss (%%rax), %%xmm0");
    unreachable();
    return;
  case TY_DOUBLE:
    // println("  movsd (%%rax), %%xmm0");
    unreachable();
    return;
  case TY_LDOUBLE:
    // println("  fldt (%%rax)");
    unreachable();
    return;
  }

  // char *insn = ty->is_unsigned ? "movz" : "movs";

  // When we load a char or a short value to a register, we always
  // extend them to the size of int, so we can assume the lower half of
  // a register always contains a valid value. The upper half of a
  // register for char, short and int may contain garbage. When we load
  // a long value to a register, it simply occupies the entire register.
  if (ty->size == 1)
    // println("  %sbl (%%rax), %%eax", insn);
    unreachable();
  else if (ty->size == 2)
    // println("  %swl (%%rax), %%eax", insn);
    unreachable();
  else if (ty->size == 4)
    // println("  movsxd (%%rax), %%rax");
    println("  I.LW(%s,%s,0)", "R.rax", "R.rax");
  else
    // println("  mov (%%rax), %%rax");
    println("  I.LW(%s,%s,0)", "R.rax", "R.rax");
}

// Store %rax to an address that the stack top is pointing to.
// 函数返回之后,他的结果存在rax中,此时栈顶指向的是调用者的局部变量,因此将rax
// store到栈顶即可.
static void store(Type *ty) {
  // pop("%rdi");
  pop("R.rdi");

  switch (ty->kind) {
  case TY_STRUCT:
  case TY_UNION: {
    int offset = 0;
    int remain_size = ty->size;
    int width = 4;
    while (remain_size) {
      while (remain_size / width < 1) {
        width /= 2;
      }
      char *LS, *SS;
      switch (width) {
      case 1:
        LS = "BU";
        SS = "B";
        break;
      case 2:
        LS = "HU";
        SS = "H";
        break;
      case 4:
        LS = "W";
        SS = "W";
        break;
      default:
        unreachable("The Store Width Error!");
        break;
      }
      println("  I.L%s(R.r8,R.rax,%d)", LS, offset);
      println("  I.S%s(R.rdi,R.r8,%d) # copy rax[%d:%d] to rdi", SS, offset,
              offset, offset + width);
      offset += width;
      remain_size -= width;
    }
  }
    return;
  case TY_FLOAT:
    // println("  movss %%xmm0, (%%rdi)");
    unreachable();
    return;
  case TY_DOUBLE:
    // println("  movsd %%xmm0, (%%rdi)");
    unreachable();
    return;
  case TY_LDOUBLE:
    // println("  fstpt (%%rdi)");
    unreachable();
    return;
  }

  if (ty->size == 1)
    // println("  mov %%al, (%%rdi)");
    println("  I.SB(R.rdi,R.rax,0)");
  else if (ty->size == 2)
    // println("  mov %%ax, (%%rdi)");
    println("  I.SH(R.rdi,R.rax,0)");
  else if (ty->size == 4)
    // println("  mov %%eax, (%%rdi)");
    println("  I.SW(R.rdi,R.rax,0)");
  else
    // println("  mov %%rax, (%%rdi)");
    unreachable("最大32位");
}

/**
 * @brief 检查rax是否为0, 如果是,那么req = 1, 否则req = 0;
 *
 * @param ty
 */
static void cmp_zero(Type *ty) {
  switch (ty->kind) {
  case TY_FLOAT:
    // println("  xorps %%xmm1, %%xmm1");
    // println("  ucomiss %%xmm1, %%xmm0");
    unreachable();
    return;
  case TY_DOUBLE:
    // println("  xorpd %%xmm1, %%xmm1");
    // println("  ucomisd %%xmm1, %%xmm0");
    unreachable();
    return;
  case TY_LDOUBLE:
    // println("  fldz");
    // println("  fucomip");
    // println("  fstp %%st(0)");
    unreachable();
    return;
  }

  if (is_integer(ty) && ty->size <= 4) {
    println("  I.BEQ(R.r0,R.rax,12) # rax == 0?");
    println("  I.ADDI(R.req,R.r0,0) # rax != 0, req = 0");
    println("  I.JAL(R.r0,8)");
    println("  I.ADDI(R.req,R.r0,1) # rax == 0, req = 1");
  } else
    unreachable();
}

enum { I8, I16, I32, I64, U8, U16, U32, U64, F32, F64, F80 };

static int getTypeId(Type *ty) {
  switch (ty->kind) {
  case TY_CHAR:
    return ty->is_unsigned ? U8 : I8;
  case TY_SHORT:
    return ty->is_unsigned ? U16 : I16;
  case TY_INT:
    return ty->is_unsigned ? U32 : I32;
  case TY_LONG:
    return ty->is_unsigned ? U64 : I64;
  case TY_FLOAT:
    return F32;
  case TY_DOUBLE:
    return F64;
  case TY_LDOUBLE:
    return F80;
  }
  return U64;
}

// The table for type casts
static char i32i8[] = "movsbl %al, %eax";
static char i32u8[] = "movzbl %al, %eax";
static char i32i16[] = "movswl %ax, %eax";
static char i32u16[] = "movzwl %ax, %eax";
static char i32f32[] = "cvtsi2ssl %eax, %xmm0";
static char i32i64[] = "movsxd %eax, %rax";
static char i32f64[] = "cvtsi2sdl %eax, %xmm0";
static char i32f80[] = "mov %eax, -4(%rsp); fildl -4(%rsp)";

static char u32f32[] = "mov %eax, %eax; cvtsi2ssq %rax, %xmm0";
static char u32i64[] = "mov %eax, %eax";
static char u32f64[] = "mov %eax, %eax; cvtsi2sdq %rax, %xmm0";
static char u32f80[] = "mov %eax, %eax; mov %rax, -8(%rsp); fildll -8(%rsp)";

static char i64f32[] = "cvtsi2ssq %rax, %xmm0";
static char i64f64[] = "cvtsi2sdq %rax, %xmm0";
static char i64f80[] = "movq %rax, -8(%rsp); fildll -8(%rsp)";

static char u64f32[] = "cvtsi2ssq %rax, %xmm0";
static char u64f64[] =
    "test %rax,%rax; js 1f; pxor %xmm0,%xmm0; cvtsi2sd %rax,%xmm0; jmp 2f; "
    "1: mov %rax,%rdi; and $1,%eax; pxor %xmm0,%xmm0; shr %rdi; "
    "or %rax,%rdi; cvtsi2sd %rdi,%xmm0; addsd %xmm0,%xmm0; 2:";
static char u64f80[] =
    "mov %rax, -8(%rsp); fildq -8(%rsp); test %rax, %rax; jns 1f;"
    "mov $1602224128, %eax; mov %eax, -4(%rsp); fadds -4(%rsp); 1:";

static char f32i8[] = "cvttss2sil %xmm0, %eax; movsbl %al, %eax";
static char f32u8[] = "cvttss2sil %xmm0, %eax; movzbl %al, %eax";
static char f32i16[] = "cvttss2sil %xmm0, %eax; movswl %ax, %eax";
static char f32u16[] = "cvttss2sil %xmm0, %eax; movzwl %ax, %eax";
static char f32i32[] = "cvttss2sil %xmm0, %eax";
static char f32u32[] = "cvttss2siq %xmm0, %rax";
static char f32i64[] = "cvttss2siq %xmm0, %rax";
static char f32u64[] = "cvttss2siq %xmm0, %rax";
static char f32f64[] = "cvtss2sd %xmm0, %xmm0";
static char f32f80[] = "movss %xmm0, -4(%rsp); flds -4(%rsp)";

static char f64i8[] = "cvttsd2sil %xmm0, %eax; movsbl %al, %eax";
static char f64u8[] = "cvttsd2sil %xmm0, %eax; movzbl %al, %eax";
static char f64i16[] = "cvttsd2sil %xmm0, %eax; movswl %ax, %eax";
static char f64u16[] = "cvttsd2sil %xmm0, %eax; movzwl %ax, %eax";
static char f64i32[] = "cvttsd2sil %xmm0, %eax";
static char f64u32[] = "cvttsd2siq %xmm0, %rax";
static char f64i64[] = "cvttsd2siq %xmm0, %rax";
static char f64u64[] = "cvttsd2siq %xmm0, %rax";
static char f64f32[] = "cvtsd2ss %xmm0, %xmm0";
static char f64f80[] = "movsd %xmm0, -8(%rsp); fldl -8(%rsp)";

#define FROM_F80_1                                                             \
  "fnstcw -10(%rsp); movzwl -10(%rsp), %eax; or $12, %ah; "                    \
  "mov %ax, -12(%rsp); fldcw -12(%rsp); "

#define FROM_F80_2 " -24(%rsp); fldcw -10(%rsp); "

static char f80i8[] = FROM_F80_1 "fistps" FROM_F80_2 "movsbl -24(%rsp), %eax";
static char f80u8[] = FROM_F80_1 "fistps" FROM_F80_2 "movzbl -24(%rsp), %eax";
static char f80i16[] = FROM_F80_1 "fistps" FROM_F80_2 "movzbl -24(%rsp), %eax";
static char f80u16[] = FROM_F80_1 "fistpl" FROM_F80_2 "movswl -24(%rsp), %eax";
static char f80i32[] = FROM_F80_1 "fistpl" FROM_F80_2 "mov -24(%rsp), %eax";
static char f80u32[] = FROM_F80_1 "fistpl" FROM_F80_2 "mov -24(%rsp), %eax";
static char f80i64[] = FROM_F80_1 "fistpq" FROM_F80_2 "mov -24(%rsp), %rax";
static char f80u64[] = FROM_F80_1 "fistpq" FROM_F80_2 "mov -24(%rsp), %rax";
static char f80f32[] = "fstps -8(%rsp); movss -8(%rsp), %xmm0";
static char f80f64[] = "fstpl -8(%rsp); movsd -8(%rsp), %xmm0";

// clang-format off
static char *cast_table[][11] = {
  // i8   i16     i32     i64     u8     u16     u32     u64     f32     f64     f80
  {NULL,  NULL,   NULL,   i32i64, i32u8, i32u16, NULL,   i32i64, i32f32, i32f64, i32f80}, // i8
  {i32i8, NULL,   NULL,   i32i64, i32u8, i32u16, NULL,   i32i64, i32f32, i32f64, i32f80}, // i16
  {i32i8, i32i16, NULL,   i32i64, i32u8, i32u16, NULL,   i32i64, i32f32, i32f64, i32f80}, // i32
  {i32i8, i32i16, NULL,   NULL,   i32u8, i32u16, NULL,   NULL,   i64f32, i64f64, i64f80}, // i64

  {i32i8, NULL,   NULL,   i32i64, NULL,  NULL,   NULL,   i32i64, i32f32, i32f64, i32f80}, // u8
  {i32i8, i32i16, NULL,   i32i64, i32u8, NULL,   NULL,   i32i64, i32f32, i32f64, i32f80}, // u16
  {i32i8, i32i16, NULL,   u32i64, i32u8, i32u16, NULL,   u32i64, u32f32, u32f64, u32f80}, // u32
  {i32i8, i32i16, NULL,   NULL,   i32u8, i32u16, NULL,   NULL,   u64f32, u64f64, u64f80}, // u64

  {f32i8, f32i16, f32i32, f32i64, f32u8, f32u16, f32u32, f32u64, NULL,   f32f64, f32f80}, // f32
  {f64i8, f64i16, f64i32, f64i64, f64u8, f64u16, f64u32, f64u64, f64f32, NULL,   f64f80}, // f64
  {f80i8, f80i16, f80i32, f80i64, f80u8, f80u16, f80u32, f80u64, f80f32, f80f64, NULL},   // f80
};
// clang-format on

static void cast(Type *from, Type *to) {
  if (to->kind == TY_VOID)
    return;

  if (to->kind == TY_BOOL) {
    cmp_zero(from);
    println("  setne %%al");
    println("  movzx %%al, %%eax");
    return;
  }

  int t1 = getTypeId(from);
  int t2 = getTypeId(to);
  if (cast_table[t1][t2])
    println("  %s", cast_table[t1][t2]);
}

/**
 * @brief
 *   Structs or unions equal or smaller than 16 bytes are passed using up to two
 * registers.
 *   If the first 8 bytes contains only floating-point type members, they are
 * passed in an XMM register.
 *   Otherwise, they are passed in a general-purpose register.
 * If a struct/union is larger than 8 bytes, the same rule is applied
 * to the the next 8 byte chunk.
 *   This function returns true if `ty` has only
 * floating-point members in its byte range [lo, hi).
 * @param ty
 * @param lo
 * @param hi
 * @param offset
 * @return true
 * @return false
 */
static bool has_flonum(Type *ty, int lo, int hi, int offset) {
  if (ty->kind == TY_STRUCT || ty->kind == TY_UNION) {
    for (Member *mem = ty->members; mem; mem = mem->next)
      if (!has_flonum(mem->ty, lo, hi, offset + mem->offset))
        return false;
    return true;
  }

  if (ty->kind == TY_ARRAY) {
    for (int i = 0; i < ty->array_len; i++)
      if (!has_flonum(ty->base, lo, hi, offset + ty->base->size * i))
        return false;
    return true;
  }

  return offset < lo || hi <= offset || ty->kind == TY_FLOAT ||
         ty->kind == TY_DOUBLE;
}

static bool has_flonum1(Type *ty) { return has_flonum(ty, 0, GP_WIDTH, 0); }

static bool has_flonum2(Type *ty) {
  return has_flonum(ty, GP_WIDTH, GP_WIDTH * 2, 0);
}

static void push_struct(Type *ty, char *name) {
  int sz = align_to(ty->size, 4);
  // println("  sub $%d, %%rsp", sz);
  println("  I.ADDI(R.rsp,R.rsp, %d) # push struct %s", -sz, name); // 下移rsp
  depth += sz / GP_WIDTH;

  int offset = 0;
  int remain_size = ty->size;
  int width = 4;
  while (remain_size) {
    while (remain_size / width < 1) {
      width /= 2;
    }
    char *LS, *SS;
    switch (width) {
    case 1:
      LS = "BU";
      SS = "B";
      break;
    case 2:
      LS = "HU";
      SS = "H";
      break;
    case 4:
      LS = "W";
      SS = "W";
      break;
    default:
      unreachable("The Store Width Error!");
      break;
    }
    println("  I.L%s(R.r10,R.rax,%d)", LS, offset);
    println("  I.S%s(R.rsp,R.r10,%d) # push rax[%d:%d] to rsp", SS, offset,
            offset, offset + width);
    offset += width;
    remain_size -= width;
  }
}

/**
 * @brief 根据之前处理的结果继续push参数
 *
 * @param args 参数节点.
 * @param first_pass 是否是第一次
 */
static void push_args2(Node *args, bool first_pass) {
  if (!args)
    return;
  // 递归的push,也就是最终栈上的顺序为 args n,args n-1, args 6.
  push_args2(args->next, first_pass);

  //如果不是通过栈传值就pass.
  if ((first_pass && !args->pass_by_stack) ||
      (!first_pass && args->pass_by_stack))
    return;

  gen_expr(args);

  switch (args->ty->kind) {
  case TY_STRUCT:
  case TY_UNION:
    push_struct(args->ty, args->var->name);
    break;
  case TY_FLOAT:
  case TY_DOUBLE:
    pushf();
    break;
  case TY_LDOUBLE:
    // println("  sub $16, %%rsp");
    // println("  fstpt (%%rsp)");
    // depth += 2;
    unreachable();
    break;
  case TY_LONG:
    unreachable();
    break;
  default:
    push();
  }
}

/**
 * @brief  Load function call arguments. Arguments are already evaluated and
 * stored to the stack as local variables. What we need to do in this
 * function is to load them to registers or push them to the stack as
 * specified by the x86-64 psABI. Here is what the spec says:
 *
 * - Up to 6 arguments of integral type are passed using RDI, RSI,
 *   RDX, RCX, R8 and R9.
 *
 * - Up to 8 arguments of floating-point type are passed using XMM0 to
 *   XMM7.
 *
 * - If all registers of an appropriate type are already used, push an
 *   argument to the stack in the right-to-left order.
 *
 * - Each argument passed on the stack takes 8 bytes, and the end of
 *   the argument area must be aligned to a 16 byte boundary.
 *
 * - If a function is variadic, set the number of floating-point type
 *   arguments to RAX.
 * NOTE 这里我限制浮点数/变长参数
 * @param node
 * @return int
 */
static int push_args(Node *node) {
  int stack = 0, gp = 0, fp = 0;

  // 如果返回值时一个大的结构体,那么caller会存buffer的指针作为函数的第一个参数.
  if (node->ret_buffer && node->ty->size > (GP_WIDTH * 2))
    gp++;

  // Load as many arguments to the registers as possible.
  for (Node *arg = node->args; arg; arg = arg->next) {
    Type *ty = arg->ty;

    switch (ty->kind) {
    case TY_STRUCT:
    case TY_UNION:
      if (ty->size > GP_WIDTH * 2) { // 大于两个寄存器时用栈传参
        arg->pass_by_stack = true;
        stack += align_to(ty->size, GP_WIDTH) / GP_WIDTH;
      } else {
        bool fp1 = has_flonum1(ty);
        bool fp2 = has_flonum2(ty);

        if (fp + fp1 + fp2 < FP_MAX && gp + !fp1 + !fp2 < GP_MAX) {
          fp = fp + fp1 + fp2;
          gp = gp + !fp1 + !fp2;
        } else {
          arg->pass_by_stack = true;
          stack += align_to(ty->size, GP_WIDTH) / GP_WIDTH;
        }
      }
      break;
    case TY_FLOAT:
    case TY_DOUBLE:
      // if (fp++ >= FP_MAX) {
      //   arg->pass_by_stack = true;
      //   stack++;
      // }
      unreachable();
      break;
    case TY_LDOUBLE:
      // arg->pass_by_stack = true;
      // stack += 2;
      unreachable();
      break;
    case TY_LONG:
      unreachable();
      break;
    default:
      if (gp++ >= GP_MAX) {
        arg->pass_by_stack = true;
        stack++;
      }
    }
  }
  // 如果 临时变量 + stack参数 没有对齐到2, 那就偏移1.
  if ((depth + stack) % 2 == 1) {
    // println("  sub $8, %%rsp");
    println("  I.ADDI(R.rsp,R.rsp,%d)", -GP_WIDTH);
    depth++;
    stack++;
  }

  push_args2(node->args, true);
  push_args2(node->args, false);

  // If the return type is a large struct/union, the caller passes
  // a pointer to a buffer as if it were the first argument.
  if (node->ret_buffer && node->ty->size > 2 * GP_WIDTH) {
    // println("  lea %d(%%rbp), %%rax", node->ret_buffer->offset);
    lea("R.rax", "R.rbp", node->ret_buffer->name, node->ret_buffer->offset);
    push();
  }

  return stack;
}

static void copy_ret_buffer(Obj *var) {
  Type *ty = var->ty;
  int gp = 0, fp = 0;

  if (has_flonum1(ty)) {
    assert(ty->size == 4 || 8 <= ty->size);
    if (ty->size == 4)
      println("  movss %%xmm0, %d(%%rbp)", var->offset);
    else
      println("  movsd %%xmm0, %d(%%rbp)", var->offset);
    fp++;
  } else {
    for (int i = 0; i < MIN(8, ty->size); i++) {
      println("  mov %%al, %d(%%rbp)", var->offset + i);
      println("  shr $8, %%rax");
    }
    gp++;
  }

  if (ty->size > 8) {
    if (has_flonum2(ty)) {
      assert(ty->size == 12 || ty->size == 16);
      if (ty->size == 12)
        println("  movss %%xmm%d, %d(%%rbp)", fp, var->offset + 8);
      else
        println("  movsd %%xmm%d, %d(%%rbp)", fp, var->offset + 8);
    } else {
      char *reg1 = (gp == 0) ? "%al" : "%dl";
      char *reg2 = (gp == 0) ? "%rax" : "%rdx";
      for (int i = 8; i < MIN(16, ty->size); i++) {
        println("  mov %s, %d(%%rbp)", reg1, var->offset + i);
        println("  shr $8, %s", reg2);
      }
    }
  }
}

/**
 * @brief 通过寄存器传结构体. 先关掉.
 *
 */
// static void copy_struct_reg(void) {
//   Type *ty = current_fn->ty->return_ty;
//   int gp = 0, fp = 0;

//   println("  mov %%rax, %%rdi");

//   if (has_flonum(ty, 0, 8, 0)) {
//     assert(ty->size == 4 || 8 <= ty->size);
//     if (ty->size == 4)
//       println("  movss (%%rdi), %%xmm0");
//     else
//       println("  movsd (%%rdi), %%xmm0");
//     fp++;
//   } else {
//     println("  mov $0, %%rax");
//     // 他这里是每次load 8bit到rax中的al 然后左移. 这里用乘法来模拟
//     for (int i = MIN(4, ty->size) - 1; i >= 0; i--) {
//       println("  shl $8, %%rax");
//       println("  mov %d(%%rdi), %%al", i);
//     }
//     gp++;
//   }

//   if (ty->size > 8) {
//     if (has_flonum(ty, 8, 16, 0)) {
//       assert(ty->size == 12 || ty->size == 16);
//       if (ty->size == 4)
//         println("  movss 8(%%rdi), %%xmm%d", fp);
//       else
//         println("  movsd 8(%%rdi), %%xmm%d", fp);
//     } else {
//       char *reg1 = (gp == 0) ? "%al" : "%dl";
//       char *reg2 = (gp == 0) ? "%rax" : "%rdx";
//       println("  mov $0, %s", reg2);
//       for (int i = MIN(16, ty->size) - 1; i >= 8; i--) {
//         println("  shl $8, %s", reg2);
//         println("  mov %d(%%rdi), %s", i, reg1);
//       }
//     }
//   }
// }

static void copy_struct_mem(void) {
  Type *ty = current_fn->ty->return_ty;
  Obj *var = current_fn->params;

  // println("  mov %d(%%rbp), %%rdi", var->offset);
  if (is_signed_overflow(var->offset, 12)) {
    unreachable();
  }
  println("  I.LW(R.rdi, R.rbp, %d)", var->offset);

  for (int i = 0; i < ty->size; i++) {
    // println("  mov %d(%%rax), %%dl", i);
    // println("  mov %%dl, %d(%%rdi)", i);
    println("  I.LBU(R.r12,R.rax,%d)", i);
    println("  I.SB(R.rdi,R.r12,%d)", i);
  }
}

// static void builtin_alloca(void) {
//   // Align size to 16 bytes.
//   println("  add $15, %%rdi");
//   println("  and $0xfffffff0, %%edi");

//   // Shift the temporary area by %rdi.
//   println("  mov %d(%%rbp), %%rcx", current_fn->alloca_bottom->offset);
//   println("  sub %%rsp, %%rcx");
//   println("  mov %%rsp, %%rax");
//   println("  sub %%rdi, %%rsp");
//   println("  mov %%rsp, %%rdx");
//   println("1:");
//   println("  cmp $0, %%rcx");
//   println("  je 2f");
//   println("  mov (%%rax), %%r8b");
//   println("  mov %%r8b, (%%rdx)");
//   println("  inc %%rdx");
//   println("  inc %%rax");
//   println("  dec %%rcx");
//   println("  jmp 1b");
//   println("2:");

//   // Move alloca_bottom pointer.
//   println("  mov %d(%%rbp), %%rax", current_fn->alloca_bottom->offset);
//   println("  sub %%rdi, %%rax");
//   println("  mov %%rax, %d(%%rbp)", current_fn->alloca_bottom->offset);
// }

// Generate code for a given node.
static void gen_expr(Node *node) {
  // println("  .loc %d %d", node->tok->file->file_no, node->tok->line_no);
  // //关掉debug信息

  switch (node->kind) {
  case ND_NULL_EXPR:
    return;
  case ND_NUM: {
    switch (node->ty->kind) {
    case TY_FLOAT: {
      // union {
      //   float f32;
      //   uint32_t u32;
      // } u = {node->fval};
      // println("  mov $%u, %%eax  # float %Lf", u.u32, node->fval);
      // println("  movq %%rax, %%xmm0");
      // return;
      unreachable();
    }
    case TY_DOUBLE: {
      // union {
      //   double f64;
      //   uint64_t u64;
      // } u = {node->fval};
      // println("  mov $%llu, %%rax  # double %Lf", u.u64, node->fval);
      // println("  movq %%rax, %%xmm0");
      // return;
      unreachable();
    }
    case TY_LDOUBLE: {
      // union {
      //   long double f80;
      //   uint64_t u64[2];
      // } u;
      // memset(&u, 0, sizeof(u));
      // u.f80 = node->fval;
      // println("  mov $%llu, %%rax  # long double %Lf", u.u64[0], node->fval);
      // println("  mov %%rax, -16(%%rsp)");
      // println("  mov $%llu, %%rax", u.u64[1]);
      // println("  mov %%rax, -8(%%rsp)");
      // println("  fldt -16(%%rsp)");
      // return;
      unreachable();
    }
    case TY_INT: {
      if (node->ty->is_unsigned) {
        if (node->ty->is_unsigned && (node->val > UINT32_MAX))
          unreachable("字面量不能超过uint32");
        load_uimm("R.rax", node->val);
      } else {
        if ((node->val < INT32_MIN || node->val > INT32_MAX))
          unreachable("字面量不能超过int32");
        load_imm("R.rax", node->val);
      }
      break;
    }
    default:
      // bool/ char 等
      load_imm("R.rax", node->val);
      break;
    }
    return;
  }
  case ND_NEG:
    gen_expr(node->lhs);

    switch (node->ty->kind) {
    case TY_FLOAT:
      // println("  mov $1, %%rax");
      // println("  shl $31, %%rax");
      // println("  movq %%rax, %%xmm1");
      // println("  xorps %%xmm1, %%xmm0");
      // return;
      unreachable();
    case TY_DOUBLE:
      // println("  mov $1, %%rax");
      // println("  shl $63, %%rax");
      // println("  movq %%rax, %%xmm1");
      // println("  xorpd %%xmm1, %%xmm0");
      // return;
      unreachable();
    case TY_LDOUBLE:
      // println("  fchs");
      // return;
      unreachable();
    }

    // println("  neg %%rax");
    println("  I.SUB(R.rax,R.r0,R.rax)");
    return;
  case ND_VAR:
    gen_addr(node);
    load(node->ty);
    return;
  case ND_MEMBER: {
    gen_addr(node);
    load(node->ty);

    Member *mem = node->member;
    if (mem->is_bitfield) {
      // println("  shl $%d, %%rax", 64 - mem->bit_width - mem->bit_offset);
      // if (mem->ty->is_unsigned)
      //   println("  shr $%d, %%rax", 64 - mem->bit_width);
      // else
      //   println("  sar $%d, %%rax", 64 - mem->bit_width);
      unreachable();
    }
    return;
  }
  case ND_DEREF:
    gen_expr(node->lhs);
    load(node->ty);
    return;
  case ND_ADDR:
    gen_addr(node->lhs);
    return;
  case ND_ASSIGN:
    gen_addr(node->lhs);
    push();
    gen_expr(node->rhs);

    if (node->lhs->kind == ND_MEMBER && node->lhs->member->is_bitfield) {
      // println("  mov %%rax, %%r8");

      // // If the lhs is a bitfield, we need to read the current value
      // // from memory and merge it with a new value.
      // Member *mem = node->lhs->member;
      // println("  mov %%rax, %%rdi");
      // println("  and $%ld, %%rdi", (1L << mem->bit_width) - 1);
      // println("  shl $%d, %%rdi", mem->bit_offset);

      // println("  mov (%%rsp), %%rax");
      // load(mem->ty);

      // long mask = ((1L << mem->bit_width) - 1) << mem->bit_offset;
      // println("  mov $%ld, %%r9", ~mask);
      // println("  and %%r9, %%rax");
      // println("  or %%rdi, %%rax");
      // store(node->ty);
      // println("  mov %%r8, %%rax");
      // return;
      unreachable();
    }

    store(node->ty);
    return;
  case ND_STMT_EXPR:
    for (Node *n = node->body; n; n = n->next)
      gen_stmt(n);
    return;
  case ND_COMMA: // 这里是lhs 置0,  rhs 赋值
    gen_expr(node->lhs);
    gen_expr(node->rhs);
    return;
  case ND_CAST:
    gen_expr(node->lhs);
    cast(node->lhs->ty, node->ty);
    return;
  case ND_MEMZERO: {
    // `rep stosb` is equivalent to `memset(%rdi, %al, %rcx)`.
    // println("  mov $%d, %%rcx", node->var->ty->size); // rcx 保存size信息
    // println("  lea %d(%%rbp), %%rdi", node->var->offset); //
    // println("  mov $0, %%al");
    // println("  rep stosb");
    uint32_t size = node->var->ty->size;
    uint32_t word_size = 4;
    int offset = node->var->offset;
    while (size) {
      if (size >= word_size) {
        char *inst = NULL;
        switch (word_size) {
        case 4:
          inst = "SW";
          break;
        case 2:
          inst = "SH";
          break;
        case 1:
          inst = "SB";
          break;
        default:
          unreachable();
          break;
        }
        if (is_signed_overflow(offset, 12)) {
          unreachable();
        }
        println("  I.%s(R.rbp,R.r0,%d) # %s[%d:%d]=0", inst, offset,
                node->var->name, offset - node->var->offset,
                offset - node->var->offset + word_size);
        size -= word_size;
        offset += word_size;
      } else {
        word_size /= 2;
      }
    }
    return;
  }
  case ND_COND: {
    int c = count();
    gen_expr(node->cond);
    cmp_zero(node->cond->ty);
    println("  je .L.else.%d", c);
    gen_expr(node->then);
    println("  jmp .L.end.%d", c);
    println(".L.else.%d:", c);
    gen_expr(node->els);
    println(".L.end.%d:", c);
    return;
  }
  case ND_NOT:
    gen_expr(node->lhs);
    cmp_zero(node->lhs->ty);
    println("  sete %%al");
    println("  movzx %%al, %%rax");
    return;
  case ND_BITNOT:
    gen_expr(node->lhs);
    println("  not %%rax");
    return;
  case ND_LOGAND: {
    int c = count();
    gen_expr(node->lhs);
    cmp_zero(node->lhs->ty);
    println("  je .L.false.%d", c);
    gen_expr(node->rhs);
    cmp_zero(node->rhs->ty);
    println("  je .L.false.%d", c);
    println("  mov $1, %%rax");
    println("  jmp .L.end.%d", c);
    println(".L.false.%d:", c);
    println("  mov $0, %%rax");
    println(".L.end.%d:", c);
    return;
  }
  case ND_LOGOR: {
    int c = count();
    gen_expr(node->lhs);
    cmp_zero(node->lhs->ty);
    println("  jne .L.true.%d", c);
    gen_expr(node->rhs);
    cmp_zero(node->rhs->ty);
    println("  jne .L.true.%d", c);
    println("  mov $0, %%rax");
    println("  jmp .L.end.%d", c);
    println(".L.true.%d:", c);
    println("  mov $1, %%rax");
    println(".L.end.%d:", c);
    return;
  }
  case ND_FUNCALL: {
    if (node->lhs->kind == ND_VAR && !strcmp(node->lhs->var->name, "alloca")) {
      // gen_expr(node->args);
      // println("  mov %%rax, %%rdi");
      // builtin_alloca();
      // return;
      unreachable("alloca");
    }

    int stack_args = push_args(node);
    gen_expr(node->lhs);

    int gp = 0, fp = 0;

    // If the return type is a large struct/union, the caller passes
    // a pointer to a buffer as if it were the first argument.
    if (node->ret_buffer && node->ty->size > 16) {
      // pop(argreg64[gp++]);
      unreachable();
    }

    for (Node *arg = node->args; arg; arg = arg->next) {
      Type *ty = arg->ty;

      switch (ty->kind) {
      case TY_STRUCT:
      case TY_UNION:
        if (ty->size > 16)
          continue;

        bool fp1 = has_flonum1(ty);
        bool fp2 = has_flonum2(ty);

        if (fp + fp1 + fp2 < FP_MAX && gp + !fp1 + !fp2 < GP_MAX) {
          if (fp1)
            popf(fp++);
          else {
            // pop(argreg64[gp++]);
            unreachable();
          }

          if (ty->size > 8) {
            if (fp2)
              popf(fp++);
            else {
              // pop(argreg64[gp++]);
              unreachable();
            }
          }
        }
        break;
      case TY_FLOAT:
      case TY_DOUBLE:
        if (fp < FP_MAX)
          popf(fp++);
        break;
      case TY_LDOUBLE:
        break;
      default:
        if (gp < GP_MAX && ty->size <= 4) {
          // pop(argreg64[gp++]);
          pop(argreg32[gp++]);
        } else {
          unreachable();
        }
      }
    }
    // 开始函数调用
    // println("  mov %%rax, %%r10");
    // println("  mov $%d, %%rax", fp);
    // println("  call *%%r10");
    // println("  add $%d, %%rsp", stack_args * 8);
    println("  I.ADD(R.r10,R.rax,R.r0)");
    load_imm("R.rax", fp);
    println("  I.AUIPC(R.r11,0)");
    println("  I.ADDI(R.r11,R.r11,20) # R.r11 指向return address");
    push_reg("R.r11");
    println("  I.JALR(R.r0,R.r10,0) # call *r10");
    println("  I.ADDI(R.rsp,R.rsp, %d) # return后回退栈参数的偏移 rsp",
            stack_args * ADDR_TYPE_SIZE);

    depth -= stack_args;

    // It looks like the most significant 48 or 56 bits in RAX may
    // contain garbage if a function return type is short or bool/char,
    // respectively. We clear the upper bits here.
    // switch (node->ty->kind) {
    // case TY_BOOL:
    //   println("  movzx %%al, %%eax");
    //   return;
    // case TY_CHAR:
    //   if (node->ty->is_unsigned)
    //     println("  movzbl %%al, %%eax");
    //   else
    //     println("  movsbl %%al, %%eax");
    //   return;
    // case TY_SHORT:
    //   if (node->ty->is_unsigned)
    //     println("  movzwl %%ax, %%eax");
    //   else
    //     println("  movswl %%ax, %%eax");
    //   return;
    // }

    // If the return type is a small struct, a value is returned
    // using up to two registers.
    if (node->ret_buffer && node->ty->size <= GP_WIDTH * 2) {
      copy_ret_buffer(node->ret_buffer);
      // println("  lea %d(%%rbp), %%rax", node->ret_buffer->offset);
      lea("R.rbp", "R.rax", node->ret_buffer->name, node->ret_buffer->offset);
    }

    return;
  }
  case ND_LABEL_VAL:
    // println("  lea %s(%%rip), %%rax", node->unique_label);
    lea_symobl("R.rax", node->unique_label);
    return;
  case ND_CAS: {
    gen_expr(node->cas_addr);
    push();
    gen_expr(node->cas_new);
    push();
    gen_expr(node->cas_old);
    println("  mov %%rax, %%r8");
    load(node->cas_old->ty->base);
    pop("%rdx"); // new
    pop("%rdi"); // addr

    int sz = node->cas_addr->ty->base->size;
    println("  lock cmpxchg %s, (%%rdi)", reg_dx(sz));
    println("  sete %%cl");
    println("  je 1f");
    println("  mov %s, (%%r8)", reg_ax(sz));
    println("1:");
    println("  movzbl %%cl, %%eax");
    return;
  }
  case ND_EXCH: {
    gen_expr(node->lhs);
    push();
    gen_expr(node->rhs);
    pop("%rdi");

    int sz = node->lhs->ty->base->size;
    println("  xchg %s, (%%rdi)", reg_ax(sz));
    return;
  }
  }

  switch (node->lhs->ty->kind) {
  case TY_FLOAT:
  case TY_DOUBLE: {
    // gen_expr(node->rhs);
    // pushf();
    // gen_expr(node->lhs);
    // popf(1);

    // char *sz = (node->lhs->ty->kind == TY_FLOAT) ? "ss" : "sd";

    // switch (node->kind) {
    // case ND_ADD:
    //   println("  add%s %%xmm1, %%xmm0", sz);
    //   return;
    // case ND_SUB:
    //   println("  sub%s %%xmm1, %%xmm0", sz);
    //   return;
    // case ND_MUL:
    //   println("  mul%s %%xmm1, %%xmm0", sz);
    //   return;
    // case ND_DIV:
    //   println("  div%s %%xmm1, %%xmm0", sz);
    //   return;
    // case ND_EQ:
    // case ND_NE:
    // case ND_LT:
    // case ND_LE:
    //   println("  ucomi%s %%xmm0, %%xmm1", sz);

    //   if (node->kind == ND_EQ) {
    //     println("  sete %%al");
    //     println("  setnp %%dl");
    //     println("  and %%dl, %%al");
    //   } else if (node->kind == ND_NE) {
    //     println("  setne %%al");
    //     println("  setp %%dl");
    //     println("  or %%dl, %%al");
    //   } else if (node->kind == ND_LT) {
    //     println("  seta %%al");
    //   } else {
    //     println("  setae %%al");
    //   }

    //   println("  and $1, %%al");
    //   println("  movzb %%al, %%rax");
    //   return;
    // }

    // error_tok(node->tok, "invalid expression");
    unreachable("lhs double");
  }
  case TY_LDOUBLE: {
    // gen_expr(node->lhs);
    // gen_expr(node->rhs);

    // switch (node->kind) {
    // case ND_ADD:
    //   println("  faddp");
    //   return;
    // case ND_SUB:
    //   println("  fsubrp");
    //   return;
    // case ND_MUL:
    //   println("  fmulp");
    //   return;
    // case ND_DIV:
    //   println("  fdivrp");
    //   return;
    // case ND_EQ:
    // case ND_NE:
    // case ND_LT:
    // case ND_LE:
    //   println("  fcomip");
    //   println("  fstp %%st(0)");

    //   if (node->kind == ND_EQ)
    //     println("  sete %%al");
    //   else if (node->kind == ND_NE)
    //     println("  setne %%al");
    //   else if (node->kind == ND_LT)
    //     println("  seta %%al");
    //   else
    //     println("  setae %%al");

    //   println("  movzb %%al, %%rax");
    //   return;
    // }

    // error_tok(node->tok, "invalid expression");
    unreachable("lhs long double");
  }
  }
  // 这里是处理一些内置的计算.
  gen_expr(node->rhs);
  push();
  gen_expr(node->lhs);
  pop("R.rdi");

  char *ax, *di; //, *dx;

  if (node->lhs->ty->kind == TY_INT || node->lhs->ty->base) {
    ax = "R.rax";
    di = "R.rdi";
    // dx = "R.rdx";
  } else {
    // ax = "%eax";
    // di = "%edi";
    // dx = "%edx";
    unreachable();
  }

  switch (node->kind) {
  case ND_ADD:
    // println("  add %s, %s", di, ax);
    println("  I.ADD(%s,%s,%s)", ax, ax, di);
    return;
  case ND_SUB:
    // println("  sub %s, %s", di, ax); ax = ax-di;
    println("  I.SUB(%s,%s,%s)", ax, ax, di); // d = s1-s2
    return;
  case ND_MUL:
    // println("  imul %s, %s", di, ax);
    println("  I.MUL(%s,%s,%s)", ax, ax, di);
    return;
  case ND_DIV:
  case ND_MOD:
    if (node->ty->is_unsigned) {
      // REMU(GP_REGISTER rd, GP_REGISTER rs1, GP_REGISTER rs2
      // println("  mov $0, %s", dx);
      // println("  div %s", di);
      // d =  s1 / s2
      println("  I.REMU(%s,%s,%s)", ax, ax, di);
    } else {
      if (node->lhs->ty->size == 8)
        // println("  cqo");
        unreachable();
      else
        // println("  cdq");
        println("  I.REM(%s,%s,%s)", ax, ax, di);
    }
    // 这里应该不需要了. x86的应该是除法暂存到一个地方.
    // if (node->kind == ND_MOD)
    // println("  mov %%rdx, %%rax");
    // println("  I.ADD(R.rax,R.rdx,R.r0)");
    return;
  case ND_BITAND:
    // println("  and %s, %s", di, ax);
    unreachable();
    return;
  case ND_BITOR:
    // println("  or %s, %s", di, ax);
    unreachable();
    return;
  case ND_BITXOR:
    // println("  xor %s, %s", di, ax);
    unreachable();
    return;
  case ND_EQ:
    println("  I.BEQ(%s,%s,12)", ax, di);
    println("  I.ADDI(%s,R.r0,0)", ax);
    println("  I.JAL(R.r0,8)");
    println("  I.ADDI(%s,R.r0,1)", ax);
    return;
  case ND_NE:
    println("  I.BNE(%s,%s,16)", ax, di);
    println("  I.ADDI(%s,R.r0,0)", ax);
    println("  I.JAL(R.r0,8)");
    println("  I.ADDI(%s,R.r0,1)", ax);
    return;
  case ND_LT:
    if (node->lhs->ty->is_unsigned && node->rhs->ty->is_unsigned) {
      println("  I.BLTU(%s,%s,16)", ax, di);
    } else if (!node->lhs->ty->is_unsigned && !node->rhs->ty->is_unsigned) {
      println("  I.BLT(%s,%s,16)", ax, di);
    } else {
      unreachable("The LT Lhs Rhs Type Not Equal!");
    }
    println("  I.ADDI(%s,R.r0,0)", ax);
    println("  I.JAL(R.r0,8)");
    println("  I.ADDI(%s,R.r0,1)", ax);
    return;
  case ND_LE:
    if (node->lhs->ty->is_unsigned && node->rhs->ty->is_unsigned) {
      println("  I.BGEU(%s,%s,16)", di, ax);
    } else if (!node->lhs->ty->is_unsigned && !node->rhs->ty->is_unsigned) {
      println("  I.BGE(%s,%s,16)", di, ax);
    } else {
      unreachable("The LE Lhs Rhs Type Not Equal!");
    }
    println("  I.ADDI(%s,R.r0,0)", ax);
    println("  I.JAL(R.r0,8)");
    println("  I.ADDI(%s,R.r0,1)", ax);
    // println("  cmp %s, %s", di, ax);
    // if (node->kind == ND_EQ) {
    //   println("  sete %%al");
    // } else if (node->kind == ND_NE) {
    //   println("  setne %%al");
    // } else if (node->kind == ND_LT) {
    //   if (node->lhs->ty->is_unsigned)
    //     println("  setb %%al");
    //   else
    //     println("  setl %%al");
    // } else if (node->kind == ND_LE) {
    //   if (node->lhs->ty->is_unsigned)
    //     println("  setbe %%al");
    //   else
    //     println("  setle %%al");
    // }

    // println("  movzb %%al, %%rax");
    return;
  case ND_SHL:
    // println("  mov %%rdi, %%rcx");
    // println("  shl %%cl, %s", ax);
    unreachable();
    return;
  case ND_SHR:
    // println("  mov %%rdi, %%rcx");
    // if (node->lhs->ty->is_unsigned)
    //   println("  shr %%cl, %s", ax);
    // else
    //   println("  sar %%cl, %s", ax);
    unreachable();
    return;
  }

  error_tok(node->tok, "invalid expression");
}

static void gen_stmt(Node *node) {
  // println("  .loc %d %d", node->tok->file->file_no, node->tok->line_no);
  // 关掉debug信息

  switch (node->kind) {
  case ND_IF: {
    int c = count();
    gen_expr(node->cond);
    cmp_zero(node->cond->ty);
    // println("  je  .L.else.%d", c);
    // 当req为0时,跳转到else
    println("  I.BEQ(R.r0,R.req,.L.else.%d)", c);
    gen_stmt(node->then);
    // println("  jmp .L.end.%d", c);
    println("  I.JAL(R.r0,.L.end.%d)", c);
    println(".L.else.%d:", c);
    if (node->els)
      gen_stmt(node->els);
    println(".L.end.%d:", c);
    return;
  }
  case ND_FOR: {
    int c = count();
    if (node->init)
      gen_stmt(node->init);
    println(".L.begin.%d:", c);
    if (node->cond) {
      gen_expr(node->cond);
      cmp_zero(node->cond->ty);
      // println("  je %s", node->brk_label);
      // 当req == 1 时跳转到label
      println("  I.BLT(R.r0,R.req,%s)", node->brk_label);
    }
    gen_stmt(node->then);
    println("%s:", node->cont_label);
    if (node->inc)
      gen_expr(node->inc);
    // println("  jmp .L.begin.%d", c);
    println("  I.JAL(R.r0,.L.begin.%d)", c);
    println("%s:", node->brk_label);
    return;
  }
  case ND_DO: {
    int c = count();
    println(".L.begin.%d:", c);
    gen_stmt(node->then);
    println("%s:", node->cont_label);
    gen_expr(node->cond);
    cmp_zero(node->cond->ty);
    // println("  jne .L.begin.%d", c);
    println("  I.BEQ(R.req,R.r0,.L.begin.%d)", c);
    println("%s:", node->brk_label);
    return;
  }
  case ND_SWITCH:
    gen_expr(node->cond);

    for (Node *n = node->case_next; n; n = n->case_next) {
      char *ax = (node->cond->ty->size == 8) ? "%rax" : "%eax";
      char *di = (node->cond->ty->size == 8) ? "%rdi" : "%edi";

      if (n->begin == n->end) {
        println("  cmp $%ld, %s", n->begin, ax);
        println("  je %s", n->label);
        continue;
      }

      // [GNU] Case ranges
      println("  mov %s, %s", ax, di);
      println("  sub $%ld, %s", n->begin, di);
      println("  cmp $%ld, %s", n->end - n->begin, di);
      println("  jbe %s", n->label);
    }

    if (node->default_case)
      println("  jmp %s", node->default_case->label);

    println("  jmp %s", node->brk_label);
    gen_stmt(node->then);
    println("%s:", node->brk_label);
    return;
  case ND_CASE:
    println("%s:", node->label);
    gen_stmt(node->lhs);
    return;
  case ND_BLOCK:
    for (Node *n = node->body; n; n = n->next)
      gen_stmt(n);
    return;
  case ND_GOTO:
    // println("  jmp %s", node->unique_label);
    println("  I.JAL(R.r0, @%s)", node->unique_label);
    return;
  case ND_GOTO_EXPR:
    gen_expr(node->lhs);
    // println("  jmp *%%rax");
    println("  I.LW(R.rax,R.rax,0)");
    println("  I.JALR(R.r0,R.rax,0)  # goto ");
    return;
  case ND_LABEL:
    println("%s:", node->unique_label);
    gen_stmt(node->lhs);
    return;
  case ND_RETURN:
    if (node->lhs) {
      gen_expr(node->lhs);
      Type *ty = node->lhs->ty;

      switch (ty->kind) {
      case TY_STRUCT:
      case TY_UNION:
        // if (ty->size <= GP_WIDTH * 2)
        //   copy_struct_reg();
        // else
        copy_struct_mem();
        break;
      }
    }

    // println("  jmp .L.return.%s", current_fn->name);
    println("  I.JAL(R.r0, .L.return.%s)", current_fn->name);
    return;
  case ND_EXPR_STMT:
    gen_expr(node->lhs);
    return;
  case ND_ASM:
    println("  %s", node->asm_str);
    return;
  }

  error_tok(node->tok, "invalid statement");
}

// Assign offsets to local variables.
static void assign_lvar_offsets(Obj *prog) {
  for (Obj *fn = prog; fn; fn = fn->next) {
    if (!fn->is_function)
      continue;
    // If a function has many parameters, some parameters are
    // inevitably passed by stack rather than by register.
    // The first passed-by-stack parameter resides at RBP+16.
    // 栈传参数时,数据由调用者保存,进入子函数后,子函数的rbp 要回退 olb rbp和ret
    // address,因此top = 2 * ADDR_TYPE_SIZE;
    int top = 2 * ADDR_TYPE_SIZE;
    int bottom = 0;

    int gp = 0, fp = 0;

    // Assign offsets to pass-by-stack parameters.
    for (Obj *var = fn->params; var; var = var->next) {
      Type *ty = var->ty;

      switch (ty->kind) {
      case TY_STRUCT:
      case TY_UNION:
        if (ty->size <= 2 * GP_WIDTH) {
          bool fp1 = has_flonum(ty, 0, GP_WIDTH, 0);
          bool fp2 = has_flonum(ty, GP_WIDTH, GP_WIDTH * 2, GP_WIDTH);
          if (fp + fp1 + fp2 < FP_MAX && gp + !fp1 + !fp2 < GP_MAX) {
            fp = fp + fp1 + fp2;
            gp = gp + !fp1 + !fp2;
            continue;
          }
        }
        break;
      case TY_FLOAT:
      case TY_DOUBLE:
        if (fp++ < FP_MAX)
          continue;
        break;
      case TY_LDOUBLE:
        break;
      default:
        if (gp++ < GP_MAX)
          continue;
      }

      top = align_to(top, ADDR_TYPE_SIZE);
      var->offset = top;
      top += var->ty->size; // top 是向上增加的.
    }

    // Assign offsets to pass-by-register parameters and local variables.
    for (Obj *var = fn->locals; var; var = var->next) {
      if (var->offset)
        continue;

      // AMD64 System V ABI has a special alignment rule for an array of
      // length at least 16 bytes. We need to align such array to at least
      // 16-byte boundaries. See p.14 of
      // https://github.com/hjl-tools/x86-psABI/wiki/x86-64-psABI-draft.pdf.
      int align = (var->ty->kind == TY_ARRAY && var->ty->size >= 16)
                      ? MAX(16, var->align)
                      : var->align;
      // 这里也会有一些对齐操作.
      bottom += var->ty->size;
      bottom = align_to(bottom, align);
      var->offset = -bottom;
    }
    // NOTE 这里栈大小会16对齐.
    fn->stack_size = align_to(bottom, 16);
  }
}

static void emit_data(Obj *prog) {
  for (Obj *var = prog; var; var = var->next) {
    if (var->is_function || !var->is_definition)
      continue;

    if (var->is_static)
      println("  .local %s", var->name);
    else
      println("  .globl %s", var->name);

    int align = (var->ty->kind == TY_ARRAY && var->ty->size >= 16)
                    ? MAX(16, var->align)
                    : var->align;

    // Common symbol
    if (opt_fcommon && var->is_tentative) {
      println("  .comm %s, %d, %d", var->name, var->ty->size, align);
      continue;
    }

    // .data or .tdata
    if (var->init_data) {
      if (var->is_tls)
        println("  .section .tdata,\"awT\",@progbits");
      else
        println("  .data");

      println("  .type %s, @object", var->name);
      println("  .size %s, %d", var->name, var->ty->size);
      println("  .align %d", align);
      println("%s:", var->name);

      Relocation *rel = var->rel;
      int pos = 0;
      while (pos < var->ty->size) {
        if (rel && rel->offset == pos) {
          println("  .quad %s%+ld", *rel->label, rel->addend);
          rel = rel->next;
          pos += 8;
        } else {
          println("  .byte %d", var->init_data[pos++]);
        }
      }
      continue;
    }

    // .bss or .tbss
    if (var->is_tls)
      println("  .section .tbss,\"awT\",@nobits");
    else
      println("  .bss");

    println("  .align %d", align);
    println("%s:", var->name);
    println("  .zero %d", var->ty->size);
  }
}

/**
 * @brief 利用浮点寄存器去store
 *
 * @param r 寄存器编号
 * @param offset 变量的相对偏移
 * @param sz 数据位宽
 */
static void store_fp(int r, int offset, int sz) {
  // switch (sz) {
  // case 4:
  //   println("  movss %%xmm%d, %d(%%rbp)", r, offset);
  //   return;
  // case 8:
  //   println("  movsd %%xmm%d, %d(%%rbp)", r, offset);
  //   return;
  // }
  unreachable();
}

/**
 * @brief 利用通用寄存器去store数据.
 *
 * @param r 寄存器编号
 * @param offset 变量的相对偏移
 * @param sz 数据位宽
 */
static void store_gp(int r, int offset, int sz) {
  if (is_signed_overflow(offset, 12)) {
    unreachable();
  }
  switch (sz) {
  case 1:
    // println("  mov %s, %d(%%rbp)", argreg8[r], offset);
    println("  I.SB(R.rbp,%s,%d)", argreg32[r], offset);
    return;
  case 2:
    // println("  mov %s, %d(%%rbp)", argreg16[r], offset);
    println("  I.SH(R.rbp,%s,%d)", argreg32[r], offset);
    return;
  case 4:
    // println("  mov %s, %d(%%rbp)", argreg32[r], offset);
    println("  I.SW(R.rbp,%s,%d)", argreg32[r], offset);
    return;
  // case 8:
  // println("  mov %s, %d(%%rbp)", argreg64[r], offset);
  //   unreachable();
  //   return;
  default:
    for (int i = 0; i < sz; i++) {
      println("  I.SB(R.rbp,%s,%d)", argreg32[r], offset + i);
      // println("  mov %s, %d(%%rbp)", argreg32[r], offset + i);
      // println("  shr $8, %s", argreg64[r]);
    }
    return;
  }
}

static void emit_text(Obj *prog) {
  for (Obj *fn = prog; fn; fn = fn->next) {
    if (!fn->is_function || !fn->is_definition)
      continue;

    // No code is emitted for "static inline" functions
    // if no one is referencing them.
    if (!fn->is_live)
      continue;

    if (fn->is_static)
      println("  .local %s", fn->name);
    else
      println("  .globl %s", fn->name);

    println("  .text");
    println("  .type %s, @function", fn->name);
    if (strcmp(fn->name, "main") == 0) {
      // main函数开始之前执行一些内容
      println("gnne_start:");

      load_uimm("R.rax", 0);
      load_uimm("R.rbx", STACK_SIZE / 32);
      println("  I.MMU_CONF(R.rax, R.rbx, 0) # 配置程序运行栈为%dkb",
              STACK_SIZE / 1024);
      load_uimm("R.rbp", STACK_SIZE);
      load_uimm("R.rsp", STACK_SIZE);
    }
    println("%s:", fn->name);
    current_fn = fn;

    // Prologue
    // println("  push %%rbp");                     // 保存老的函数的帧栈
    // println("  mov %%rsp, %%rbp");               // sp指向老的fp的位置
    // println("  sub $%d, %%rsp", fn->stack_size); // 移动sp到当前程序的栈顶
    // println("  mov %%rsp, %d(%%rbp)", fn->alloca_bottom->offset);
    // ⚠️这里他特意添加了一个alloca_bottom变量放到最后,
    // 因此他的位置就是sp的位置.
    push_reg("R.rbp");
    println("  I.ADD(R.rbp,R.rsp,R.r0)");
    println("  I.ADDI(R.rsp,R.rsp,%d)", check_imm(-fn->stack_size, 12));
    println("  I.SW(R.rbp,R.rsp, %d) # 存储rsp到alloca_bottom",
            check_imm(fn->alloca_bottom->offset, 12));

    // Save arg registers if function is variadic
    if (fn->va_area) {
      // int gp = 0, fp = 0;
      // for (Obj *var = fn->params; var; var = var->next) {
      //   if (is_flonum(var->ty))
      //     fp++;
      //   else
      //     gp++;
      // }

      // int off = fn->va_area->offset;

      // // va_elem
      // println("  movl $%d, %d(%%rbp)", gp * 8, off);          // gp_offset
      // println("  movl $%d, %d(%%rbp)", fp * 8 + 48, off + 4); // fp_offset
      // println("  movq %%rbp, %d(%%rbp)", off + 8); // overflow_arg_area
      // println("  addq $16, %d(%%rbp)", off + 8);
      // println("  movq %%rbp, %d(%%rbp)", off + 16); // reg_save_area
      // println("  addq $%d, %d(%%rbp)", off + 24, off + 16);

      // // __reg_save_area__
      // println("  movq %%rdi, %d(%%rbp)", off + 24);
      // println("  movq %%rsi, %d(%%rbp)", off + 32);
      // println("  movq %%rdx, %d(%%rbp)", off + 40);
      // println("  movq %%rcx, %d(%%rbp)", off + 48);
      // println("  movq %%r8, %d(%%rbp)", off + 56);
      // println("  movq %%r9, %d(%%rbp)", off + 64);
      // println("  movsd %%xmm0, %d(%%rbp)", off + 72);
      // println("  movsd %%xmm1, %d(%%rbp)", off + 80);
      // println("  movsd %%xmm2, %d(%%rbp)", off + 88);
      // println("  movsd %%xmm3, %d(%%rbp)", off + 96);
      // println("  movsd %%xmm4, %d(%%rbp)", off + 104);
      // println("  movsd %%xmm5, %d(%%rbp)", off + 112);
      // println("  movsd %%xmm6, %d(%%rbp)", off + 120);
      // println("  movsd %%xmm7, %d(%%rbp)", off + 128);
      unreachable();
    }

    // Save passed-by-register arguments to the stack
    // 虽然有的参数到了寄存器上,但是还是需要把寄存器上的参数移动到栈上.
    int gp = 0, fp = 0; // 先清空寄存器.
    for (Obj *var = fn->params; var; var = var->next) {
      if (var->offset > 0)
        continue; // 寄存器传参的var的offset都是负的!, 因为这样便于支持变长参数.

      Type *ty = var->ty;
      // 根据当前var的长度来决定如何store
      switch (ty->kind) {
      case TY_STRUCT:
      case TY_UNION:
        assert(ty->size <= 16);
        if (has_flonum(ty, 0, 8, 0))
          store_fp(fp++, var->offset, MIN(8, ty->size));
        else
          store_gp(gp++, var->offset, MIN(8, ty->size));

        if (ty->size > 8) {
          if (has_flonum(ty, 8, 16, 0))
            store_fp(fp++, var->offset + 8, ty->size - 8);
          else
            store_gp(gp++, var->offset + 8, ty->size - 8);
        }
        break;
      case TY_FLOAT:
      case TY_DOUBLE:
        store_fp(fp++, var->offset, ty->size);
        break;
      default:
        store_gp(gp++, var->offset, ty->size);
      }
    }

    // Emit code, 在body中通过push存储额外的临时变量,都会增加栈depth
    gen_stmt(fn->body);
    assert(depth == 0); // 返回出去时必须没有多余的临时变量.

    // [https://www.sigbus.info/n1570#5.1.2.2.3p1] The C spec defines
    // a special rule for the main function. Reaching the end of the
    // main function is equivalent to returning 0, even though the
    // behavior is undefined for the other functions.
    // if (strcmp(fn->name, "main") == 0)
    //   println("  mov $0, %%rax");

    // Epilogue
    println(".L.return.%s:", fn->name);
    // println("  mov %%rbp, %%rsp");
    // println("  pop %%rbp");
    // println("  ret");
    if (strcmp(fn->name, "main") == 0) {
      // main函数跳转到end.
      println("  I.FENCE()");
      println("  I.END(R.rax)");
    } else {
      // 非main函数的return跳转到上一级函数
      println("  I.ADD(R.rsp, R.rbp, R.r0) # rsp回到当前栈顶");
      println("  I.LW(%s,R.rsp,0)", "R.rbp");
      println("  I.ADDI(R.rsp,R.rsp,4) # pop old rpb");
      println("  I.LW(%s,R.rsp,0)", "R.r11");
      println("  I.ADDI(R.rsp,R.rsp,4) # pop ret addr");
      println("  I.JALR(R.r0,R.r11,0) # return");
    }
  }
}

void codegen(Obj *prog, FILE *out) {
  output_file = out;

  File **files = get_input_files();
  println("  .stack_size %d", STACK_SIZE); // 写入一些信息
  for (int i = 0; files[i]; i++)
    println("  .file %d \"%s\"", files[i]->file_no, files[i]->name);
  assign_lvar_offsets(prog);
  emit_data(prog);
  emit_text(prog);
}
