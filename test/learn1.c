typedef int int32_t;
typedef unsigned int uint32_t;

typedef struct shape {
  int32_t n;
  int32_t c;
  int32_t h;
  int32_t w;
} shape_t;

typedef struct stride {
  int32_t c;
  int32_t h;
  int32_t w;
} stride_t;

typedef struct buffer {
  shape_t shape;
  uint32_t ddr_addr;
} buffer_t;

shape_t pack_shape(int32_t n, int32_t c, int32_t h, int32_t w) {
  shape_t s = {n, c, h, w};
  return s;
}

stride_t pack_stride(int32_t c, int32_t h, int32_t w) {
  stride_t s = {c, h, w};
  return s;
}

// // I.L2_STORE_CONF(stride_t.ss1, stride_t.ss1, L2_DATATYPE.i16,
// // DDR_DATATYPE.i16);

// void l2_store_conf(stride_t rstride_d, stride_t rstride_s, int32_t
// l2_datatype,
//                    int32_t ddr_datatype) {}

// void main(buffer_t input, buffer_t output) {
//   stride_t i_s = pack_stride(2, 2, 2);
//   stride_t r_s = pack_stride(2, 2, 2);

//   l2_store_conf(i_s, r_s, 2, 2);
// }

int32_t foo(int32_t a) { return a + 1; }
int32_t foo2(int32_t a) { return foo(a) + 1; }

int main(buffer_t input, buffer_t output) {
  int b = 1;
  foo2(b);
  return 0;
}