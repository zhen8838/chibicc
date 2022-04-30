#define assert(x)                                                              \
  if (x) {                                                                     \
    asm("  I.ADD(R.r0,R.r0,R.r0)");                                            \
  } else {                                                                     \
    asm("   I.INTR(R.r0)");                                                    \
  }

int main() {
  int b = 1;
  assert(b);
  return 0;
}