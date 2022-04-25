
int foo(int a) { return a + 1; }
int foo2(int a) { return foo(a) + 2; }

int main() {
  int b = 1;
  foo2(b);
  return 0;
}