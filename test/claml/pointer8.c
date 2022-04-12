int doo(int x) { return x; }

int foo(int a, int (*decode)(int)) {
  int b = decode(a);
  return b;
}

int main() {
  int r = foo(3, doo);
  sparrow_print(r);
  int q = foo(3, &doo);
  return 0;
}
