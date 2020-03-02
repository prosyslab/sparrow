struct A;

int f() {
  struct A *p = 0;
  return 0;
}

struct A {
  int f;
};

int g() {
  struct A a;
  a.f = 1;
  return 0;
}
