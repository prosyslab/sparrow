struct A;

struct A {
  int f;
  struct A *next;
};

struct A;

int main() {
  struct A a;
  a.f = 1;
  struct A *p = &a;
  p->f = 1;

  return 0;
}
