struct A {
  int a;
};
typedef struct _B {
  int arr[3];
  struct A sa;
} B;

int foo() {
  B b = {1, 2, 3, {4}};
  b.sa.a = (b.arr[0], b.arr[1]);
  return b.sa.a;
}
