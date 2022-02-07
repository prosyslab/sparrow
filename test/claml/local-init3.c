struct Base {
  float f;
};
typedef struct _A {
  struct Base base;
  int arr[3];
} A;
typedef struct _B {
  A sa[2];
  int b;
} B;
int main() { B b = {1, 2, 3}; }
