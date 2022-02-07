typedef struct _A {
  int a;
  int arr[2];
  int b;
} A;

struct B {
  char a;
  A _a[2];
};

const int c = 3;
struct B b = {
    1,
    {{2, {c, c}, 5}, {6, {7, 8}, 9}},
};

int main() { return 0; }
