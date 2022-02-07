typedef char *str;
typedef int (*FuncPtr)(int, int);

enum DayOfWeek { // Pending
  Sunday = 15,
  Monday,
  Tuesday,
  Wednesday,
  Thursday,
  Friday,
  Saturday
};

typedef struct _L {
  char *cp;
} L;

typedef struct _M {
  int n;
  L l;
  double arr[2];
} M;

typedef struct _G {
  int k;
  enum DayOfWeek day;
  char arr[2];
  M m;
  int l;
} G;

struct A {
  int a;
  int b;
};
struct B {
  int c;
  int d;
};
union U {
  float uu;
  double du;
  int iu;
};
struct C {
  FuncPtr fptr;
  str sp;
  int o;
  int e;
  double *(*ss)(char *, int *);
  G g;
  int f;
  union U u;
  struct B struct_b;
};

struct C my = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18};

int main() { int i = 0; }
