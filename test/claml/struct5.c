struct a {
  int b;
};
struct {
  struct a c;
} d[] = {{.c = {.b = 2}}};
