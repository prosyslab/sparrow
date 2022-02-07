struct a {
  int b
};
struct {
  struct a c[4]
} d[] = {{.c = {}}};
