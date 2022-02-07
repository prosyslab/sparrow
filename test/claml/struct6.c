struct a {
  int b;
};
struct {
  struct a c;
} d[] = {{.c = {}}};
