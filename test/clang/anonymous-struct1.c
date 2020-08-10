struct {
  struct {
    struct {
    } a;
  } b
} c;
d() { void *p = (void *)&c.b; }
