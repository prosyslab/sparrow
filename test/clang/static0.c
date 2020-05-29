static int static_f() { return 0; }
static int static2_f() { return 0; }

int non_static_f() { return 0; }

struct S {
  int (*fp)(void);
};

struct S s = {static_f};
