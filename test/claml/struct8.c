struct a {
  struct {
    struct a *b;
  } d;
};

struct a A;
int h() { A.d.b->d.b = 0; }
