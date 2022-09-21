typedef struct bfd bfd;

struct bfd {
  int cacheable;
};

void f(bfd *b) { b->cacheable = 1; }
