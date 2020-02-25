typedef struct {
  int __val[2];
} __fsid_t;

__fsid_t gg;

int f(int x) {
  __fsid_t a;
  a.__val[0] = 1;
  return 1;
}
