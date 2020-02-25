typedef struct {
  int __val[2];
} __fsid_t;

int global = 1;
int g[4] = {1, 2, 3, 4};
int gg[4][4] = {{1, 2, 3, 4}, {1, 2, 3, 4}, {1, 2, 3, 4}, {1, 2, 3, 4}};
struct A {
  int f;
  int y;
};
struct A a = {1, 2};
int f(int x) {
  int l[4] = {1, 2, 3, 4};
  __builtin_bswap32(x);
  __fsid_t a;
  return 1;
}
