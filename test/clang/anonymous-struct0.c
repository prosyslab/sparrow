typedef struct {
  struct {
    unsigned overload;
  } com;
  struct {
    unsigned shreg;
  } bit;
  struct {
    unsigned send;
  } boo;
} cvsd_t;

typedef cvsd_t prev_t;

int main() {
  prev_t *a;
  a = 0;
  // a->com.overload = 1;
  return 0;
}
