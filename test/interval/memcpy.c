void *memcpy(void *dst, void *src, int num);

int main(int argc, char **argv) {
  char buf[10];
  char *str = "hello";
  char *p = memcpy(buf, str, 7);
  p[10] = 0;
  sparrow_print(p);
  return 0;
}
