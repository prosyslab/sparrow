void *strncpy(void *dst, void *src, int num);

int main(int argc, char **argv) {
  char buf[10];
  char *str = "hello";
  char *p = strncpy(buf, str, 7);
  p[10] = 0;
  return 0;
}
