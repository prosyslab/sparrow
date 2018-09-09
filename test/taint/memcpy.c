void *memcpy(void *dst, void *src, int num);

int main(int argc, char **argv) {
  char buf[10];
  char *p = memcpy(buf, argv[1], 6);
  printf(buf);
  printf(p);
  return 0;
}
