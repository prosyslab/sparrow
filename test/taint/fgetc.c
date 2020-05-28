int fgetc(void *);

int main() {
  char buf[10];
  buf[0] = fgetc(0);
  buf[1] = fgetc(0);
  printf(buf);
  return 0;
}
