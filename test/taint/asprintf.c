int main(int argc, char **argv) {
  char buf[10];
  char *fmt;
  asprintf(&fmt, "%s", argv[1]);
  sprintf(buf, fmt);
  return 0;
}
