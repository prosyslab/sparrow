void f() {
  int offset = 1;
  char *s = "string";
  char *p = s;
  *(offset + p) = 1;
}
