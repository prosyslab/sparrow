int snprintf(char * s, int n, const char * format, ...);

int main(int argc, char **argv) {
  char *p = malloc(10);
  snprintf(p, 10, "%s", *argv);
  vsnprintf(p, 10, p, "");
  printf(p);
  return 0;
}
