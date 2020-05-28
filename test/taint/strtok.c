char *strtok(char *, char *);

int main(int argc, char **argv) {
  char *p;
  p = strtok(argv[0], "/");
  printf(p);
  return 0;
}
