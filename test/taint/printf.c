char *getenv(char *);
int main() {
  char *p = getenv("PATH");
  printf(p);
  return 0;
}
