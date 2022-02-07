int f(char *c1, const char *c2, int s) { return 2; }
int g(char *c1, const char *c2, int s) { return 1; }

int main(int x) {
  int (*fn)(char *, const char *, int) = (x > 10) ? f : g;
  char *word = "20";
  int slen = 10;
  return fn(word, "const char str", slen);
}
