int a;
int main() {
  int c = -1;
  switch (a) {
  case 0:
    __attribute__((__fallthrough__));
  case 1:
    c = 0;
    break;
  default:
    c = 1;
  }
  return c;
}
