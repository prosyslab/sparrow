int a = 1;
int c = 0;

f() {
  {
    if (a && c) {
      a++;
    } else if (a) {
      c = 1;
    }
  }
  if (a && c) {
    c = -1;
  } else if (a) {
    a = 2;
  }
}
