void f(int x) {
  int y;
  if (x < 1 && x > 10) {
    y = x + 1;
  } else {
  target:
    y = x + 2;
    int target = 1;
    target++;
  }
  goto target;
}
