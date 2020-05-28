void f() {
  int x, y;

x:
  x = 1;
  goto y;
y:
  y = 1;
  goto x;
}
