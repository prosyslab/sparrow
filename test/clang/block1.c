int f() {
  int x = 3;
  { int x = 4; }
  return x;
}
