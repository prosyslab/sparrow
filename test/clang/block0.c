void f() {
  int x;
  int y;
  {
    x = 1;
    y = 2;
    {
      int y;
      y = 1;
    }
  }
}
