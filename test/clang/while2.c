void f() {
  int x;
    while (1) {
    while_continue:
      x = 0;
      if (x < 1) {
        goto while_break;
      }
    }
while_break:;
}
