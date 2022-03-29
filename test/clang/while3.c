int foo() { return 3; }

int main() {
  int r;
  while (r = foo() == 0)
    sparrow_print(r);
}
