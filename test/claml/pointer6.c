int g() { return 1; };
int h() { return 2; };

int main() {
  int x = 1;
  int (*f)() = x > 0 ? g : h;
  return f();
}
