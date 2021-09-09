a;
b() {
  int c = (__typeof__(a))1;
  return c;
}

int main() { return b(); }
