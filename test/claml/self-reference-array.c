struct nd {
  int v;
  struct nd *p1[100];
};

int main() {
  struct nd tmp, tmp2;
  tmp.p1[0] = &tmp2;
  return 0;
}
