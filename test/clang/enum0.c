enum state{a=1, b=2};
enum week { Mon, Tue = 10, Wed };

int main() {
  enum state a;
  enum week;
  printf("%d\n", Wed);
  return 0;
}
