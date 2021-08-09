enum a { b, c };
typedef f;
struct f {
  enum a d;
};
struct f a = {c};
int main() {
  f x = a.d;
  return x;
}
