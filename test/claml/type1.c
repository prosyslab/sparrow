enum a { b };
struct c {
  enum a d;
};
typedef c;
struct c a;
int main() { return a.d; }
