typedef struct {
  unsigned char op;
  unsigned char bits;
  unsigned short val;
} code;

void f() {
  static const code lenfix[5] = {
      {96, 7, 0}, {0, 8, 80}, {0, 8, 16}, {20, 8, 115}, {18, 7, 31}};
}
