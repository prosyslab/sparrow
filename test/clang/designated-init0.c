struct Point {
  int x, y, z;
};

int main() {
  struct Point p1 = {.y = 0, .z = 1, .x = 2};
  struct Point p2 = {.x = 20};

  return 0;
}
