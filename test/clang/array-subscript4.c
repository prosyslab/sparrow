#define LINE_BIOS(p) (0 [p] == 0)
a() {
  int **ptr;
  if (LINE_BIOS(*ptr)) {
    return 0;
  };
}