int main() {
  struct atom {
    int A[42];
    int b;
  };
  typedef struct atom atom_t;

  static atom_t ramb16_atoms[1] = {{{17}, 5}};

  return 0;
}
