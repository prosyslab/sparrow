int main() {
  struct atom {
    int A[42];
  };
  typedef struct atom atom_t;

  static atom_t ramb16_atoms[1] = {{{17}}};

  return 0;
}
