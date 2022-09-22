struct strt {
  int Length;
};

int main() {
  struct strt *acts = (struct strt *)malloc(sizeof(struct strt));
  acts->Length = 3;

  struct strt *act_implicit = &*acts;
  act_implicit->Length = 4;

  struct strt temp = *acts;
  struct strt *act_explicit = &temp;
  act_explicit->Length = 5;

  sparrow_print(acts);
  sparrow_print(act_implicit);
  sparrow_print(act_explicit);
  sparrow_print(acts->Length);
  sparrow_print(act_implicit->Length);
  sparrow_print(act_explicit->Length);

  return 0;
}
