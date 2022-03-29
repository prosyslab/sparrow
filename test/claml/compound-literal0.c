struct a {
  int f1;
  int f2;
};
int b() {
  struct a *p = &(struct a){1, 2};
  return p->f1;
}
