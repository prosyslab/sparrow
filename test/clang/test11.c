struct sigaction {
  int x;
};

extern int sigaction(const struct sigaction *__restrict __act);

int f() {
  sigaction(0);
  return 0;
}
