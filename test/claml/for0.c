int main(int argc, char *argv[]) {
  int i;
  for (i = 0; argv[i]; i++)
    ;
  sparrow_print(i);
}
