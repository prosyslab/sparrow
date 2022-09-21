int zip(int a, int b) { return 0; }
int unzip(int a, int b) { return 0; }

int (*work)(int a, int b) = zip;

int main() {
  work = unzip;
  sparrow_print(*work);
  return 0;
}
