void vsnprintf(char *dst, int len, char *format, ...);

void myprintf(char *dst, int len, char *format, ...) {
  __builtin_va_list args;
  __builtin_va_start(args, format);
  vsnprintf(dst, len, format, args);
}

int main(int argc, char** argv){
  char bug[10];
  myprintf("", 10, argv[1], "", "");
  return 0;
}
