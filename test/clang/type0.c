struct _IO_FILE;
typedef struct _IO_FILE FILE;
extern struct _IO_FILE *stdout;
extern __inline __attribute__((__gnu_inline__)) int
vprintf(const char *__restrict __fmt, __builtin_va_list __arg) {
  return vfprintf(stdout, __fmt, __arg);
}
