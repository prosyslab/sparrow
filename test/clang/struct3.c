struct __pthread_cond_s {
  __extension__ unsigned long long int __wseq;
  struct {
    unsigned int __low;
    unsigned int __high;
  } __wseq32;
};

int main() {
  struct __pthread_cond_s a;
  return 0;
}
