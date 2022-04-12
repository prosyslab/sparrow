typedef void vorbis_info_mapping;

typedef struct {
  int (*unpack)(int);
} vorbis_func_mapping;

int mapping0_unpack(int x) { return x; }

vorbis_func_mapping mapping0_exportbundle = {&mapping0_unpack};
vorbis_func_mapping *p[] = {&mapping0_exportbundle};
int main() {
  int y = p[0]->unpack(0);
  sparrow_print(y);
  int z = (*p[0]->unpack)(10);
  sparrow_print(z);

  return 0;
}
