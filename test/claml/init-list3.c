typedef struct {
  unsigned int a;
} my_type;
my_type myType = {&myType};
int main() { return 0; }
