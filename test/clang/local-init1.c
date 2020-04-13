#include <stdio.h>

typedef int (*FuncPtr) (int, int);

union U {
    float uu;
    double du;
    int iu;
};

struct A {
    int a;
    float b;
    double c;
    int arr[5];
};
struct B {
    int e;
    struct A sa;
    int f;
};
struct C {
    int g;
    union U u;
    struct B sb;
};
struct D {
    struct C P;
    int k;
    int arr[3];
    FuncPtr fptr;
};
int main() {
    struct D d = {1,2,3,4,5,6,7};
    return 1;
}
