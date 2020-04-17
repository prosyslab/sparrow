typedef struct _A {
    int a;
    int b;
}A;
struct B {
    int a;
    A AA[4];
    int c;
};

struct B b = {1,2,3,4,5,6,7,8};

int main() {
    return 0;
}
