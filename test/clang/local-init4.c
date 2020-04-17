typedef struct _A {
    int a;
    int b;
} A;
typedef struct B {
    int c;
    A a[2];
    float f;
} B;
struct C {
    double d;
    B b[2];
};
int main() {
    struct C c = {1,2};
}
