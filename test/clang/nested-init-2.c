struct A {
    int a;
    int arr[2];
};
struct B {
    int a;
    struct A _a;
};

struct B b = {1, {2,{3,4}} };

int main() { return 0; }
