void *memset(void *ptr, int value, int num);

struct S {
    int field;
    int arr[10];
};

int main(){
    char buf[10];
    char *p = memset(buf, 20, 10);
    int x = buf[*p];
    int y = *(p + 10);

    struct S s;
    memset(&s, 0, sizeof(struct S));
    s.arr[10] = 0;
    return 0;
}
