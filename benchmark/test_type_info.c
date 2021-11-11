#include<stdio.h>
#include<stdlib.h>

typedef struct data {
    int a,b,c,d;
} data;

int foo(char *p) {
    int s;
    data *pd = (data*)p;
    s = pd->a + pd->b;
    printf("s: %d\n",s);
    return s;
}

int main(int argc, char **argv){
    foo((char*)argv);
    return 0;
}
