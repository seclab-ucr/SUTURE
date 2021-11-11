#include<stdio.h>
#include<stdlib.h>

typedef struct data0 {
    int a,b;
} data0;

typedef struct data1 {
    int a,b,c;
} data1;

typedef struct G {
    data0 *p0;
    data1 *p1;
} G;

int ioctl0(void *p, int u) {
    G *pg = (G*)p;
    data0 *pd = pg->p0;
    pd->a = u;
    return 0;
}

int ioctl1(void *p) {
    G *pg = (G*)p;
    data0 *pd = pg->p0;
    pd->a += 0xffff;
    return 0;
}

int main(int argc, char **argv){
    ioctl0(argv,9);
    ioctl1(argv);
    return 0;
}
