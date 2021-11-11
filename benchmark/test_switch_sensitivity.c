#include<stdio.h>
#include<stdlib.h>

typedef struct data {
    int a,b,c,d;
} data;

int ioctl1(int a, int c) {
    switch (c) {
    case 0:
        ++a;
        printf("ioctl1() case 0, %d\n",a);
        break;
    case 1:
        a *= a;
        printf("ioctl1() case 1\n");
        break;
    default:
        --a;
        printf("ioctl1() case def\n");
        break;
    }
    return a;
}

int ioctl0(int cmd, int v) {
    switch (cmd) {
    case 0:
        ++v;
        printf("case 0, %d\n",v);
        break;
    case 1:
        v *= v;
        printf("case 1\n");
        ioctl1(v,cmd);
        break;
    case 2:
        --v;
        printf("case 2, %d\n",v);
        ioctl1(v,cmd);
        break;
    default:
        printf("case def\n");
        ioctl1(v,cmd);
        break;
    }
    return 0;
}

int main(int argc, char **argv){
    ioctl0(argc,argc+1);
    return 0;
}
