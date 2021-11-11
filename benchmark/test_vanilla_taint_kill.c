#include<stdio.h>
#include<stdlib.h>

typedef struct data {
    int a,b;
} data;

data gd;
int g;

//Test the taint kill
int ioctl0(int ua) {
    gd->a = ua;
    printf("%d\n",gd->a);
    gd->a = 0;
    return 0;
}

//Test the taint overwrite
int ioctl1(int ua) {
    gd->b = ua;
    printf("%d\n",gd->b);
    gd->b = g;
    return 0;
}

int main(int argc, char **argv){
    ioctl0(argc);
    ioctl1(argc);
    return 0;
}
