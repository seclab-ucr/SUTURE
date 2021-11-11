#include<stdio.h>
#include<stdlib.h>

typedef struct data {
    int a,b;
} data;

typedef struct G {
    int a,b;
    data *p0,*p1;
} G;

G g0,g1,g2,g3;
G g4,g5,g6,g7;

data d0,d1,d2,d3;

int ioctl0(int c) {
    G *pg;
    switch (c) {
    case 0:
        pg = &g0;
        break;
    case 1:
        pg = &g1;
        break;
    case 2:
        pg = &g2;
        break;
    case 3:
        pg = &g3;
        break;
    }
    //Instead of a 4*4 update, an actual run will only have 4*1*1 update.
    pg->p1 = pg->p0;
    return 0;
}

int main(int argc, char **argv){
    ioctl0(argc);
    return 0;
}
