#include<stdio.h>
#include<stdlib.h>

typedef struct data {
    int a,b;
} data;

typedef struct G {
    int a,b;
    data *p;
} G;

G g0,g1,g2,g3;
G g4,g5,g6,g7;

int ioctl0(int cmd, void *p);
int ioctl1(int cmd, void *p);

int ioctl0(int cmd, void *p) {
    int res;
    data *ui = (data*)p;
    switch(cmd) {
        case 0:
            g0.a = ui->a;
            break;
        case 1:
            g1.b = g0.a;
            break;
        case 2:
            g2.a = g1.b;
            break;
        case 3:
            g3.b = g2.a;
            break;
        case 4:
            g5.b = g4.a;
            break;
        case 5:
            g7.b = g6.a;
            break;
        default:
            res = g3.b * 0xffff;
            printf("res: %d\n",res);
            break;
    }
    return 0;
}

int ioctl1(int cmd, void *p) {
    int res;
    data *ui = (data*)p;
    switch(cmd) {
        case 0:
            g4.a = ui->b;
            break;
        case 1:
            g6.a = g5.b;
            break;
        default:
            res = g7.b * 0xffff;
            printf("res: %d\n",res);
            break;
    }
    return 0;
}

int main(int argc, char **argv){
    ioctl0(argc,0);
    ioctl1(argc,0);
    return 0;
}
