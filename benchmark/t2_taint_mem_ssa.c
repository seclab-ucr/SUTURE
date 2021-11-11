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

data d0,d1,d2,d3;

int ioctl0(int cmd, void *p);
int ioctl1(int cmd, void *p);

int foo0(data *p) {
    int r;
    if (!p) {
        return 0;
    }
    r = p->a + p->b;
    if (r > 8) {
        printf("r: %d\n",r);
    }else {
        printf("r is small\n");
    }
    return r;
}

int foo1(data *p) {
    int r;
    if (!p) {
        return 0;
    }
    r = p->a + p->b;
    if (r > 8) {
        printf("r: %d\n",r);
    }else {
        printf("r is small\n");
    }
    return r;
}

int bar0(data *p) {
    int r;
    if (!p) {
        return 0;
    }
    if (p->a > 0) {
        printf("true br: %d\n",p->a);
        p->a = 0;
    }else {
        printf("false br\n");
        p->a = 1;
    }
    return r;
}

int ioctl0(int cmd, void *p) {
    int res;
    data *ui = (data*)p;
    switch(cmd) {
        case 0:
            d0.a = ui->a;
            break;
        default:
            break;
    }
    return 0;
}

int ioctl2(int cmd, void *p) {
    int res;
    data *ui = (data*)p;
    switch(cmd) {
        case 0:
            d0.a = d2.a;
            break;
        case 1:
            d2.a = ui->a;
            bar0(&d2);
            d2.a = ui->b; //only this (indtead if ui->a) can be reagrded as a user taint source for d2.a since this is a winner TF.
            if (d2.a > 0) {
                d2.a = 2;
            }
            break;
        default:
            break;
    }
    return 0;
}

int ioctl1(int cmd, void *p) {
    int res;
    data *pd;
    data *ui = (data*)p;
    switch(cmd) {
        case 0:
            pd = (ui->a ? &d0 : &d1);
            if (ui->b) {
                d0.a = d1.a; //d0.a is only tainted by d1.a now.
                foo0(&d0);
            }
            foo1(&d0); //here d0.a can be either tainted by d1.a, or in the initial state (i.e. only has inherent taint).
            pd->a = d1.b; //weak TF propagation
            foo0(&d0); //d0.a can be tainted by d1.a, d1.b, or in initial state.
            d0.a = 0; //strong taint kill propagation
            foo1(&d0); //d0.a is not tainted now, so there should be no warning.
        default:
            break;
    }
    return 0;
}

int main(int argc, char **argv){
    ioctl0(argc,0);
    ioctl1(argc,0);
    ioctl2(argc,0);
    return 0;
}
