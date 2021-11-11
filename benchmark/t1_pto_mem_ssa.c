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

int foo1(G *pg) {
    int r;
    if (!pg) {
        return 0;
    }
    data *p = pg->p;
    r = p->a + p->b;
    if (r > 8) {
        printf("r: %d\n",r);
    }else {
        printf("r is small\n");
    }
    return r;
}

int foo2(G *pg) {
    int r;
    if (!pg) {
        return 0;
    }
    data *p = pg->p;
    r = p->a + p->b;
    if (r > 8) {
        printf("r: %d\n",r);
    }else {
        printf("r is small\n");
    }
    return r;
}

int ioctl0(int cmd, void *p) {
    int res;
    data *ui = (data*)p;
    switch(cmd) {
        case 0:
            //g6.p->a = ui->a;
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
            //g6.p->a = ui->a;
            d2.a = ui->a;
            break;
        default:
            break;
    }
    return 0;
}


int ioctl1(int cmd, void *p) {
    int res;
    G *pg;
    data *ui = (data*)p;
    switch(cmd) {
        case 0:
            pg = (ui->a ? &g6 : &g7);
            g6.p = &d2;
            if (ui->b) {
                g6.p = &d0;
                //Exp: g6.p can only point to d0.
                foo1(&g6);
            }else {
                g6.p = &d1;
                //Exp: g6.p can only point to d1.
                foo2(&g6);
            }
            //Exp: g6.p can point to both d0 and d1, but not d2!
            foo0(g6.p);
            pg->p = &d2;
            //Exp: g6.p can point to both d0 ,d1 and d2. (since 'pg' has multiple pto, although post-dom, this is a weak update for g6.p). 
            foo1(&g6);
            g6.p = &d3;
            //Exp: g6.p only points to d3 (post-dom and strong update).
            foo2(&g6);
            break;
        case 1:
            //This case is to test the pto path-coverage (i.e. whether along every path there exists a pto record, if none, we should create a dummy pto for it).
            if (ui->a) {
                g6.p = &d3;
            }
            //here g6.p can still potentially point to anything (e.g. a dummy pointee obj should be created), it's still possible that the TF from ioctl0 and ioctl2 can reach here.
            //Why d0 in ioctl0 or d2 in ioctl2 *can* be this dummy? Imagine that there exists some un-analyzed preliminary code that assigns them as a pointee of g6->p.
            //NOTE that we can match this dummy w/ d0 in ioctl0 or d2 in ioctl2 because case 0 of ioctl1 assigns both d0,d1,d2,d3 as a pointee of G6->p, so our access path based matching can work,
            //if there is no such a "case 0", we will have FNs here.
            //TODO: if we're sure that all preliminary code have been analyzed (so this dummy pto can only come from other parallel code segments), then we need to only match this
            //dummy pto w/ some "winner" ptos to the real objects (e.g. &d3 in case 0 of ioctl 1). 
            foo1(&g6);
        default:
            break;
    }
    return 0;
}

int main(int argc, char **argv){
    g6.p = &d0;
    ioctl0(argc,0);
    ioctl1(argc,0);
    ioctl2(argc,0);
    return 0;
}
