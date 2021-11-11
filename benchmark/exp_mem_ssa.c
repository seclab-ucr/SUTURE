#include<stdio.h>
#include<stdlib.h>

struct data {
    int a,b;
} d;

int foo(int c) {
    int r;
    if(c>0){
        r += c;
        d.a += r;
    }else{
        r -= c;
        d.a -= r;
    }
    return r;
}

int main(int argc, char **argv){
    foo(argc);
    return 0;
}
