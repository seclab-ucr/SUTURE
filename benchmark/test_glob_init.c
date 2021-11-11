#include<stdio.h>
#include<stdlib.h>

typedef struct data {
    int a,b;
} data;

typedef struct A {
    int a,b;
    data d;
} A;

typedef struct B {
    int a,b;
    data *d;
} B;

data d;

const data e = {1,2};

A sta = {1,2,{3,4}};
A as[] = {{1,2,{3,4}}, {5,6,{7,8}}};
B stb = {1,2,&d};

int main(int argc, char **argv){
    return 0;
}
