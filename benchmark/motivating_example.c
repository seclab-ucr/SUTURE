#include<stdio.h>
#include<stdlib.h>

typedef struct data {
    __int32_t a;
    char b[4];
} data;
data d;

int __attribute__((noinline)) foo(int n, char c) {
    if (n == 0) {
        d.b[1] = c;
    }
    return 0;
}

int entry0(int cmd, char user_input) {
    switch (cmd)
    {
    case 0:
        d.b[0] = user_input;
        break;
    default:
        foo(cmd,user_input);
    }
    return 0;
}

int __attribute__((noinline)) bar(char *p) {
    *(p+4) += 0xf0; //Overflow site (1)
    return 0;
}

int entry1() {
    bar((char*)&d);
    d.b[0] = 0;
    return 0;
}

int entry2() {
    char a[8];
    a[0] = d.b[1] + 0xf0; //Overflow site (2)
    printf("%c\n",a[0]);
    return 0;
}

//This "main()" exists only to make the file compilable, we can assume that this module
//only has three entry functions which are entry0 - entry2 defined above.
int main(int argc, char **argv) {
    entry0(argc,**argv);
    entry1();
    entry2();
    return 0;
}
