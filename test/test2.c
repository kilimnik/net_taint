#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main2()
{
    char buf1[] = "123";
    char* buf = malloc(4);
    strcpy(buf, buf1);

    printf("%s\n", buf);

    *buf++;

    printf("%s\n", buf);

    (*buf)++;

    printf("%s\n", buf);

    ++*buf;

    printf("%s\n", buf);

    ++(*buf);

    printf("%s\n", buf);
}