#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef long unsigned int (*hStrLenFunc)(const char *str);

int main2()
{
    hStrLenFunc strLenFunc = &strlen;
    return (*strLenFunc)("123");
}

int main()
{
    return main2();
}
