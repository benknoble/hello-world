#include <stdio.h>

int main(int argc, char **argv) {
    char c = 1;
    char d = (char)1;
    char e = (char)(-1);
    printf("%zu\t%zu\n", sizeof(c), sizeof(d));
    printf("%c\n", e);
}
