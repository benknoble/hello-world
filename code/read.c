#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    FILE *f = fopen("dne", "r");
    if (f == NULL)
        exit(1);
    printf("%c\n", fgetc(f));
}
