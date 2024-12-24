#include <stdio.h>
#include <stdint.h>

// compile with clang's -ftrapv !
// make overflow CFLAGS=-ftrapv

int main(void) {
    int32_t a = 1<<30;
    int32_t b = 1<<30;
    int32_t result = a + b;
    printf("%d\n", result);
}
