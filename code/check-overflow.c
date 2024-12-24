#include <stdio.h>
#include <stdint.h>
#include <sys/errno.h>

// compile with clang's -ftrapv !
// make check-overflow CFLAGS=-ftrapv

int main(void) {
    int32_t a = 1<<30;
    int32_t b = 1<<30;
    // demo only…
    int32_t result = (b > INT32_MAX - a) ? (errno=ERANGE,perror(NULL),-1) : a + b;
    printf("%d\n", result);
}
