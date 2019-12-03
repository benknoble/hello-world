#include <stdio.h>

int sum(int a, int b) {
    return a + b;
}

int inc (int a) {
    return a + 1;
}

void displayResult(int (*f)  (int, int), int a, int b) {
    printf("%d\n", (*f)(a,b));
}

int main(int argc, char **argv) {
    displayResult(sum, 3, 4);
    displayResult(inc, 3, 4);
}
