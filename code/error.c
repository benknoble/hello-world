#include <unistd.h>
#include <stdio.h>

int main() {
    execlp("dne", "dne");
    perror("my_program");
}
