#include <pthread.h>
#include <semaphore.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#define NUM_OPERATIONS 15
#define OUTPUT_LENGTH 20
#define T1_WAIT_SECONDS 5
#define T2_WAIT_SECONDS 1

char shared_str[OUTPUT_LENGTH];
int print_count = 0;
sem_t semaphore;

void *thread1(void *arg) {
    char local_str[OUTPUT_LENGTH] = "THREAD 1 UNLOCK";
    bool done = false;
    while (!done) {
        sleep(T1_WAIT_SECONDS);
        sem_wait(&semaphore); // decrement semaphore
        printf("THREAD 1 LOCK\n");
        // critical section, write to shared buffer
        strcpy(shared_str, local_str);
        // mock "expensive" operation, note thread 2 will wait
        sleep(T1_WAIT_SECONDS);
        printf("%s\n", shared_str);
        print_count++;
        done = (print_count >= NUM_OPERATIONS);
        sem_post(&semaphore); // increment semaphore
    }
}

void *thread2(void *arg) {
    char local_str[OUTPUT_LENGTH] = "THREAD 2 UNLOCK";
    bool done = false;
    while (!done) {
        sleep(T2_WAIT_SECONDS);
        sem_wait(&semaphore); // decrement semaphore
        printf("THREAD 2 LOCK\n");
        // critical section, write to shared buffer
        strcpy(shared_str, local_str);
        sleep(T2_WAIT_SECONDS);
        printf("%s\n", shared_str);
        print_count++;
        done = (print_count >= NUM_OPERATIONS);
        sem_post(&semaphore); // increment semaphore
    }
}

int main()
{
    // initialize semaphore
    // * between threads (second argument is 0)
    // * with initial value 1 (third argument)
    sem_init(&semaphore, 0, 1);
    // create two threads
    pthread_t t1, t2;
    pthread_create(&t1, NULL, thread1, NULL);
    pthread_create(&t2, NULL, thread2, NULL);
    // wait for both threads to terminate
    pthread_join(t1, NULL);
    pthread_join(t2, NULL);
    sem_destroy(&semaphore);
    return 0;
}
