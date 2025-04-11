#include "worker.h"

int main() {
    int sum = 0;
    pthread_t threads[2];
    struct ThreadArgs args[2] = {
      {1, &sum, "Hello from thread 1"},
      {2, &sum, "Greetings from thread 2"}
    };

    for (int i = 0; i < 2; i++) {
        pthread_create(&threads[i], NULL, worker_thread, &args[i]);
    }

    for (int i = 0; i < 2; i++) {
        pthread_join(threads[i], NULL);
    }

    printf("The sum of thread ids : %d\n", sum);
    return 0;
}
