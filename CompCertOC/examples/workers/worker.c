#include "worker.h"

void* worker_thread(void* args) {
    struct ThreadArgs* params = (struct ThreadArgs*)args;
    (*(params->sum)) += params->id;
    printf("Thread %d says: %s\n", params->id, params->message);
    return NULL;
}
