#ifndef WORKER_H
#define WORKER_H

#include <stdio.h>
#include <pthread.h>

struct ThreadArgs {
    int id;
    int* sum;
    const char* message;
};

void* worker_thread(void* args);

#endif
