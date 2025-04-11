#ifndef TREE_THREAD_H
#define TREE_THREAD_H

#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>

typedef struct {
    int level;      
    int max_depth;  
} ThreadParam;

void* node_thread(void* arg);

#endif
