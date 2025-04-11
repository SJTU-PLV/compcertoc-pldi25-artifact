#include "node.h"

void* node_thread(void* arg) {
    ThreadParam* param = (ThreadParam*)arg;
    int current_level = param->level;
    int max_depth = param->max_depth;
    
    free(param);

    printf("Level %d thread started\n", current_level);
    
    if (current_level < max_depth) {
        pthread_t left, right;
        
        ThreadParam* left_param = malloc(sizeof(ThreadParam));
        left_param->level = current_level + 1;
        left_param->max_depth = max_depth;

        ThreadParam* right_param = malloc(sizeof(ThreadParam));
        right_param->level = current_level + 1;
        right_param->max_depth = max_depth;

        pthread_create(&left, NULL, node_thread, left_param);
        pthread_create(&right, NULL, node_thread, right_param);

        pthread_join(left, NULL);
        pthread_join(right, NULL);
    }
    
    printf("Level %d thread finished\n", current_level);
    return NULL;
}
