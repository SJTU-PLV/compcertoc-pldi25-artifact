#include "node.h"

int main() {
    pthread_t root;
    const int max_depth = 3;

    ThreadParam* root_param = malloc(sizeof(ThreadParam));
    root_param->level = 0;
    root_param->max_depth = max_depth;

    pthread_create(&root, NULL, node_thread, root_param);
    
    pthread_join(root, NULL);
    
    printf("\n All tree threads completed\n");
    return 0;
}
