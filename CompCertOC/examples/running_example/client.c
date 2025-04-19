#include <pthread.h>
#include <stdio.h>

#define N   5

typedef struct { 
	int *input;
	int *result;
	int  size;
} Arg;

void* server(void *a);

int main(void)
{
	pthread_t a;

	int input[N] = {1, 2, 3, 4, 5}, result[N];
	int mask = 0, i;
	Arg arg = {input, result, N};
    
	pthread_create(&a, NULL, server, &arg);

	for (i = 0; i < N; i++) {
		mask += input[i];
		// yield();
	}

	pthread_join(a, NULL);

	for (i = 0; i < N; i++) {
		result[i] = result[i] & mask;
		printf("%d; ", result[i]);
	}
    
	return 0;
}
