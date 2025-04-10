#include <stdlib.h>

typedef struct { 
	int *input;
	int *result;
	int  size;
} Arg;

void encrypt (int input, int *result);

void* server(void *a)
{
	Arg *arg = (Arg *) a;
	int *input = arg->input;
	int *result = arg->result;
	int size = arg->size;

	for (int i = 0; i < size ; i++) {
		encrypt(input[i], result + i);
		// yield();
	}

	return NULL;
}
