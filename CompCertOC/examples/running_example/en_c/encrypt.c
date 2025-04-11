int key = 42;
void encrypt (int input, int *result)
{
	int output = input ^ key;
	*result = output;
}
