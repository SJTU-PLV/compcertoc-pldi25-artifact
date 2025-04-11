#include <pthread.h>
#include <stdio.h>

void *thread(void *p) {(*(int *)p)++; return NULL; }
int main(){
  int i = 0; pthread_t tid;
  pthread_create (&tid, NULL, thread, (void *)&i);
  pthread_join(tid,NULL);
  printf("%d\n",i);
  return 0;
}
