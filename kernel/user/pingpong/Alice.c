#include <proc.h>
#include <stdio.h>
#include <syscall.h>
#include <sysenter.h>
#include <x86.h>

#define SIZE 100000000
#define PGSIZE 4096
#define BIT 'a'

char buf[SIZE];

void write_buf(int i)
{
  unsigned int new_quota;
  buf[i] = BIT;
  new_quota = get_quota();

  printf("Alice: I did something secret, my quota is now %d.\n", new_quota);
}

int
main (int argc, char **argv)
{
  printf("\nHello! This is Alice's process. I've been told that this execution environment is secure,\n");
  printf("so I will be performing top secret computations here!\n");

  printf("Before I begin, I will be a nice person and yield to other processes. See you in a bit!\n");

  yield();

  printf("\nAlice: Hello again! Now it's time for me to perform some secret computations that will\n");
  printf("require allocating memory.\n");

  unsigned int quota = get_quota();
  int i, j, k;
  printf("Alice: I have %d available quota for my computations. How nice!\n", quota);
  for (i = 0; i < 5; i++) {
    for (j = 0; j < 5; j++) {
      k = i*PGSIZE*PGSIZE + (j+1)*PGSIZE/2;
      write_buf(k);
    }
  }

  printf("Alice: I've finished my top secret computation! I sure hope no one was able to learn anything\n");
  printf("about what I did. Goodbye!\n");

  while (1) {
	//printf ("Alice silently yield\n");
	yield ();
  }	
  return 0;
}
