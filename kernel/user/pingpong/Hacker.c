#include <proc.h>
#include <stdio.h>
#include <syscall.h>
#include <sysenter.h>
#include <x86.h>

#define SIZE 100000000
#define PGSIZE 4096
#define BIT 'h'

char buf[SIZE];

void write_buf(int i, unsigned int quota)
{
  unsigned int new_quota;
  buf[i] = BIT;
  new_quota = get_quota();

  printf("Hacker: Wrote \'%c\' to index %d, quota is now %d.", buf[i], i, new_quota);

  if (new_quota < quota)
    printf(" (page fault occurred, allocated %d new page(s))\n", quota - new_quota);
  else
    printf("\n");
}

int
main (int argc, char **argv)
{
  printf("\nHacker process reporting in!\n");
  printf("Here's my secret plan: I'm going to let Alice execute her program and allocate some\n");
  printf("pages. Once she yields back to me, I'll keep allocating pages, until all available\n");
  printf("memory is used. Then, based on how much memory I get, I can learn something about how\n");
  printf("many pages Alice allocated! The more memory I get, the less memory Alice used.\n");

  printf("Ok, yielding now to let Alice execute her program. See you later.\n");
  yield();
  printf("\nHacker: And we're back! Let's see what we can figure out about Alice's memory usage.\n");
  printf("I have a buffer of size %d bytes, I will write a character into various indices to\n", SIZE);
  printf("force the operating system to handle page faults by allocating new pages for me.\n");

  unsigned int quota = get_quota();

  int i, j, k;
  printf("Hacker: Apparently I have %d available quota. That could make this attack difficult...\n", quota);
  for (i = 0; i < 5; i++) {
    int flag = 0;
    for (j = 0; j < 5; j++) {
      quota = get_quota();
      if (quota == 0) {
	flag = 1;
	break;
      }
      k = i*PGSIZE*PGSIZE + (j+1)*PGSIZE/2;
      write_buf(k, quota);
    }
    if (flag) break;
  }

  printf("Hacker: I've been thwarted by CertiKOS, my memory usage was limited only by available quota,\n");
  printf("which is completely independent from Alice's memory usage. I give up :(\n");

  while (1) yield ();
  return 0;
}
