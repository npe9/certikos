#include <proc.h>
#include <stdio.h>
#include <syscall.h>

int
main (int argc, char **argv)
{
    while (1)
    {
        yield ();
    }

    return 0;
}
