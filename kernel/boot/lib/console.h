#ifndef _CERTIKOS_BOOT_CONSOLE_H_
#define _CERTIKOS_BOOT_CONSOLE_H_

#ifdef BOOT_CONSOLE

#include <types.h>

#define CONSBUFSIZE 512

struct iocons;

void cons_init(void);
void cons_intr(int (*proc)(void));

#else /* BOOT_CONSOLE */

void cons_init(void)
{
}

void cons_intr(int (*proc)(void))
{
}

#endif /* !BOOT_CONSOLE */

#endif /* !_CERTIKOS_BOOT_CONSOLE_H_  */
