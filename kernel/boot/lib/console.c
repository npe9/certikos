#include <x86.h>
#include <stdarg.h>
#include <video.h>
/* #include <kbd.h> */
#include <console.h>

/***** General device-independent console code *****/
// Here we manage the console input buffer,
// where we stash characters received from the keyboard or serial port
// whenever the corresponding interrupt occurs.

static void cons_putc(int c);

static struct {
	uint8_t buf[CONSBUFSIZE];
	uint32_t rpos;
	uint32_t wpos;
} cons;

void cons_intr(int (*proc)(void))
{
    int c;
    while ((c = (*proc)()) != -1) {
	if (c == 0)
	    continue;
	cons.buf[cons.wpos++] = c;
	if (cons.wpos == CONSBUFSIZE)
	    cons.wpos = 0;
    }
}

/* int */
/* cons_getc(void) */
/* { */
/*     int c; */

/*     kbd_intr(); */

/*     if (cons.rpos != cons.wpos) { */
/*	c = cons.buf[cons.rpos++]; */
/*	if (cons.rpos == CONSBUFSIZE) */
/*	    cons.rpos = 0; */
/*	return c; */
/*     } */
/*     return 0; */
/* } */

// output a character to the console
static void
cons_putc(int c)
{
//	serial_putc(c);
	video_putc(c);
}

// initialize the console devices
void
cons_init(void)
{
//	if (!cpu_onboot())	// only do once, on the boot CPU
//		return;

	video_init();
	/* kbd_init(); */
}

// `High'-level console I/O.  Used by readline and cprintf.
void
cputs(const char *str)
{
	while (*str)
		cons_putc(*str++);
}
