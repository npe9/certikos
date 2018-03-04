#ifndef _CERTIKOS_BOOT_STDIO_H_
#define _CERTIKOS_BOOT_STDIO_H_

#include <types.h>
#include <stdarg.h>

#ifndef NULL
#define NULL	((void *) 0)
#endif				/* !NULL */

#ifdef BOOT_CONSOLE

int cons_getc(void);

#define putchar(c)	fputc(c, stdout)
#define putc(c,fh)	fputc(c, fh)
#define getchar()	cons_getc()
#define getc()	cons_getc()

void printfmt(void (*putch) (int, void *), void *putdat, const char *fmt, ...);
void vprintfmt(void (*putch) (int, void *), void *putdat, const char *fmt,
	       va_list);
int sprintf(char *str, const char *fmt, ...);
int vsprintf(char *str, const char *fmt, va_list);
int snprintf(char *str, int size, const char *fmt, ...);
int vsnprintf(char *str, int size, const char *fmt, va_list);

void cputs(const char *str);

int cprintf(const char *fmt, ...);
int vcprintf(const char *fmt, va_list);

#else /* BOOT_CONSOLE */

int cons_getc(void)
{
	return 0;
}

#define putchar(c)	do {} while (0)
#define putc(c,fh)	do {} while (0)
#define getchar()	do {} while (0)
#define getc()		do {} while (0)

void printfmt(void (*putch) (int, void *), void *putdat, const char *fmt, ...)
{
}

void vprintfmt(void (*putch) (int, void *), void *putdat, const char *fmt,
	       va_list va)
{
}

int sprintf(char *str, const char *fmt, ...)
{
	return 0;
}

int vsprintf(char *str, const char *fmt, va_list va)
{
	return 0;
}

int snprintf(char *str, int size, const char *fmt, ...)
{
	return 0;
}

int vsnprintf(char *str, int size, const char *fmt, va_list va)
{
	return 0;
}

void cputs(const char *str)
{
}

int cprintf(const char *fmt, ...)
{
	return 0;
}

int vcprintf(const char *fmt, va_list va)
{
	return 0;
}

#endif /* !BOOT_CONSOLE */

#endif /* !_CERTIKOS_BOOT_STDIO_H_ */
