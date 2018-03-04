// Kernel debugging code.
// Called throughout the kernel, especially by assert() macro.
// See COPYRIGHT for copyright information.

#include <stdarg.h>
#include <x86.h>
#include <stdio.h>
#include <debug.h>

// Variable panicstr contains argument to first call to panic; used as flag
// to indicate that the kernel has already called panic and avoid recursion.
static const char *panicstr;

void debug_normal(const char *file, int line, const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	cprintf("[D] %s:%d: ", file, line);
	vcprintf(fmt, ap);
	va_end(ap);
}

// Panic is called on unresolvable fatal errors.
// It prints "panic: mesg", and then enters the kernel monitor.
void debug_panic(const char *file, int line, const char *fmt, ...)
{
	va_list ap;

	// Avoid infinite recursion if we're panicking from kernel mode.
	if ((read_cs() & 3) == 0) {
		if (panicstr)
			goto dead;
		panicstr = fmt;
	}
	// First print the requested message
	va_start(ap, fmt);
	cprintf("[P] %s:%d: ", file, line);
	vcprintf(fmt, ap);
	cprintf("\n");
	va_end(ap);

 dead:
	halt();
}

/* like panic, but don't */
void debug_warn(const char *file, int line, const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	cprintf("[W] %s:%d: ", file, line);
	vcprintf(fmt, ap);
	cprintf("\n");
	va_end(ap);
}
