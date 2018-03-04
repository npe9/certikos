#ifdef DEBUG_MSG

#include <preinit/dev/console.h>
#include <preinit/dev/serial.h>
#include <preinit/lib/video.h>

#include <preinit/lib/debug.h>
#include <preinit/lib/stdarg.h>

struct dprintbuf
{
    int idx; /* current buffer index */
    int cnt; /* total bytes printed so far */
    char buf[CONSOLE_BUFFER_SIZE];
};

static void
cputs (const char *str)
{
    while (*str)
    {
        serial_putc (*str);
        video_putc (*str);
        str += 1;
    }
}

static void
putch (int ch, struct dprintbuf *b)
{
    b->buf[b->idx++] = ch;
    if (b->idx == CONSOLE_BUFFER_SIZE - 1)
    {
        b->buf[b->idx] = 0;
        cputs (b->buf);
        b->idx = 0;
    }
    b->cnt++;
}

int
vdprintf (const char *fmt, va_list ap)
{
    struct dprintbuf b;

    b.idx = 0;
    b.cnt = 0;
    vprintfmt ((void*) putch, &b, fmt, ap);

    b.buf[b.idx] = 0;
    cputs (b.buf);

    return b.cnt;
}

int
dprintf (const char *fmt, ...)
{
    va_list ap;
    int cnt;

    va_start(ap, fmt);
    cnt = vdprintf (fmt, ap);
    va_end(ap);

    return cnt;
}

/***********************************
 * Video single version
 ***********************************/


static void
vcputs (const char *str)
{
    while (*str)
    {
        video_putc (*str ++);
    }
}

static void
vputch (int ch, struct dprintbuf *b)
{
    b->buf[b->idx++] = ch;
    if (b->idx == CONSOLE_BUFFER_SIZE - 1)
    {
        b->buf[b->idx] = 0;
        vcputs (b->buf);
        b->idx = 0;
    }
    b->cnt++;
}

int
vvdprintf (const char *fmt, va_list ap)
{
    struct dprintbuf b;

    b.idx = 0;
    b.cnt = 0;
    vprintfmt ((void*) vputch, &b, fmt, ap);

    b.buf[b.idx] = 0;
    vcputs (b.buf);

    return b.cnt;
}

int
vprintf (const char *fmt, ...)
{
    va_list ap;
    int cnt;

    va_start(ap, fmt);
    cnt = vvdprintf (fmt, ap);
    va_end(ap);

    return cnt;
}

#endif /* DEBUG_MSG */
