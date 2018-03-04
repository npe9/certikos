#include <preinit/dev/tsc.h>
#include <preinit/lib/types.h>

uint32_t
tsc_freq_lo(void)
{
	return (tsc_per_ms * 1000) & 0xffffffff;
}

uint32_t
tsc_freq_hi(void)
{
	return ((tsc_per_ms * 1000) >> 32) & 0xffffffff;
}
