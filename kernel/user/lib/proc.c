#include <proc.h>
#include <syscall.h>
#include <types.h>

pid_t
spawn(uint32_t elf_id, uint32_t quota)
{
	return sys_spawn(elf_id, quota);
}

void
yield(void)
{
	sys_yield();
}

unsigned int get_quota(void)
{
  return sys_get_quota();
}
