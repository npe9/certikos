#include <proc.h>
#include <stdio.h>
#include <syscall.h>
#include <sysenter.h>

#define WARMINGUP 10
#define NO_WARMINGUP 0
#define ROOT_QUOTA 720896

int
main (int argc, char **argv)
{
    printf ("profiling is running\n");


//    unit_profiling (&t1, &t2, unit_sys_get_tsc_per_ms, 1, WARMINGUP);
//
//    printf ("sys_get_tsc_per_ms: start %llu\n end %llu\n (%llu)", t1, t2,
//        t2 - t1);
//
//    unit_profiling (&t1, &t2, unit_sys_spawn, 2, WARMINGUP);
//
//    printf ("sys_spawn: start %llu\n end %llu\n (%llu)", t1, t2, t2 - t1);
//
//    printf ("chunk = 0x%08x\n", chunk);
//    current_page_idx = 0;
//
//    unit_profiling (&t1, &t2, unit_pft_handling, 3, WARMINGUP);
//
//    printf ("pgf_handl: start %llu\n end %llu\n (%llu)", t1, t2, t2 - t1);

    while (1)
    {
        yield ();
    }
    return 0;
}
