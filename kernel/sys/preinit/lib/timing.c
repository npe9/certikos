#include <preinit/lib/timing.h>
#include <preinit/lib/debug.h>
#include <preinit/lib/x86.h>
#include <preinit/dev/tsc.h>
#include <preinit/lib/video.h>

unsigned long long jiffies = 0ull;

static stopwatch_t stopwatches[MAX_STOPWATCH];

pf_record_t pf_records[MAX_TSC_RECORDS];

trace_t traces[MAX_TRACES];

/**
 * Compute with 96 bit intermediate result: (a*b)/c
 */
static gcc_inline uint64_t
muldiv64 (uint64_t a, uint32_t b, uint32_t c)
{
    union
    {
        uint64_t ll;
        struct
        {
            uint32_t low, high;
        } l;
    } u, res;
    uint64_t rl, rh;

    u.ll = a;
    rl = (uint64_t) u.l.low * (uint64_t) b;
    rh = (uint64_t) u.l.high * (uint64_t) b;
    rh += (rl >> 32);
    res.l.high = rh / c;
    res.l.low = (((rh % c) << 32) + (rl & 0xffffffff)) / c;
    return res.ll;
}

int64_t gcc_inline
tsc2ns (int64_t tsc)
{
    return muldiv64 (tsc, 1000u * 1000u, tsc_per_ms);
}

int64_t gcc_inline
tsc2us (int64_t tsc)
{
    return muldiv64 (tsc, 1000u, tsc_per_ms);
}

int64_t gcc_inline
tsc2ms (int64_t tsc)
{
    return tsc / tsc_per_ms;
}

int64_t gcc_inline
tsc2s (int64_t tsc)
{
    return tsc / 1000u / tsc_per_ms;
}

void gcc_inline
tsc2time (uint64_t tsc, char * output)
{
    int64_t t1, t2 = 0;
    char * unit;

    if ((t1 = tsc2s (tsc)) == 0)
    {
        if ((t1 = tsc2ms (tsc)) == 0)
        {
            if ((t1 = tsc2us (tsc)) == 0)
            {
                t1 = tsc2ns (tsc);
                unit = "ns";
            }
            else
            {
                t2 = tsc2ns (tsc / 1000);
                unit = "us";
            }
        }
        else
        {
            t2 = tsc2us (tsc / 1000);
            unit = "ms";
        }
    }
    else
    {
        t2 = tsc2ms (tsc / 1000);
        unit = "s";
    }

    sprintf (output, "%lld.%lld %s", t1, t2, unit);
}

int64_t gcc_inline
elapse_ns (uint64_t past, uint64_t now)
{
    KERN_ASSERT(now > 0 && past > 0);

    return tsc2ns (now - past);
}

int64_t gcc_inline
elapse_us (uint64_t past, uint64_t now)
{
    KERN_ASSERT(now > 0 && past > 0);

    return tsc2us (now - past);
}

int64_t gcc_inline
elapse_ms (uint64_t now, uint64_t past)
{
    KERN_ASSERT(now > 0 && past > 0);

    return tsc2ms (now - past);
}

int32_t gcc_inline
elapse_s (uint64_t past, uint64_t now)
{
    KERN_ASSERT(now > 0 && past > 0);

    return tsc2s (now - past);
}

void
stopwatch_reset (stopwatch_id id)
{
    KERN_ASSERT(id >= 0 && id < MAX_STOPWATCH);
    stopwatches[id].last = 0;
    stopwatches[id].accum = 0;
    stopwatches[id].enable = FALSE;
}

void
stopwatch_init ()
{
    int i;
    for (i = 0; i < MAX_STOPWATCH; i++)
    {
        stopwatch_reset (i);
    }
}

uint64_t
stopwatch_start (stopwatch_id id)
{
    KERN_ASSERT(id >= 0 && id < MAX_STOPWATCH);

    stopwatches[id].last = rdtsc ();

    stopwatches[id].enable = TRUE;
    return stopwatches[id].last;
}

uint64_t
stopwatch_stop (stopwatch_id id)
{

    uint64_t now = rdtsc (), interval;

    KERN_ASSERT(id >= 0 && id < MAX_STOPWATCH);

    if (!stopwatches[id].enable)
    {
        return 0ull;
    }

    interval = now - stopwatches[id].last;
    stopwatches[id].accum += interval;

    stopwatches[id].enable = FALSE;

    return interval;
}

uint64_t
stopwatch_lap (stopwatch_id id)
{
    uint64_t now = rdtsc ();

    KERN_ASSERT(id >= 0 && id < MAX_STOPWATCH);

    if (!stopwatches[id].enable)
    {
        return 0ull;
    }

    return now - stopwatches[id].last;
}

uint64_t
stopwatch_record (stopwatch_id id)
{
    KERN_ASSERT(id >= 0 && id < MAX_STOPWATCH);

    return stopwatches[id].accum;
}

void
pf_record_init ()
{
    int i;
    for (i = 0; i < MAX_TSC_RECORDS; i++)
    {
        pf_records[i].tsc.periodic = 0;
        pf_records[i].tsc.since_boot = 0;
        pf_records[i].times.periodic = 0;
        pf_records[i].times.since_boot = 0;
    }

    pf_records[REC_VMEXIT_ALL].name = "all vmexit";
    pf_records[REC_VMEXIT_EXCEPTION].name = "exception";
    pf_records[REC_VMEXIT_EXT_INTR].name = "ext_intr";
    pf_records[REC_VMEXIT_TRIPLE_FAUL].name = "triple_faul";
    pf_records[REC_VMEXIT_INIT].name = "init";
    pf_records[REC_VMEXIT_SIPI].name = "sipi";
    pf_records[REC_VMEXIT_IO_SMI].name = "io_smi";
    pf_records[REC_VMEXIT_SMI].name = "smi";
    pf_records[REC_VMEXIT_INTR_WINDOW].name = "intr_window";
    pf_records[REC_VMEXIT_NMI_WINDOW].name = "nmi_window";
    pf_records[REC_VMEXIT_TASK_SWITCH].name = "task_switch";
    pf_records[REC_VMEXIT_CPUID].name = "cpuid";
    pf_records[REC_VMEXIT_GETSEC].name = "getsec";
    pf_records[REC_VMEXIT_HLT].name = "hlt";
    pf_records[REC_VMEXIT_INVD].name = "invd";
    pf_records[REC_VMEXIT_INVLPG].name = "invlpg";
    pf_records[REC_VMEXIT_RDPMC].name = "rdpmc";
    pf_records[REC_VMEXIT_RDTSC].name = "rdtsc";
    pf_records[REC_VMEXIT_RSM].name = "rsm";
    pf_records[REC_VMEXIT_VMCALL].name = "vmcall";
    pf_records[REC_VMEXIT_VMCLEAR].name = "vmclear";
    pf_records[REC_VMEXIT_VMLAUNCH].name = "vmlaunch";
    pf_records[REC_VMEXIT_VMPTRLD].name = "vmptrld";
    pf_records[REC_VMEXIT_VMPTRST].name = "vmptrst";
    pf_records[REC_VMEXIT_VMREAD].name = "vmread";
    pf_records[REC_VMEXIT_VMRESUME].name = "vmresume";
    pf_records[REC_VMEXIT_VMWRITE].name = "vmwrite";
    pf_records[REC_VMEXIT_VMXOFF].name = "vmxoff";
    pf_records[REC_VMEXIT_VMXON].name = "vmxon";
    pf_records[REC_VMEXIT_CR_ACCESS].name = "cr_access";
    pf_records[REC_VMEXIT_DR_ACCESS].name = "dr_access";
    pf_records[REC_VMEXIT_INOUT].name = "inout";
    pf_records[REC_VMEXIT_INOUT_SERIAL].name = "inout.serial";
    pf_records[REC_VMEXIT_INOUT_VPIT].name = "inout.vpit";
    pf_records[REC_VMEXIT_INOUT_VPIC].name = "inout.vpic";
    pf_records[REC_VMEXIT_INOUT_NVRAM].name = "inout.nvram";
    pf_records[REC_VMEXIT_INOUT_KBD].name = "inout.pad";
    pf_records[REC_VMEXIT_INOUT_VIRTIO].name = "inout.vio";
    pf_records[REC_VMEXIT_INOUT_OTHERS].name = "inout.others";

    pf_records[REC_VMEXIT_RDMSR].name = "rdmsr";
    pf_records[REC_VMEXIT_WRMSR].name = "wrmsr";
    pf_records[REC_VMEXIT_INVAL_VMCS].name = "inval_vmcs";
    pf_records[REC_VMEXIT_INVAL_MSR].name = "inval_msr";
    pf_records[REC_VMEXIT_MWAIT].name = "mwait";
    pf_records[REC_VMEXIT_MTF].name = "mtf";
    pf_records[REC_VMEXIT_MONITOR].name = "monitor";
    pf_records[REC_VMEXIT_PAUSE].name = "pause";
    pf_records[REC_VMEXIT_MCE].name = "mce";
    pf_records[REC_VMEXIT_TPR].name = "tpr";
    pf_records[REC_VMEXIT_APIC].name = "apic";
    pf_records[REC_VMEXIT_GDTR_IDTR].name = "gdtr_idtr";
    pf_records[REC_VMEXIT_LDTR_TR].name = "ldtr_tr";
    pf_records[REC_VMEXIT_EPT_FAULT].name = "ept_fault";
    pf_records[REC_VMEXIT_EPT_MISCONFIG].name = "ept_misconfig";
    pf_records[REC_VMEXIT_INVEPT].name = "invept";
    pf_records[REC_VMEXIT_RDTSCP].name = "rdtscp";
    pf_records[REC_VMEXIT_VMX_PREEMPT].name = "vmx_preempt";
    pf_records[REC_VMEXIT_INVVPID].name = "invvpid";
    pf_records[REC_VMEXIT_WBINVD].name = "wbinvd";
    pf_records[REC_VMEXIT_XSETBV].name = "xsetbv";
    pf_records[REC_VMEXIT_RDRAND].name = "rdrand";
    pf_records[REC_VMEXIT_INVPCID].name = "invpcid";
    pf_records[REC_VMEXIT_VMFUNC].name = "vmfunc";
}

void
profiling_init ()
{
    stopwatch_init ();
    pf_record_init ();
}

uint64_t
pf_record (pf_record_id id, uint64_t interval)
{
    KERN_ASSERT(id >= 0 && id < MAX_TSC_RECORDS);

    pf_records[id].tsc.periodic += interval;
    pf_records[id].times.periodic++;
    return pf_records[id].tsc.periodic;
}

void
pf_record_tick (pf_record_id id)
{
    KERN_ASSERT(id >= 0 && id < MAX_TSC_RECORDS);

    pf_records[id].tsc.since_boot += pf_records[id].tsc.periodic;
    pf_records[id].times.since_boot += pf_records[id].times.periodic;

    pf_records[id].times.periodic = 0;
    pf_records[id].tsc.periodic = 0;
}

void
trace_init (trace_id_t id)
{
    KERN_ASSERT(id >= 0 && id < MAX_TRACES);

    traces[id].current = 0;
}

void
trace_enable (trace_id_t id)
{
    KERN_ASSERT(id >= 0 && id < MAX_TRACES);

    traces[id].enable = TRUE;
}

void
trace_disable (trace_id_t id)
{
    KERN_ASSERT(id >= 0 && id < MAX_TRACES);

    traces[id].enable = FALSE;
}

void gcc_inline
trace_add (trace_id_t id, const char * name)
{
    KERN_ASSERT(id >= 0 && id < MAX_TRACES);

    if (!traces[id].enable)
    {
        return;
    }

    int i = traces[id].current;
    if (i >= MAX_TRACE_PATH)
    {
        return;
    }

    traces[id].ti[i].name = name;
    traces[id].ti[i].tsc = rdtsc ();
    traces[id].current++;
}

void
trace_dump (trace_id_t id)
{
    KERN_ASSERT(id >= 0 && id < MAX_TRACES);

    int i;
    trace_t * tr = &traces[id];
    KERN_INFO("[%d] %d trace points: \n", (int) id, tr->current);
    for (i = 0; i < tr->current; i++)
    {
        KERN_INFO ("%s: %llu\n", tr->ti[i].name, tr->ti[i].tsc);
    }
}

#if defined(CONFIG_APP_VMM) && defined(PROFILING)
static uint32_t
action_print_vmexit (void * p)
{
    KERN_ASSERT(p == NULL);
    int i, t;
    video_clear_screen ();
    video_set_cursor (0, 0);
    for (i = REC_VMEXIT_ALL; i <= REC_VMEXIT_VMFUNC; i++)
    {
        if (pf_records[i].times.since_boot != 0)
        {
            vprintf ("%11s: %8llu (%8llu us) ", pf_records[i].name,
                pf_records[i].times.periodic,
                tsc2us (pf_records[i].tsc.periodic));
            t++;
            if (t % 2 == 0)
            {
                vprintf ("\n");
            }
        }
        pf_record_tick (i);
    }

    return 0;
}
#endif

runnable_t periodic_run[] =
    {
#if defined(CONFIG_APP_VMM) && defined(PROFILING)
        { .enable = TRUE,
          .period = IRQ_PERIOD(1),
          .param = NULL,
          .action = &action_print_vmexit,
        },
#endif
    };

#define MAX_RUNNABLES sizeof(periodic_run) / sizeof(periodic_run[0])

void
periodic (void)
{
    int i;

    jiffies++;

    for (i = 0; i < MAX_RUNNABLES; i++)
    {
        if (periodic_run[i].enable && (jiffies % periodic_run[i].period == 0))
        {
            (*periodic_run[i].action) (periodic_run[i].param);
        }
    }
}

