#ifndef _PREINIT_LIB_TIMING_H_
#define _PREINIT_LIB_TIMING_H_

#include <preinit/lib/types.h>
#include <preinit/dev/timer.h>
#include <preinit/lib/x86.h>

extern unsigned long long jiffies;

typedef uint32_t
(*run) (void *);

typedef struct runnable
{
    int enable;
    int period;
    void * param;
    run action;
} runnable_t;

/**
 * 1 cycle time of period (in second) needs IRQ_PERIOD(x) irqs
 */
#define IRQ_PERIOD(x)     (FREQ * (x))

void periodic (void);

/**
 * 1 s  = 1000 ms
 * 1 ms = 1000 us
 * 1 us = 1000 ns
 * 1 ns = 2.8 tsc (for a cpu with 2.8 GHz)
 */
int64_t gcc_inline tsc2ns (int64_t tsc);
int64_t gcc_inline tsc2us (int64_t tsc);
int64_t gcc_inline tsc2ms (int64_t tsc);
int64_t gcc_inline tsc2s (int64_t tsc);

int64_t gcc_inline elapse_ns (uint64_t past, uint64_t now);
int64_t gcc_inline elapse_us (uint64_t past, uint64_t now);
int64_t gcc_inline elapse_ms (uint64_t now, uint64_t past);
int32_t gcc_inline elapse_s (uint64_t past, uint64_t now);

/**
 * stop watch
 *
 * --|<-------------.--------------.-------------------->|
 * start           lap             |                    stop
 *   |<--------------------------lap
 */

typedef struct stopwatch
{
    bool enable;
    uint64_t last;
    uint64_t accum;
} stopwatch_t;

typedef enum {
    STW_VMEXIT = 0,

    MAX_STOPWATCH,
} stopwatch_id;


void profiling_init ();
void stopwatch_init ();
void stopwatch_reset (stopwatch_id id);
uint64_t stopwatch_start (stopwatch_id id);
uint64_t stopwatch_stop (stopwatch_id id);
uint64_t stopwatch_lap (stopwatch_id id);

typedef struct {
    uint64_t periodic;
    uint64_t since_boot;
} pf_record_item_t;


typedef struct
{
    const char * name;
    pf_record_item_t tsc;
    pf_record_item_t times;
} pf_record_t;

typedef enum
{
    REC_VMEXIT_ALL = 0,
    REC_VMEXIT_EXCEPTION,
    REC_VMEXIT_EXT_INTR,
    REC_VMEXIT_TRIPLE_FAUL,
    REC_VMEXIT_INIT,
    REC_VMEXIT_SIPI,
    REC_VMEXIT_IO_SMI,
    REC_VMEXIT_SMI,
    REC_VMEXIT_INTR_WINDOW,
    REC_VMEXIT_NMI_WINDOW,
    REC_VMEXIT_TASK_SWITCH,
    REC_VMEXIT_CPUID,
    REC_VMEXIT_GETSEC,
    REC_VMEXIT_HLT,
    REC_VMEXIT_INVD,
    REC_VMEXIT_INVLPG,
    REC_VMEXIT_RDPMC,
    REC_VMEXIT_RDTSC,
    REC_VMEXIT_RSM,
    REC_VMEXIT_VMCALL,
    REC_VMEXIT_VMCLEAR,
    REC_VMEXIT_VMLAUNCH,
    REC_VMEXIT_VMPTRLD,
    REC_VMEXIT_VMPTRST,
    REC_VMEXIT_VMREAD,
    REC_VMEXIT_VMRESUME,
    REC_VMEXIT_VMWRITE,
    REC_VMEXIT_VMXOFF,
    REC_VMEXIT_VMXON,
    REC_VMEXIT_CR_ACCESS,
    REC_VMEXIT_DR_ACCESS,
    REC_VMEXIT_INOUT,
    REC_VMEXIT_INOUT_SERIAL,
    REC_VMEXIT_INOUT_VPIT,
    REC_VMEXIT_INOUT_VPIC,
    REC_VMEXIT_INOUT_NVRAM,
    REC_VMEXIT_INOUT_KBD,
    REC_VMEXIT_INOUT_VIRTIO,
    REC_VMEXIT_INOUT_OTHERS,


    REC_VMEXIT_RDMSR,
    REC_VMEXIT_WRMSR,
    REC_VMEXIT_INVAL_VMCS,
    REC_VMEXIT_INVAL_MSR,
    REC_VMEXIT_MWAIT,
    REC_VMEXIT_MTF,
    REC_VMEXIT_MONITOR,
    REC_VMEXIT_PAUSE,
    REC_VMEXIT_MCE,
    REC_VMEXIT_TPR,
    REC_VMEXIT_APIC,
    REC_VMEXIT_GDTR_IDTR,
    REC_VMEXIT_LDTR_TR,
    REC_VMEXIT_EPT_FAULT,
    REC_VMEXIT_EPT_MISCONFIG,
    REC_VMEXIT_INVEPT,
    REC_VMEXIT_RDTSCP,
    REC_VMEXIT_VMX_PREEMPT,
    REC_VMEXIT_INVVPID,
    REC_VMEXIT_WBINVD,
    REC_VMEXIT_XSETBV,
    REC_VMEXIT_RDRAND,
    REC_VMEXIT_INVPCID,
    REC_VMEXIT_VMFUNC,

    MAX_TSC_RECORDS
} pf_record_id;

uint64_t pf_record (pf_record_id id, uint64_t interval);
void pf_record_tick (pf_record_id id);

typedef struct trace_item {
    const char * name;
    uint64_t tsc;
} trace_item_t;

#define MAX_TRACE_PATH  32

typedef struct trace {
    int current;
    bool enable;
    trace_item_t ti[MAX_TRACE_PATH];
} trace_t;

typedef enum
{
    TR_YIELD = 0,
    TR_GET_TSC_PER_MS = 1,
    TR_SPAWN = 2,
    TR_PGFLT = 3,
    MAX_TRACES
} trace_id_t;


void trace_init (trace_id_t id);
void trace_enable (trace_id_t id);
void trace_disable (trace_id_t id);
void trace_add (trace_id_t id, const char * name);
void trace_dump (trace_id_t id);


#ifdef PROFILING
#define tri(id, name) do { \
        trace_add ((id), (name)); \
    } while (0)
#else

#define tri(id, name) do { \
    } while (0)

#endif



#endif /* !_PREINIT_LIB_TIMING_H_ */

