# -*-Makefile-*-

OBJDIRS		+= $(KERN_OBJDIR)/preinit/lib

KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/printfmt.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/dprintf.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/debug.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/mboot.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/seg.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/types.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/string.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/elf.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/video.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/timing.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/pmap.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/trap.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/x86.c
#KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/vmx_x86.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/syscall.c
#KERN_SRCFILES	+= $(KERN_DIR)/preinit/lib/vmcs_dump.c

$(KERN_OBJDIR)/preinit/lib/%.o: $(KERN_DIR)/preinit/lib/%.c
	@echo + cc[PREINIT/lib] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<

$(KERN_OBJDIR)/preinit/lib/%.o: $(KERN_DIR)/preinit/lib/%.S
	@echo + as[PREINIT/lib] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<
