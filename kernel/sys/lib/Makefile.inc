# -*-Makefile-*-

OBJDIRS		+= $(KERN_OBJDIR)/lib

KERN_SRCFILES	+= $(KERN_DIR)/lib/entry.S
KERN_SRCFILES	+= $(KERN_DIR)/lib/string.c
KERN_SRCFILES	+= $(KERN_DIR)/lib/x86.c
KERN_SRCFILES	+= $(KERN_DIR)/lib/seg.c
KERN_SRCFILES	+= $(KERN_DIR)/lib/trap_asm.S
KERN_SRCFILES	+= $(KERN_DIR)/lib/sysenter_asm.S
KERN_SRCFILES	+= $(KERN_DIR)/lib/user.c

$(KERN_OBJDIR)/lib/%.o: $(KERN_DIR)/lib/%.c
	@echo + cc[KERN/lib] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<

$(KERN_OBJDIR)/lib/%.o: $(KERN_DIR)/lib/%.S
	@echo + as[KERN/lib] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<
