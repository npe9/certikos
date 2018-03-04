# -*-Makefile-*-

OBJDIRS		+= $(KERN_OBJDIR)/dev

KERN_SRCFILES	+= $(KERN_DIR)/dev/tsc.c
KERN_SRCFILES	+= $(KERN_DIR)/dev/svm_asm.S
KERN_SRCFILES	+= $(KERN_DIR)/dev/pmap.c

$(KERN_OBJDIR)/dev/%.o: $(KERN_DIR)/dev/%.c
	@echo + cc[KERN/dev] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<

$(KERN_OBJDIR)/dev/%.o: $(KERN_DIR)/dev/%.S
	@echo + as[KERN/dev] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<
