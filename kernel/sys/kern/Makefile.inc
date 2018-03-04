# -*-Makefile-*-

OBJDIRS		+= $(KERN_OBJDIR)/kern

KERN_SRCFILES	+= $(KERN_DIR)/kern/certikos.S

# lagency
KERN_SRCFILES	+= $(KERN_DIR)/kern/unimplemented.c

$(KERN_OBJDIR)/kern/%.o: $(KERN_DIR)/kern/%.c
	@echo + $(COMP_NAME)[KERN/kern] $<
	@mkdir -p $(@D)
	$(V)$(CCOMP) $(CCOMP_KERN_CFLAGS) -c -o $@ $<
	$(V)$(CCOMP) $(CCOMP_KERN_CFLAGS) -S -O -o ${@}.S $<


$(KERN_OBJDIR)/kern/%.o: $(KERN_DIR)/kern/%.S
	@echo + as[KERN/kern] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<