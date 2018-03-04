# -*-Makefile-*-

OBJDIRS		+= $(KERN_OBJDIR)/preinit

KERN_SRCFILES	+= $(KERN_DIR)/preinit/preinit.c

include		$(KERN_DIR)/preinit/dev/Makefile.inc
include		$(KERN_DIR)/preinit/lib/Makefile.inc

$(KERN_OBJDIR)/preinit/%.o: $(KERN_DIR)/preinit/%.c
	@echo + cc[PREINIT] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<

$(KERN_OBJDIR)/preinit/%.o: $(KERN_DIR)/preinit/%.S
	@echo + as[PREINIT] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<
