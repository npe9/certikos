# -*-Makefile-*-

OBJDIRS		+= $(KERN_OBJDIR)/preinit/dev

KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/console.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/serial.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/pic.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/tsc.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/timer.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/intr.c
#KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/vmx_drv.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/ide.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/pci.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/disk.c
KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/ahci.c
#KERN_SRCFILES	+= $(KERN_DIR)/preinit/dev/vmx_asm.S


$(KERN_OBJDIR)/preinit/dev/%.o: $(KERN_DIR)/preinit/dev/%.c
	@echo + cc[PREINIT/dev] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<


$(KERN_OBJDIR)/preinit/dev/%.o: $(KERN_DIR)/preinit/dev/%.S
	@echo + as[PREINIT/dev] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(KERN_CFLAGS) -c -o $@ $<
