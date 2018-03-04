# -*-Makefile-*-

LOADER_OBJFILES += $(OBJDIR)/boot/loader.o
LOADER_OBJFILES += $(OBJDIR)/boot/exec_kernel.o

$(OBJDIR)/boot/loader: $(LOADER_OBJFILES) $(BOOT_LIB_OBJFILES)
	@echo + ld[BOOT] $@
	$(V)$(LD) $(BOOT_LDFLAGS) -e loader -Ttext 0xe000 -o $@ $^ $(GCC_LIB32)
	$(V)$(OBJDUMP) -S $@ > $@.asm

$(OBJDIR)/boot/%.o: boot/loader/%.c
	@echo + cc[BOOT] $<
	@mkdir -p $(@D)
	$(V)$(CC) -nostdinc $(BOOT_CFLAGS) -Os -c -o $@ $<

$(OBJDIR)/boot/%.o: boot/loader/%.S
	@echo + as[BOOT] $<
	@mkdir -p $(@D)
	$(V)$(CC) -nostdinc $(BOOT_CFLAGS) -Os -c -o $@ $<
