# -*-Makefile-*-

BOOT0_OBJFILES += $(OBJDIR)/boot/boot0.o

$(OBJDIR)/boot/boot0: $(BOOT0_OBJFILES)
	@echo + ld[BOOT] $@
	$(V)$(LD) $(BOOT_LDFLAGS) -N -e start -Ttext 0x600 -o $@.elf $^
	$(V)$(OBJDUMP) -S $@.elf > $@.asm
	$(V)$(OBJCOPY) -S -O binary $@.elf $@
	$(V)$(PERL) $(UTILSDIR)/check_size.pl 446 $@

$(OBJDIR)/boot/%.o: boot/boot0/%.c
	@echo + cc[BOOT] $<
	@mkdir -p $(@D)
	$(V)$(CC) -nostdinc $(BOOT_CFLAGS) -Os -c -o $@ $<

$(OBJDIR)/boot/%.o: boot/boot0/%.S
	@echo + as[BOOT] $<
	@mkdir -p $(@D)
	$(V)$(CC) -nostdinc $(BOOT_CFLAGS) -Os -c -o $@ $<
