# -*-Makefile-*-

ifdef BOOT_DEBUG
BOOT_LIB_OBJFILES += $(OBJDIR)/boot/debug.o
ifndef BOOT_CONSOLE
BOOT_CONSOLE := " "
BOOT_CFLAGS += -DBOOT_CONSOLE
endif
endif

ifdef BOOT_CONSOLE
BOOT_LIB_OBJFILES += $(OBJDIR)/boot/console.o
BOOT_LIB_OBJFILES += $(OBJDIR)/boot/cprintf.o
BOOT_LIB_OBJFILES += $(OBJDIR)/boot/video.o
BOOT_LIB_OBJFILES += $(OBJDIR)/boot/printfmt.o
endif

BOOT_LIB_OBJFILES += $(OBJDIR)/boot/biosdisk.o
BOOT_LIB_OBJFILES += $(OBJDIR)/boot/fs.o
BOOT_LIB_OBJFILES += $(OBJDIR)/boot/string.o
BOOT_LIB_OBJFILES += $(OBJDIR)/boot/int13.o
BOOT_LIB_OBJFILES += $(OBJDIR)/boot/switch_mode.o

$(OBJDIR)/boot/%.o: boot/lib/%.c
	@echo + cc[BOOT] $<
	@mkdir -p $(@D)
	$(V)$(CC) -nostdinc $(BOOT_CFLAGS) -Os -c -o $@ $<

$(OBJDIR)/boot/%.o: boot/lib/%.S
	@echo + as[BOOT] $<
	@mkdir -p $(@D)
	$(V)$(CC) -nostdinc $(BOOT_CFLAGS) -Os -c -o $@ $<
