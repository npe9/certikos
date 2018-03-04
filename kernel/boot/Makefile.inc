# -*-Makefile-*-

BOOT_DIR	:= $(TOP)/boot

# Compiling and Linking options for the bootloader
BOOT_CFLAGS	:= $(CFLAGS) -Os -m32 -I. -Iboot/include -Iboot/lib
BOOT_LDFLAGS	:= $(LDFLAGS) -m elf_i386

BOOT_DEBUG	:= " "
BOOT_CONSOLE	:= " "

ifdef BOOT_DEBUG
BOOT_COMPILE_DEF += -DBOOT_DEBUG
endif

ifdef BOOT_CONSOLE
BOOT_COMPILE_DEF += -DBOOT_CONSOLE
endif

BOOT_CFLAGS	+= $(BOOT_COMPILE_DEF)

ifdef ENABLE_BOOT_CF
BOOT_CFLAGS	+= -DENABLE_BOOT_CF
endif

# Object files generated for the bootloader
BOOT_BINFILES	+= $(OBJDIR)/boot/boot0
BOOT_BINFILES	+= $(OBJDIR)/boot/boot1
BOOT_BINFILES	+= $(OBJDIR)/boot/loader

# Sub-makefiles for the bootloader
include $(BOOT_DIR)/lib/Makefile.inc
include $(BOOT_DIR)/boot0/Makefile.inc
include $(BOOT_DIR)/boot1/Makefile.inc
include $(BOOT_DIR)/loader/Makefile.inc

# Top-level target to build the bootloader
boot: $(BOOT_BINFILES)
	@echo All targets of boot loader are done.

# Target to install the bootloader on a disk image
install_boot: boot mbr sects kern_loader
	@echo bootloader is installed on $(CERTIKOS_IMG).

mbr: $(OBJDIR)/boot/boot0 $(CERTIKOS_IMG)
	@echo + write boot0
	$(V)$(DD) if=$(OBJDIR)/boot/boot0 of=$(CERTIKOS_IMG) bs=446 count=1 conv=notrunc

sects: $(OBJDIR)/boot/boot1 $(CERTIKOS_IMG)
	@echo + write boot1
	$(V)$(DD) if=$(OBJDIR)/boot/boot1 of=$(CERTIKOS_IMG) bs=512 count=62 conv=notrunc seek=1

kern_loader: $(OBJDIR)/boot/loader $(CERTIKOS_IMG)
	@echo + copy loader to /boot/loader
	$(V)$(UTILSDIR)/mount.sh
	$(V)sudo mkdir -p /mnt/boot
	$(V)sudo cp -f $(OBJDIR)/boot/loader /mnt/boot/loader
	$(V)$(UTILSDIR)/umount.sh
