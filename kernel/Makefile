#
# Top-level Makefile for certikos64
#

ifndef V
V		:= @
else
V		:=
endif

ARCH		:= i386

COMP_NAME	:= "ccomp"

ifdef USE_GCC
	ENABLE_CCOMP	:= 0
	COMP_NAME		:= "cc"
else
	ENABLE_CCOMP	:= 1
	COMP_NAME		:= "ccomp"
endif



# Cross-compiler toolchain
#
# This Makefile will automatically use a cross-compiler toolchain installed
# as 'pios-*' or 'i386-elf-*', if one exists.  If the host tools ('gcc',
# 'objdump', and so forth) compile for a 32-bit x86 ELF target, that will
# be detected as well.  If you have the right compiler toolchain installed
# using a different name, set GCCPREFIX explicitly in conf/env.mk

# try to infer the correct GCCPREFIX
ifndef GCCPREFIX
GCCPREFIX := $(shell sh misc/gccprefix.sh)
endif

# Directories
TOP		:= .
SRCDIR		:= $(TOP)
OBJDIR		:= $(TOP)/obj
UTILSDIR	:= $(TOP)/misc
TESTDIR		:= $(TOP)/test
OBJDIRS		:=

# Compiler and Linker
CC		:= $(GCCPREFIX)gcc
LD		:= $(GCCPREFIX)ld
CFLAGS		:= -g3 -MD -Wall -Werror -Wno-strict-aliasing -Wno-unused-function -pipe -fno-builtin -nostdinc -fno-stack-protector
LDFLAGS		:= -nostdlib

ifeq ($(ENABLE_CCOMP), 1)

CCOMP		:= ccomp
CCOMP_CFLAGS	:= -finline-asm -fpacked-structs -fno-sse

CLIGHTGEN	:= clightgen
CLIGHTGEN_FLAGS	:= -fall

ifeq ($(V),)
CCOMP_CFLAGS	+= -v
endif

else
# Uncomment following two lines when you suspect differences between gcc and
# compcert cause problems.

CCOMP		:= $(GCCPREFIX)gcc
CCOMP_CFLAGS	:= -MD -Wall -Werror -Wno-strict-aliasing -Wno-unused-function -pipe -fno-builtin -nostdinc -fno-stack-protector -O2 -g -m32 -D__COMPCERT__
endif

# other tools
PERL		:= perl
OBJDUMP		:= $(GCCPREFIX)objdump
OBJCOPY		:= $(GCCPREFIX)objcopy
DD		:= $(GCCPREFIX)dd
NM		:= $(GCCPREFIX)nm
CSCOPE		:= cscope

# others
GCC_LIB32 := $(shell $(CC) $(CFLAGS) -m32 -print-libgcc-file-name)
ifeq ($(ARCH), amd64)
GCC_LIB64 := $(shell $(CC) $(CFLAGS) -m64 -print-libgcc-file-name)
endif

# If this is the first time building CertiKOS64, please follow the instructions
# in HOW_TO_MAKE_DISK_IMAGE to create a disk image file manually and put it in
# directory $(OBJDIR)/ (default: obj/)
CERTIKOS_IMG	:= certikos.img

# bochs
BOCHS		:= bochs
BOCHS_OPT	:= -q

# qemu
QEMU		:= qemu-system-x86_64
QEMUOPTS	:= -smp 1 -hda $(CERTIKOS_IMG) -serial mon:stdio -m 2048 -k en-us
QEMUOPTS_KVM	:= -cpu host -enable-kvm
QEMUOPTS_BIOS	:= -L $(UTILSDIR)/qemu/

# Targets

.PHONY: all boot dev kern lib sys user deps


all: pce boot sys user
	@echo "Use compcert: $(ENABLE_CCOMP)"
	@echo "compiler: ${CCOMP}"
	@echo "All targets are done."

pce:
	@echo "Kernel compiler: [${CCOMP}] ${CCOMP_CFLAGS}"
	@echo "User compiler: [${CC}] ${CFLAGS}"
	@echo "Linker: [${LD}] ${LDFLAGS}"

install_img: install_boot install_sys install_user
	@echo "CertiKOS is installed on the disk image."

bochs: $(CERTIKOS_IMG) .bochsrc
	@echo + start bochs
	$(V)$(BOCHS) $(BOCHS_OPT)

qemu: $(CERTIKOS_IMG)
	$(V)$(QEMU) $(QEMUOPTS)

qemu-kvm: $(CERTIKOS_IMG)
	$(V)$(QEMU) $(QEMUOPTS) $(QEMUOPTS_KVM)

qemu-bios: $(CERTIKOS_IMG)
	$(V)$(QEMU) $(QEMUOPTS) $(QEMUOPTS_BIOS)

iso: all
	$(V)cp $(OBJDIR)/sys/kernel $(UTILSDIR)/iso/boot/kernel
	$(V)grub-mkrescue -o $(CERTIKOS_IMG) $(UTILSDIR)/iso

package:
	$(V)tar czf ../certikos.tar.gz --exclude=obj --exclude=cscope.* .

cscope:
	$(V)rm -rf cscope.*
	$(V)find . -name "*.[chsS]" > cscope.files
	$(V)cscope -bkq -i cscope.files

# Sub-makefiles
include boot/Makefile.inc
include user/Makefile.inc
include sys/Makefile.inc

deps: $(OBJDIR)/.deps

$(OBJDIR)/.deps: $(foreach dir, $(OBJDIRS), $(wildcard $(dir)/*.d))
	$(V)mkdir -p $(@D)
	$(V)$(PERL) $(UTILSDIR)/mergedep.pl $@ $^

-include $(OBJDIR)/.deps

clean:
	$(V)rm -rf $(OBJDIR)
	$(V)find . -name "*.[v]" -delete

