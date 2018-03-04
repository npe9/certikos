# -*-Makefile-*-

USER_DIR	:= user
USER_OBJDIR	:= $(OBJDIR)/user

OBJDIRS		+= $(USER_OBJDIR)

include $(USER_DIR)/config.mk

USER_CFLAGS	+= $(CFLAGS) -m32 -D_USER_ -g3 -I$(USER_DIR)/include -I$(KERN_DIR)
USER_LDFLAGS	:= $(LDFLAGS) -m elf_i386 -Ttext=0x40000000 -e _start

include $(USER_DIR)/lib/Makefile.inc
include $(USER_DIR)/idle/Makefile.inc
include $(USER_DIR)/vmm/Makefile.inc
include $(USER_DIR)/pingpong/Makefile.inc
include $(USER_DIR)/profile/Makefile.inc

user: lib idle vmm pingpong profile
	@echo All targets of user are done.

install_user:
