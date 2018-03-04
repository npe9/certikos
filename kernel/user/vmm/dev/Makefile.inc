# -*-Makefile-*-

OBJDIRS		+= $(USER_OBJDIR)/vmm/dev

VDEV_SRCDIR	:= $(USER_DIR)/vmm/dev
VDEV_OBJDIR	:= $(USER_OBJDIR)/vmm/dev

USER_VDEV_SRC	:=

include $(VDEV_SRCDIR)/i8042/Makefile.inc
include $(VDEV_SRCDIR)/i8254/Makefile.inc
include $(VDEV_SRCDIR)/nvram/Makefile.inc
include $(VDEV_SRCDIR)/virtio/Makefile.inc
include $(VDEV_SRCDIR)/i8259/Makefile.inc
include $(VDEV_SRCDIR)/serial/Makefile.inc

USER_VMM_SRC	+= $(USER_VDEV_SRC)
