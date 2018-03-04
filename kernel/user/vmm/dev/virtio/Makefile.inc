# -*-Makefile-*-

OBJDIRS		+= $(VDEV_OBJDIR)/virtio

USER_VDEV_SRC	+= $(VDEV_SRCDIR)/virtio/virtio.c
USER_VDEV_SRC	+= $(VDEV_SRCDIR)/virtio/virtio_blk.c
USER_VDEV_SRC	+= $(VDEV_SRCDIR)/virtio/pci.c

$(VDEV_OBJDIR)/virtio/%.o: $(VDEV_SRCDIR)/virtio/%.c
	@echo + cc[VDEV/virtio] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<

$(VDEV_OBJDIR)/virtio/%.o: $(VDEV_SRCDIR)/virtio/%.S
	@echo + as[VDEV/virtio] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<
