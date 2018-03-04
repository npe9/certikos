# -*-Makefile-*-

OBJDIRS		+= $(VDEV_OBJDIR)/serial

USER_VDEV_SRC	+= $(VDEV_SRCDIR)/serial/serial.c

$(VDEV_OBJDIR)/serial/%.o: $(VDEV_SRCDIR)/serial/%.c
	@echo + cc[VDEV/serial] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<

$(VDEV_OBJDIR)/serial/%.o: $(VDEV_SRCDIR)/serial/%.S
	@echo + as[VDEV/serial] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<
