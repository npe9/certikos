# -*-Makefile-*-

OBJDIRS		+= $(VDEV_OBJDIR)/i8042

USER_VDEV_SRC	+= $(VDEV_SRCDIR)/i8042/kbd.c
USER_VDEV_SRC	+= $(VDEV_SRCDIR)/i8042/ps2.c

$(VDEV_OBJDIR)/i8042/%.o: $(VDEV_SRCDIR)/i8042/%.c
	@echo + cc[VDEV/i8042] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<

$(VDEV_OBJDIR)/i8042/%.o: $(VDEV_SRCDIR)/i8042/%.S
	@echo + as[VDEV/i8042] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<
