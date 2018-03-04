# -*-Makefile-*-

OBJDIRS		+= $(VDEV_OBJDIR)/i8259

USER_VDEV_SRC	+= $(VDEV_SRCDIR)/i8259/pic.c

$(VDEV_OBJDIR)/i8259/%.o: $(VDEV_SRCDIR)/i8259/%.c
	@echo + cc[VDEV/i8259] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<

$(VDEV_OBJDIR)/i8259/%.o: $(VDEV_SRCDIR)/i8259/%.S
	@echo + as[VDEV/i8259] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<
