# -*-Makefile-*-

OBJDIRS		+= $(VDEV_OBJDIR)/nvram

USER_VDEV_SRC	+= $(VDEV_SRCDIR)/nvram/nvram.c

$(VDEV_OBJDIR)/nvram/%.o: $(VDEV_SRCDIR)/nvram/%.c
	@echo + cc[VDEV/nvram] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<

$(VDEV_OBJDIR)/nvram/%.o: $(VDEV_SRCDIR)/nvram/%.S
	@echo + as[VDEV/nvram] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<
