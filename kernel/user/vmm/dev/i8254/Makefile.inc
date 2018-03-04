# -*-Makefile-*-

OBJDIRS		+= $(VDEV_OBJDIR)/i8254

USER_VDEV_SRC	+= $(VDEV_SRCDIR)/i8254/pit.c

$(VDEV_OBJDIR)/i8254/%.o: $(VDEV_SRCDIR)/i8254/%.c
	@echo + cc[VDEV/i8254] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<

$(VDEV_OBJDIR)/i8254/%.o: $(VDEV_SRCDIR)/i8254/%.S
	@echo + as[VDEV/i8254] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<
