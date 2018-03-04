# -*-Makefile-*-

OBJDIRS		+= $(USER_OBJDIR)/vmm/vmx

USER_VMM_SRC	+= $(USER_DIR)/vmm/vmx/vmx.c

$(USER_OBJDIR)/vmm/vmx/%.o: $(USER_DIR)/vmm/vmx/%.c
	@echo + cc[USER/vmm] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<

$(USER_OBJDIR)/vmm/vmx/%.o: $(USER_DIR)/vmm/vmx/%.S
	@echo + as[USER/vmm] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<
