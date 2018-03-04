# -*-Makefile-*-

OBJDIRS		+= $(USER_OBJDIR)/vmm/svm

USER_VMM_SRC	+= $(USER_DIR)/vmm/svm/svm.c

$(USER_OBJDIR)/vmm/svm/%.o: $(USER_DIR)/vmm/svm/%.c
	@echo + cc[USER/vmm] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<

$(USER_OBJDIR)/vmm/svm/%.o: $(USER_DIR)/vmm/svm/%.S
	@echo + as[USER/vmm] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<
