# -*-Makefile-*-

OBJDIRS		+= $(USER_OBJDIR)/vmm

USER_VMM_SRC	+= $(USER_DIR)/vmm/vmm.c
USER_VMM_SRC	+= $(USER_DIR)/vmm/vmm_dev.c
USER_VMM_SRC	+= $(USER_DIR)/vmm/main.c

include $(USER_DIR)/vmm/dev/Makefile.inc
include $(USER_DIR)/vmm/svm/Makefile.inc
include $(USER_DIR)/vmm/vmx/Makefile.inc

USER_VMM_OBJ	:= $(patsubst %.c, $(OBJDIR)/%.o, $(USER_VMM_SRC))
USER_VMM_OBJ	:= $(patsubst %.S, $(OBJDIR)/%.o, $(USER_VMM_OBJ))

USER_VMM_BINFILES := $(UTILSDIR)/bios.bin
USER_VMM_BINFILES += $(UTILSDIR)/vgabios.bin

KERN_BINFILES	+= $(USER_OBJDIR)/vmm/vmm

vmm: $(USER_OBJDIR)/vmm/vmm

$(USER_OBJDIR)/vmm/vmm: $(USER_LIB_OBJ) $(USER_VMM_OBJ) $(USER_VMM_BINFILES)
	@echo + ld[USER/vmm] $@
	$(V)$(LD) -o $@ $(USER_LDFLAGS) $(USER_LIB_OBJ) $(USER_VMM_OBJ) $(GCC_LIBS) -b binary $(USER_VMM_BINFILES)
	$(V)$(OBJDUMP) -S $@ > $@.asm
	$(V)$(NM) -n $@ > $@.sym

$(USER_OBJDIR)/vmm/%.o: $(USER_DIR)/vmm/%.c
	@echo + cc[USER/vmm] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<

$(USER_OBJDIR)/vmm/%.o: $(USER_DIR)/vmm/%.S
	@echo + as[USER/vmm] $<
	@mkdir -p $(@D)
	$(V)$(CC) $(USER_CFLAGS) -c -o $@ $<
