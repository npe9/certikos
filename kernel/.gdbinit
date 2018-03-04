target remote localhost:8832
symbol-file obj/sys/kernel
add-symbol-file obj/user/vmm/vmm 0x40000000

layout asm
winheight asm 50

layout reg
winheight reg 8

focus cmd

break main
continue
