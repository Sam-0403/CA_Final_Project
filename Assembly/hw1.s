.data
    n: .word 7
    
.text
.globl __start

FUNCTION:
    # Todo: Define your own function in HW1
    addi a5, x10, 0
func:
    addi sp, sp, -8
    sw   x1, 4(sp)  #
    sw   a5, 0(sp)  #
    addi a1, a5, -1 
    bne  a1, x0, L1
    addi x10, x0, 7
    addi sp, sp, 8
    jalr x0, 0(x1)
L1: srli a5, a5, 1
    jal  x1, func
    lw   a5, 0(sp)
    lw   x1, 4(sp)
    addi sp, sp, 8
    slli x10, x10, 3
    slli t1, a5, 2
    add x10, x10, t1
    jalr x0, 0(x1)

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall