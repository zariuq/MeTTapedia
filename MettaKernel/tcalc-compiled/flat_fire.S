/* Reference x86-64 implementation of generic flat-rule firing.
   SysV arguments 7 and 8 (dest, scratch) arrive on the stack.
   No allocation, calls, globals, or optimized instruction selection. */
    .text
    .globl flat_fire
    .type flat_fire,@function
flat_fire:
    endbr64
    push %rbp
    push %rbx
    push %r12
    push %r13
    push %r14
    push %r15
    mov 56(%rsp), %r12
    mov 64(%rsp), %r13

    xor %r10d, %r10d
    xor %r11d, %r11d
    test %rcx, %rcx
    jz .Lguards_done
.Lguard_loop:
    mov (%rdx,%r10,4), %eax
    mov %eax, %ebx
    and $255, %ebx
    mov %eax, %ebp
    shr $8, %ebp
    and $255, %ebp
    mov %eax, %r14d
    shr $16, %r14d
    and $255, %r14d
    shr $24, %eax
    mov (%rsi,%rbx,4), %r15d
    add %ebp, %r15d
    mov (%rsi,%r14,4), %ebx
    add %eax, %ebx
    mov (%rdi,%r15,4), %eax
    mov $1, %ebp
    cmp (%rdi,%rbx,4), %eax
    cmovne %ebp, %r11d
    inc %r10
    cmp %rcx, %r10
    jne .Lguard_loop
.Lguards_done:
    test %r11d, %r11d
    jnz .Lrefuse

    xor %r10d, %r10d
    test %r9, %r9
    jz .Ldest_setup
.Lmake_loop:
    mov (%r8,%r10,4), %eax
    mov %eax, %ebx
    and $255, %ebx
    shr $8, %eax
    and $255, %eax
    mov (%rsi,%rbx,4), %ebp
    add %eax, %ebp
    mov (%rdi,%rbp,4), %eax
    mov %eax, (%r13,%r10,4)
    inc %r10
    cmp %r9, %r10
    jne .Lmake_loop

.Ldest_setup:
    xor %r10d, %r10d
    test %r9, %r9
    jz .Laccept
.Ldest_loop:
    mov (%r13,%r10,4), %eax
    mov %eax, (%r12,%r10,4)
    inc %r10
    cmp %r9, %r10
    jne .Ldest_loop
.Laccept:
    mov $1, %eax
    jmp .Lreturn
.Lrefuse:
    xor %eax, %eax
.Lreturn:
    pop %r15
    pop %r14
    pop %r13
    pop %r12
    pop %rbx
    pop %rbp
    ret
    .size flat_fire, .-flat_fire
    .section .note.GNU-stack,"",@progbits
