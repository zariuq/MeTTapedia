/* Export the exact relocation-free bytes checked by the linked-image proof. */
.section .text
.p2align 4
.global flat_fire
.type flat_fire,@function
flat_fire:
.incbin "ordinary_flat_linked.text", 0, 224
.size flat_fire, 211

.global ordinary_flat_adapter
.type ordinary_flat_adapter,@function
ordinary_flat_adapter:
.incbin "ordinary_flat_linked.text", 224
.size ordinary_flat_adapter, .-ordinary_flat_adapter
.section .note.GNU-stack,"",@progbits
