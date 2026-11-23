#pragma once
/* Micromath as a theory over the tcalc tier-0 kernel, with the slot interface of
   Micromath's own C kernel so that both can be driven by one script. */
#include <stdbool.h>
#include <stdint.h>

typedef struct { uint64_t out, f, x, y; } MmBody;

bool     mm_init(void);
uint64_t mm_new_opaque(void);                              /* 0 on failure */
uint64_t mm_new_def(uint64_t f, uint64_t x, uint64_t y, uint64_t slot);
bool     mm_set(uint64_t out, uint64_t f, uint64_t x, uint64_t y, uint64_t slot);  /* trusted */
MmBody   mm_get(uint64_t slot);
bool     mm_proj1(uint64_t x, uint64_t y, uint64_t slot);
bool     mm_proj2(uint64_t x, uint64_t y, uint64_t slot);
bool     mm_refl(uint64_t a, uint64_t slot);
bool     mm_sub1(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t dest);
bool     mm_sub2(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t dest);
bool     mm_sub1_arena(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t dest);
bool     mm_sub2_arena(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t dest);
bool     mm_sub1_verify(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t dest, bool *arena_ok);
bool     mm_sub2_verify(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t dest, bool *arena_ok);
