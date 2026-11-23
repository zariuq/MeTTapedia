/* Hooks that tcalc-tier0's lockstep harness expects from its tcalc participant.
   There they also check tcalc's arena specializer against tcalc's own firing. The
   compiled unit has no arena, so here each hook fires the compiled rule: the arena
   check passes trivially, and the harness's "tcalc-runtime" and "tcalc-arena-gen"
   columns both measure the compiled unit. */
#include "micromath_tcalc.h"

bool mm_sub1_arena(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d) { return mm_sub1(m, u, v, x, d); }
bool mm_sub2_arena(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d) { return mm_sub2(m, u, v, x, d); }

bool mm_sub1_verify(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d, bool *arena_ok) {
  *arena_ok = true;
  return mm_sub1(m, u, v, x, d);
}

bool mm_sub2_verify(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d, bool *arena_ok) {
  *arena_ok = true;
  return mm_sub2(m, u, v, x, d);
}
