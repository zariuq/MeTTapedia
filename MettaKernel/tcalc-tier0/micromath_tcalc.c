#include "micromath_tcalc.h"
#include "tcalc.h"
#include <stdlib.h>

/* Micromath as a theory: a theorem (eq out f x y) says out(a,b) = f(x(a,b), y(a,b)),
   with names 0 and 1 the projections. Six rules; the seven symbol equalities of each
   substitution rule are repeated holes. Slots map Micromath's theorem indices to
   occurrences; an unset slot reads as (eq 0 0 0 0), which proj1 derives. */
static int SYM, EQ, r_proj1, r_proj2, r_refl, r_sub1, r_sub2, r_def;
TcTheory tc_theory;
#define MAX_SLOT (1u << 24)

static Term eq4(Term o, Term f, Term x, Term y) { Term a[4] = { o, f, x, y }; return tc_app(EQ, a); }
static Term nm(uint64_t s) { return tc_name((uint16_t)SYM, s); }
static Occ at(uint64_t s) { return s < MAX_SLOT ? (Occ)(s + 3) : 0; }
static int rule(int nkeep, const Term *keep, Term make, int fresh) {
  Rule r = { .nkeep = (uint8_t)nkeep, .make = { make, 0 }, .fresh = (int8_t)fresh };
  for (int i = 0; i < nkeep; i++) r.keep[i] = (Pat){ keep[i], 0 };
  return tc_rule(&r);
}

bool mm_init(void) {
  if (!tc_init(1u << 15, 1u << 12)) return false;
  SYM = tc_sort(0); int PROP = tc_sort(SORT_PROVABLE);
  Binder s4[4] = { { (uint16_t)SYM, 0, 0 }, { (uint16_t)SYM, 0, 0 }, { (uint16_t)SYM, 0, 0 }, { (uint16_t)SYM, 0, 0 } };
  EQ = tc_con((uint16_t)PROP, 0, 4, s4);
  Binder v[9]; for (int i = 0; i < 9; i++) v[i] = (Binder){ (uint16_t)SYM, 0, 0 };
  tc_fresh_name(); tc_fresh_name();                       /* X = 0, Y = 1 */
  if (EQ < 0 || !tc_ctx(9, v)) return false;
  Term X = nm(0), Y = nm(1);
  Term t = tc_v(0), u = tc_v(1), w = tc_v(2), x = tc_v(3), a = tc_v(4), b = tc_v(5), u1 = tc_v(6), w1 = tc_v(7), x1 = tc_v(8);
  r_proj1 = rule(0, NULL, eq4(x, X, x, a), -1);  /* x = X(x,a) */
  r_proj2 = rule(0, NULL, eq4(a, Y, x, a), -1);  /* a = Y(x,a) */
  r_refl  = rule(0, NULL, eq4(a, a, X, Y), -1);  /* a = a(X,Y) */
  Term s1[4] = { eq4(x, t, u, w), eq4(u1, u, a, b), eq4(w1, w, a, b), eq4(x1, x, a, b) };
  r_sub1  = rule(4, s1, eq4(x1, t, u1, w1), -1);
  Term s2[4] = { eq4(x, t, u, w), eq4(u1, u, a, b), eq4(w1, w, a, b), eq4(x1, t, u1, w1) };
  r_sub2  = rule(4, s2, eq4(x1, x, a, b), -1);
  r_def   = rule(0, NULL, eq4(x1, t, u, w), 8);  /* fresh x1 := t(u,w) */
  tc_theory = (TcTheory){
    .prefix = "mm", .header = "micromath_tcalc.h", .body_type = "MmBody", .max_slot = MAX_SLOT,
    .nentries = 6,
    .entries = {
      { "proj1",   TC_ENT_INPUTS, r_proj1, 2, { 3, 4 } },
      { "proj2",   TC_ENT_INPUTS, r_proj2, 2, { 3, 4 } },
      { "refl",    TC_ENT_INPUTS, r_refl,  1, { 4 } },
      { "sub1",    TC_ENT_KEEPS,  r_sub1,  0, { 0 } },
      { "sub2",    TC_ENT_KEEPS,  r_sub2,  0, { 0 } },
      { "new_def", TC_ENT_FRESH,  r_def,   3, { 0, 1, 2 } },
    },
    .unset_rule = r_proj1, .unset_nbinds = 2, .unset_hole = { 3, 4 }, .unset_val = { 0, 0 },
  };
  Term in[9] = { 0 };
  for (int i = 0; i < tc_theory.unset_nbinds; i++) in[tc_theory.unset_hole[i]] = nm(tc_theory.unset_val[i]);
  Occ dummy = tc_fire(tc_theory.unset_rule, NULL, NULL, in);
  tc_unset(dummy);
  tc_seal();
  return dummy && r_proj1 >= 0 && r_proj2 >= 0 && r_refl >= 0 && r_sub1 >= 0 && r_sub2 >= 0 && r_def >= 0;
}

static bool fire(int r, const Occ *p, const Term *in, uint64_t d) { return d < MAX_SLOT && tc_flat_fire(r, p, in, (Occ)(d + 3)) != 0; }
uint64_t mm_new_opaque(void) { uint64_t s = tc_fresh_name(); return s == UINT64_MAX ? 0 : s; }
uint64_t mm_new_def(uint64_t f, uint64_t x, uint64_t y, uint64_t s) {
  Term in[9] = { [0] = nm(f), [1] = nm(x), [2] = nm(y) };
  return fire(r_def, NULL, in, s) ? tc_next_name() - 1 : 0;
}
bool mm_set(uint64_t o, uint64_t f, uint64_t x, uint64_t y, uint64_t s) {
  Term a[4] = { nm(o), nm(f), nm(x), nm(y) };
  return s < MAX_SLOT && tc_flat_put((Occ)(s + 3), 0, EQ, a) != 0;
}
MmBody mm_get(uint64_t s) {
  const Term *a = tc_flat_args(at(s), 1u);
  return (MmBody){ tc_name_id(a[0]), tc_name_id(a[1]), tc_name_id(a[2]), tc_name_id(a[3]) };
}
bool mm_proj1(uint64_t x, uint64_t y, uint64_t s) { Term in[9] = { [3] = nm(x), [4] = nm(y) }; return fire(r_proj1, NULL, in, s); }
bool mm_proj2(uint64_t x, uint64_t y, uint64_t s) { Term in[9] = { [3] = nm(x), [4] = nm(y) }; return fire(r_proj2, NULL, in, s); }
bool mm_refl(uint64_t a, uint64_t s) { Term in[9] = { [4] = nm(a) }; return fire(r_refl, NULL, in, s); }
bool mm_sub1(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d) { Occ p[4] = { at(m), at(u), at(v), at(x) }; return fire(r_sub1, p, NULL, d); }
bool mm_sub2(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d) { Occ p[4] = { at(m), at(u), at(v), at(x) }; return fire(r_sub2, p, NULL, d); }
#ifdef TC_HAVE_GEN
#include "micromath_tcalc_gen.h"
static bool same_flat(Occ o1, Occ o2) {
  if (!o1 || !o2) return o1 == o2;
  const Term *a1 = tc_flat_args(o1, 1u), *a2 = tc_flat_args(o2, 1u);
  return a1 && a2 && a1[0] == a2[0] && a1[1] == a2[1] && a1[2] == a2[2] && a1[3] == a2[3];
}
bool mm_sub1_arena(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d) { Occ p[4] = { at(m), at(u), at(v), at(x) }; return d < MAX_SLOT && tc_fire_arena_3(p, (Occ)(d + 3)) != 0; }
bool mm_sub2_arena(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d) { Occ p[4] = { at(m), at(u), at(v), at(x) }; return d < MAX_SLOT && tc_fire_arena_4(p, (Occ)(d + 3)) != 0; }
bool mm_sub1_verify(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d, bool *arena_ok) {
  Occ p[4] = { at(m), at(u), at(v), at(x) }, o2 = tc_fire_arena_3(p, 1), o1 = tc_flat_fire(r_sub1, p, NULL, d < MAX_SLOT ? (Occ)(d + 3) : 2);
  *arena_ok = same_flat(o1, o2);
  return d < MAX_SLOT && o1 != 0;
}
bool mm_sub2_verify(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d, bool *arena_ok) {
  Occ p[4] = { at(m), at(u), at(v), at(x) }, o2 = tc_fire_arena_4(p, 1), o1 = tc_flat_fire(r_sub2, p, NULL, d < MAX_SLOT ? (Occ)(d + 3) : 2);
  *arena_ok = same_flat(o1, o2);
  return d < MAX_SLOT && o1 != 0;
}
#endif
