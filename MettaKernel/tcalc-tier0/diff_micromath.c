/* Differential test: Micromath's own C kernel against Micromath as a theory over the
   tcalc tier-0 kernel. Every operation runs on both; verdicts and the destination
   theorem must agree after every call. Workloads follow boolean_controls.c, plus
   wrong-premise calls in the exhaustive sweep and a random fuzz over a small symbol set. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "kernel.h"
#include "micromath_tcalc.h"
#include "micromath_tcalc_gen.h"

static uint64_t ops, agree_acc, agree_ref;

static void fail(const char *what, uint64_t slot) {
  const ThmBody *a = get_thm(slot); MmBody b = mm_get(slot), c = mm_gen_get(slot);
  fprintf(stderr, "DIVERGENCE at op %" PRIu64 " (%s), slot %" PRIu64 ": micromath {%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64
          "} tcalc {%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 "} gen {%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 "}\n",
          ops, what, slot, a->out, a->f, a->x, a->y, b.out, b.f, b.x, b.y, c.out, c.f, c.x, c.y);
  exit(1);
}
static void same_slot(uint64_t s, const char *what) {
  const ThmBody *a = get_thm(s); MmBody b = mm_get(s), c = mm_gen_get(s);
  if (a->out != b.out || a->f != b.f || a->x != b.x || a->y != b.y ||
      a->out != c.out || a->f != c.f || a->x != c.x || a->y != c.y) fail(what, s);
}
static void verdict(bool a, bool b, bool c, uint64_t dest, const char *what) {
  ++ops;
  if (a != b || a != c) fail(what, dest);
  if (a) ++agree_acc; else ++agree_ref;
  same_slot(dest, what);
}
#define BOTH(what, dest, mcall, tcall, gcall) verdict((mcall), (tcall), (gcall), (dest), (what))
#define SUB1(what, d, m, u, v, x) do { bool aok = false; bool tr = mm_sub1_verify((m), (u), (v), (x), (d), &aok); if (!aok) fail(what " (arena-gen)", (d)); BOTH((what), (d), rule_substitute1((m), (u), (v), (x), (d)), tr, mm_gen_sub1((m), (u), (v), (x), (d))); } while (0)
#define SUB2(what, d, m, u, v, x) do { bool aok = false; bool tr = mm_sub2_verify((m), (u), (v), (x), (d), &aok); if (!aok) fail(what " (arena-gen)", (d)); BOTH((what), (d), rule_substitute2((m), (u), (v), (x), (d)), tr, mm_gen_sub2((m), (u), (v), (x), (d))); } while (0)

static void set_both(uint64_t s, uint64_t o, uint64_t f, uint64_t x, uint64_t y) {
  BOTH("axiom", s, _set_thm(o, f, x, y, s), mm_set(o, f, x, y, s), mm_gen_set(o, f, x, y, s));
}
static uint64_t opaque_both(void) {
  uint64_t a = new_node_opaque(), b = mm_new_opaque(), c = mm_gen_new_opaque();
  ++ops;
  if (a != b || a != c) { fprintf(stderr, "DIVERGENCE opaque %" PRIu64 " vs %" PRIu64 " vs %" PRIu64 "\n", a, b, c); exit(1); }
  return a;
}
static unsigned bit(unsigned t, unsigned l, unsigned r) { return (t >> (2 * l + r)) & 1u; }
static unsigned superpose(unsigned o, unsigned l, unsigned r) {
  unsigned res = 0;
  for (unsigned a = 0; a < 2; a++) for (unsigned b = 0; b < 2; b++) res |= bit(o, bit(l, a, b), bit(r, a, b)) << (2 * a + b);
  return res;
}
static uint64_t named(unsigned m) { return m + 2; }

static void fixture(unsigned t, unsigned u, unsigned v, unsigned a, unsigned b) {
  unsigned x = superpose(t, u, v), ua = superpose(u, a, b), va = superpose(v, a, b), xa = superpose(x, a, b);
  set_both(0, named(x), named(t), named(u), named(v));
  set_both(1, named(ua), named(u), named(a), named(b));
  set_both(2, named(va), named(v), named(a), named(b));
  set_both(3, named(xa), named(x), named(a), named(b));
  set_both(4, named(xa), named(t), named(ua), named(va));
}

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }
static uint64_t rng = 0x243F6A8885A308D3u;
static uint64_t rnd(uint64_t m) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng % m; }

int main(void) {
  if (!init() || !mm_init() || !mm_gen_init()) { fprintf(stderr, "init failed\n"); return 1; }
  for (int i = 0; i < 16; i++) opaque_both();                   /* names 2..17: the 16 Boolean functions */

  for (uint64_t x = 0; x < 18; x++) {                           /* basic rules */
    for (uint64_t y = 0; y < 18; y++) {
      BOTH("proj1", 10, rule_proj1(x, y, 10), mm_proj1(x, y, 10), mm_gen_proj1(x, y, 10));
      BOTH("proj2", 11, rule_proj2(x, y, 11), mm_proj2(x, y, 11), mm_gen_proj2(x, y, 11));
    }
    BOTH("refl", 12, rule_refl(x, 12), mm_refl(x, 12), mm_gen_refl(x, 12));
  }
  uint64_t future = get_last_const() + 100;                     /* names not yet allocated */
  BOTH("proj1 future", 23, rule_proj1(future, UINT64_MAX, 23), mm_proj1(future, UINT64_MAX, 23), mm_gen_proj1(future, UINT64_MAX, 23));
  BOTH("proj2 future", 24, rule_proj2(UINT64_MAX, future, 24), mm_proj2(UINT64_MAX, future, 24), mm_gen_proj2(UINT64_MAX, future, 24));
  BOTH("refl future", 25, rule_refl(UINT64_MAX, 25), mm_refl(UINT64_MAX, 25), mm_gen_refl(UINT64_MAX, 25));

  for (unsigned t = 0; t < 16; t++)                             /* exhaustive Boolean sweep */
    for (unsigned u = 0; u < 16; u++)
      for (unsigned v = 0; v < 16; v++)
        for (unsigned a = 0; a < 16; a++)
          for (unsigned b = 0; b < 16; b++) {
            fixture(t, u, v, a, b);
            SUB1("sub1", 5, 0, 1, 2, 3);
            SUB2("sub2", 6, 0, 1, 2, 4);
            SUB1("sub1 wrong", 7, 0, 1, 2, 4);
            SUB2("sub2 wrong", 7, 0, 1, 2, 3);
            SUB1("sub1 swapped", 7, 0, 2, 1, 3);
          }

  uint64_t s[10];                                               /* single-guard mutations */
  for (int i = 0; i < 10; i++) s[i] = opaque_both();
  for (unsigned rule = 0; rule < 2; rule++)
    for (unsigned g = 0; g < 7; g++) {
      uint64_t rows[4][4] = { { s[3], s[0], s[1], s[2] }, { s[6], s[1], s[4], s[5] }, { s[7], s[2], s[4], s[5] },
                              { s[8], rule ? s[0] : s[3], rule ? s[6] : s[4], rule ? s[7] : s[5] } };
      static const int row[7] = { 1, 2, 2, 2, 3, 3, 3 }, col[7] = { 1, 1, 2, 3, 1, 2, 3 };
      rows[row[g]][col[g]] = s[9];
      for (int i = 0; i < 4; i++) set_both(i, rows[i][0], rows[i][1], rows[i][2], rows[i][3]);
      if (rule) SUB2("sub2 mutated", 8, 0, 1, 2, 3);
      else      SUB1("sub1 mutated", 8, 0, 1, 2, 3);
    }

  SUB1("sub1 dummies", 20, UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX);
  SUB2("sub2 dummies", 21, UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX);
  fixture(1, 6, 8, 3, 5);
  SUB1("sub1 dummy main", 22, UINT64_MAX, 1, 2, 3);

  {                                                             /* definitions */
    uint64_t a = new_node_def(named(8), named(6), named(14), 30), b = mm_new_def(named(8), named(6), named(14), 30), e = mm_gen_new_def(named(8), named(6), named(14), 30);
    ++ops; if (a != b || a != e || !a) { fprintf(stderr, "DIVERGENCE def %" PRIu64 " vs %" PRIu64 " vs %" PRIu64 "\n", a, b, e); return 1; }
    same_slot(30, "def");
    for (int p = 0; p < 3; p++) {
      uint64_t v[3] = { named(8), named(6), named(14) };
      v[p] = get_last_const() + 1;                              /* an operand that is not yet allocated */
      uint64_t c = new_node_def(v[0], v[1], v[2], 30), d = mm_new_def(v[0], v[1], v[2], 30), f = mm_gen_new_def(v[0], v[1], v[2], 30);
      ++ops; if (c != d || c != f || c) { fprintf(stderr, "DIVERGENCE def bound\n"); return 1; }
      same_slot(30, "def bound");
    }
  }

  for (uint64_t i = 0; i < 20000000; i++) {                     /* random fuzz over symbols 0..3 */
    uint64_t d = rnd(16), k = rnd(100), q[4] = { rnd(18), rnd(18), rnd(18), rnd(18) };
    if (k < 30) { uint64_t r0 = rnd(4), r1 = rnd(4), r2 = rnd(4), r3 = rnd(4); set_both(d, r0, r1, r2, r3); }
    else if (k < 62) SUB1("fuzz sub1", d, q[0], q[1], q[2], q[3]);
    else if (k < 94) SUB2("fuzz sub2", d, q[0], q[1], q[2], q[3]);
    else if (k < 96) { uint64_t x = rnd(4), y = rnd(4); BOTH("fuzz proj1", d, rule_proj1(x, y, d), mm_proj1(x, y, d), mm_gen_proj1(x, y, d)); }
    else if (k < 98) { uint64_t x = rnd(4), y = rnd(4); BOTH("fuzz proj2", d, rule_proj2(x, y, d), mm_proj2(x, y, d), mm_gen_proj2(x, y, d)); }
    else { uint64_t x = rnd(4); BOTH("fuzz refl", d, rule_refl(x, d), mm_refl(x, d), mm_gen_refl(x, d)); }
  }
  printf("differential: %" PRIu64 " operations, verdicts and theorems identical across micromath, tcalc-runtime, tcalc-arena-gen, and tcalc-schema-gen (%" PRIu64 " accepted, %" PRIu64 " refused)\n",
         ops, agree_acc, agree_ref);

  /* Cost, each kernel alone: (a) the exhaustive sweep, five axioms and two substitutions per
     fixture; (b) one valid substitution repeated, premises already in place. */
  double t0, tm, tt, ta, tg; volatile bool sink = 0; const uint64_t REP = 20000000;
  t0 = now();
  for (unsigned t = 0; t < 16; t++) for (unsigned u = 0; u < 16; u++) for (unsigned v = 0; v < 16; v++)
    for (unsigned a = 0; a < 16; a++) for (unsigned b = 0; b < 16; b++) {
      unsigned x = superpose(t, u, v), ua = superpose(u, a, b), va = superpose(v, a, b), xa = superpose(x, a, b);
      _set_thm(named(x), named(t), named(u), named(v), 0); _set_thm(named(ua), named(u), named(a), named(b), 1);
      _set_thm(named(va), named(v), named(a), named(b), 2); _set_thm(named(xa), named(x), named(a), named(b), 3);
      _set_thm(named(xa), named(t), named(ua), named(va), 4);
      sink ^= rule_substitute1(0, 1, 2, 3, 5); sink ^= rule_substitute2(0, 1, 2, 4, 6);
    }
  tm = now() - t0; t0 = now();
  for (unsigned t = 0; t < 16; t++) for (unsigned u = 0; u < 16; u++) for (unsigned v = 0; v < 16; v++)
    for (unsigned a = 0; a < 16; a++) for (unsigned b = 0; b < 16; b++) {
      unsigned x = superpose(t, u, v), ua = superpose(u, a, b), va = superpose(v, a, b), xa = superpose(x, a, b);
      mm_set(named(x), named(t), named(u), named(v), 0); mm_set(named(ua), named(u), named(a), named(b), 1);
      mm_set(named(va), named(v), named(a), named(b), 2); mm_set(named(xa), named(x), named(a), named(b), 3);
      mm_set(named(xa), named(t), named(ua), named(va), 4);
      sink ^= mm_sub1(0, 1, 2, 3, 5); sink ^= mm_sub2(0, 1, 2, 4, 6);
    }
  tt = now() - t0; t0 = now();
  for (unsigned t = 0; t < 16; t++) for (unsigned u = 0; u < 16; u++) for (unsigned v = 0; v < 16; v++)
    for (unsigned a = 0; a < 16; a++) for (unsigned b = 0; b < 16; b++) {
      unsigned x = superpose(t, u, v), ua = superpose(u, a, b), va = superpose(v, a, b), xa = superpose(x, a, b);
      mm_set(named(x), named(t), named(u), named(v), 0); mm_set(named(ua), named(u), named(a), named(b), 1);
      mm_set(named(va), named(v), named(a), named(b), 2); mm_set(named(xa), named(x), named(a), named(b), 3);
      mm_set(named(xa), named(t), named(ua), named(va), 4);
      sink ^= mm_sub1_arena(0, 1, 2, 3, 5); sink ^= mm_sub2_arena(0, 1, 2, 4, 6);
    }
  ta = now() - t0; t0 = now();
  for (unsigned t = 0; t < 16; t++) for (unsigned u = 0; u < 16; u++) for (unsigned v = 0; v < 16; v++)
    for (unsigned a = 0; a < 16; a++) for (unsigned b = 0; b < 16; b++) {
      unsigned x = superpose(t, u, v), ua = superpose(u, a, b), va = superpose(v, a, b), xa = superpose(x, a, b);
      mm_gen_set(named(x), named(t), named(u), named(v), 0); mm_gen_set(named(ua), named(u), named(a), named(b), 1);
      mm_gen_set(named(va), named(v), named(a), named(b), 2); mm_gen_set(named(xa), named(x), named(a), named(b), 3);
      mm_gen_set(named(xa), named(t), named(ua), named(va), 4);
      sink ^= mm_gen_sub1(0, 1, 2, 3, 5); sink ^= mm_gen_sub2(0, 1, 2, 4, 6);
    }
  tg = now() - t0;
  printf("cost (a) sweep, 1048576 fixtures: micromath %.3f s | tcalc-runtime %.3f s (%.1fx) | tcalc-arena-gen %.3f s (%.1fx) | tcalc-schema-gen %.3f s (%.2fx)\n",
         tm, tt, tt / tm, ta, ta / tm, tg, tg / tm);
  fixture(1, 6, 8, 3, 5);
  t0 = now(); for (uint64_t i = 0; i < REP; i++) sink ^= rule_substitute1(0, 1, 2, 3, 5); tm = now() - t0;
  t0 = now(); for (uint64_t i = 0; i < REP; i++) sink ^= mm_sub1(0, 1, 2, 3, 5); tt = now() - t0;
  t0 = now(); for (uint64_t i = 0; i < REP; i++) sink ^= mm_sub1_arena(0, 1, 2, 3, 5); ta = now() - t0;
  t0 = now(); for (uint64_t i = 0; i < REP; i++) sink ^= mm_gen_sub1(0, 1, 2, 3, 5); tg = now() - t0;
  printf("cost (b) substitute1: micromath %.1f ns | tcalc-runtime %.1f ns (%.1fx) | tcalc-arena-gen %.1f ns (%.1fx) | tcalc-schema-gen %.1f ns (%.2fx)\n",
         tm / REP * 1e9, tt / REP * 1e9, tt / tm, ta / REP * 1e9, ta / tm, tg / REP * 1e9, tg / tm);
  return 0;
}
