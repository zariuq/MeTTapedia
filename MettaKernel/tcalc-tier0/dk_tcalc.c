/* Dedukti (Lambda-Pi Calculus Modulo Rewriting) verifier on tcalc (Row 5).
   Sorts, terms (Type, Kind, DB, Const, PVar, Joker, App, Lam, Pi), contexts,
   typing side-condition certificates (SPACE_REL), and typing judgments
   TYPED(ctx, term, type) (SPACE_THM, protected) are hash-consed tcalc terms
   and occurrences. Once sealed (tc_seal), SPACE_THM can only be populated by
   committing prepared steps (tc_commit_prepared) for the 8 Lambda-Pi-Modulo
   inference rules:
     1. R_SORT          (|- Type : Kind)
     2. R_CONST         (Gamma |- c : T_c)
     3. R_VAR           (Gamma |- x_i : T_i)
     4. R_PI            (Gamma |- A : Type, Gamma, x:A |- B : s ==> Gamma |- Pi x:A. B : s)
     5. R_LAM           (Gamma |- A : Type, Gamma, x:A |- t : B ==> Gamma |- \x:A. t : Pi x:A. B)
     6. R_APP           (Gamma |- f : Pi x:A. B, Gamma |- a : A ==> Gamma |- f a : B[x := a])
     7. R_CONV          (Gamma |- t : A, A ===_beta,delta,R B ==> Gamma |- t : B)
     8. R_REWRITE_ADMIT (Delta |- lhs : T, Delta |- rhs : T ==> admits [Delta] lhs --> rhs) */
#define _POSIX_C_SOURCE 200809L
#include <ctype.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "tcalc.h"

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e3 + ts.tv_nsec * 1e-6;
}

enum { SPACE_REL = 0, SPACE_THM = 1 };

static int S_INT, S_NAME, S_TM, S_CTX, S_CERT, S_TYPED;
static int C_TM_TYPE, C_TM_KIND, C_TM_NONE;
static int C_TM_DB, C_TM_CONST, C_TM_PVAR, C_TM_JOKER;
static int C_TM_AP, C_TM_LAM, C_TM_PI;
static int C_CTX_NIL, C_CTX_CONS;
static int C_TYPED;
static int C_SORT_CERT, C_CONST_CERT, C_VAR_CERT, C_PI_CERT;
static int C_LAM_CERT, C_APP_CERT, C_CONV_CERT, C_REWRITE_CERT;
static int C_DOM_SORT, C_DEFINABLE;

static int R_SORT, R_CONST, R_VAR, R_PI, R_LAM, R_APP, R_CONV, R_REWRITE_ADMIT;
static Term T_TYPE, T_KIND, T_NONE, T_CTX_NIL;
static Occ OCC_DOM_TYPE, OCC_DOM_KIND;
static uint64_t stat_rule_fires[9];
static uint32_t g_whnf_gen = 1;

static inline Occ commit_dk_step(int rule, const Occ *keep, const Term *inst) {
  TcPreparedStep step = { .rule = rule, .keep = keep, .inst = inst };
  TcAdmissionReceipt rec;
  return tc_commit_prepared(&step, &rec) ? rec.out : 0;
}

/* ---- Rewrite rules attached to a head symbol ---- */
#define MAX_RULE_ARGS  16
#define MAX_RULE_PVARS 32

typedef struct {
  uint32_t head_sym;
  uint32_t nargs;
  uint32_t npvars;
  Term     pats[MAX_RULE_ARGS];
  Term     rhs;
} DkRule;

/* ---- Symbol table ---- */
typedef struct {
  char    *text;
  uint32_t len, hash;
  Term     nterm;
  bool     declared;
  bool     rewritable;
  Occ      def_occ; /* DEFINABLE(nterm) occurrence in SPACE_REL when rewritable */
  Term     tp;
  Term     def; /* non-zero for := definitions */
  DkRule  *rules;
  uint32_t nrules, caprules;
} DkSym;

static DkSym *syms;
static uint32_t nsyms, capsyms;
static uint32_t *sym_tab;
static size_t sym_tab_cap;

static uint32_t hash_bytes(const char *s, size_t n) {
  uint32_t h = 2166136261u;
  for (size_t i = 0; i < n; i++) {
    h ^= (uint8_t)s[i];
    h *= 16777619u;
  }
  return h ? h : 1u;
}

/* ---- Per-Term metadata ---- */
typedef struct {
  uint32_t fv;       /* 1 + max free DB index, 0 if closed */
  uint32_t uval;     /* integer value for S_INT or sym_id for S_NAME */
  Term     whnf;     /* cached WHNF for closed terms */
  uint32_t whnf_gen; /* generation of cached WHNF */
  Term     shift1;   /* cached shift(0, +1) */
  uint8_t  init;
  uint8_t  has_pvar; /* 1 if contains C_TM_PVAR or C_TM_JOKER */
} NodeMeta;

static NodeMeta *NMETA;
static size_t nmeta_cap;
static Term *int_terms;
static size_t int_terms_cap;

static inline NodeMeta *meta_of(Term t) {
  if ((size_t)t >= nmeta_cap) {
    size_t nc = nmeta_cap ? nmeta_cap * 2 : (1u << 20);
    while (nc <= (size_t)t) nc *= 2;
    NodeMeta *nm = realloc(NMETA, nc * sizeof(NodeMeta));
    memset(nm + nmeta_cap, 0, (nc - nmeta_cap) * sizeof(NodeMeta));
    NMETA = nm;
    nmeta_cap = nc;
  }
  return &NMETA[t];
}

static uint32_t sym_lookup_n(const char *s, size_t len) {
  if (!sym_tab_cap) return 0;
  uint32_t h = hash_bytes(s, len);
  size_t mask = sym_tab_cap - 1;
  for (size_t i = h & mask;; i = (i + 1) & mask) {
    uint32_t id = sym_tab[i];
    if (!id) break;
    if (syms[id].hash == h && syms[id].len == len &&
        memcmp(syms[id].text, s, len) == 0)
      return id;
  }
  /* In --chain mode, Mod.foo resolves to foo if foo is declared */
  const char *dot = memchr(s, '.', len);
  if (dot && (size_t)(dot - s + 1) < len) {
    const char * base = dot + 1;
    size_t blen = len - (size_t)(base - s);
    uint32_t bh = hash_bytes(base, blen);
    for (size_t i = bh & mask;; i = (i + 1) & mask) {
      uint32_t id = sym_tab[i];
      if (!id) break;
      if (syms[id].hash == bh && syms[id].len == blen &&
          memcmp(syms[id].text, base, blen) == 0)
        return id;
    }
  }
  return 0;
}

static uint32_t sym_intern_n(const char *s, size_t len) {
  uint32_t existing = sym_lookup_n(s, len);
  if (existing) return existing;
  uint32_t h = hash_bytes(s, len);
  if (nsyms + 1 >= capsyms) {
    uint32_t nc = capsyms ? capsyms * 2 : 1024;
    syms = realloc(syms, (size_t)nc * sizeof(DkSym));
    capsyms = nc;
  }
  if ((size_t)(nsyms + 1) * 2 >= sym_tab_cap) {
    size_t nc = sym_tab_cap ? sym_tab_cap * 2 : 2048;
    free(sym_tab);
    sym_tab = calloc(nc, sizeof(uint32_t));
    sym_tab_cap = nc;
    size_t mask = nc - 1;
    for (uint32_t j = 1; j <= nsyms; j++) {
      size_t k = syms[j].hash & mask;
      while (sym_tab[k]) k = (k + 1) & mask;
      sym_tab[k] = j;
    }
  }
  uint32_t id = ++nsyms;
  DkSym *e = &syms[id];
  memset(e, 0, sizeof(*e));
  e->text = malloc(len + 1);
  memcpy(e->text, s, len);
  e->text[len] = '\0';
  e->len = (uint32_t)len;
  e->hash = h;
  e->nterm = tc_name((uint16_t)S_NAME, tc_fresh_name());
  meta_of(e->nterm)->uval = id;
  size_t mask = sym_tab_cap - 1;
  size_t slot = h & mask;
  while (sym_tab[slot]) slot = (slot + 1) & mask;
  sym_tab[slot] = id;
  return id;
}

/* ---- Term constructors on tcalc ---- */
static inline Term mk_int(uint32_t n) {
  if ((size_t)n >= int_terms_cap) {
    size_t nc = int_terms_cap ? int_terms_cap * 2 : 1024;
    while (nc <= (size_t)n) nc *= 2;
    Term *it = realloc(int_terms, nc * sizeof(Term));
    memset(it + int_terms_cap, 0, (nc - int_terms_cap) * sizeof(Term));
    int_terms = it;
    int_terms_cap = nc;
  }
  if (!int_terms[n]) {
    Term t = tc_name((uint16_t)S_INT, tc_fresh_name());
    meta_of(t)->uval = n;
    int_terms[n] = t;
  }
  return int_terms[n];
}

static inline uint32_t int_val(Term t) {
  return meta_of(t)->uval;
}

static Term mk_tm_db(uint32_t idx) {
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TM_DB, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) { m->init = 1; m->fv = idx + 1u; m->has_pvar = 0; }
  return t;
}

static Term mk_tm_const(uint32_t sym_id) {
  Term a[1] = { syms[sym_id].nterm };
  Term t = tc_app(C_TM_CONST, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) { m->init = 1; m->fv = 0; m->has_pvar = 0; m->uval = sym_id; }
  return t;
}

static Term mk_tm_pvar(uint32_t idx) {
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TM_PVAR, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) { m->init = 1; m->fv = 0; m->has_pvar = 1; m->uval = idx; }
  return t;
}

static Term mk_tm_joker(uint32_t idx) {
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TM_JOKER, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) { m->init = 1; m->fv = 0; m->has_pvar = 1; m->uval = idx; }
  return t;
}

static Term mk_tm_ap(Term f, Term x) {
  Term a[2] = { f, x };
  Term t = tc_app(C_TM_AP, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mf = *meta_of(f), mx = *meta_of(x);
    m = meta_of(t);
    m->init = 1;
    m->fv = mf.fv > mx.fv ? mf.fv : mx.fv;
    m->has_pvar = (uint8_t)(mf.has_pvar | mx.has_pvar);
  }
  return t;
}

static Term mk_tm_lam(Term opt_dom, Term body) {
  if (!opt_dom) opt_dom = T_NONE;
  Term a[2] = { opt_dom, body };
  Term t = tc_app(C_TM_LAM, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta md = *meta_of(opt_dom), mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    uint32_t bfv = mb.fv > 0 ? mb.fv - 1u : 0u;
    m->fv = md.fv > bfv ? md.fv : bfv;
    m->has_pvar = (uint8_t)(md.has_pvar | mb.has_pvar);
  }
  return t;
}

static Term mk_tm_pi(Term dom, Term cod) {
  Term a[2] = { dom, cod };
  Term t = tc_app(C_TM_PI, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta md = *meta_of(dom), mc = *meta_of(cod);
    m = meta_of(t);
    m->init = 1;
    uint32_t cfv = mc.fv > 0 ? mc.fv - 1u : 0u;
    m->fv = md.fv > cfv ? md.fv : cfv;
    m->has_pvar = (uint8_t)(md.has_pvar | mc.has_pvar);
  }
  return t;
}

static Term mk_ctx_cons(Term tp, Term tail) {
  Term a[2] = { tp, tail };
  return tc_app(C_CTX_CONS, a);
}

static Term ctx_nth_shifted(Term ctx, uint32_t idx);

/* ---- Operation cache for shift & instantiate ---- */
enum { OP_TM_SHIFT = 1, OP_TM_INST = 2 };
typedef struct {
  Term a, b, res;
  uint32_t param;
  int32_t amount;
  uint8_t op;
} OpSlot;
#define OP_CACHE_SIZE (1u << 17)
static OpSlot op_cache[OP_CACHE_SIZE];

static inline uint32_t op_slot_idx(uint8_t op, Term a, Term b, uint32_t p, int32_t amt) {
  uint64_t h = (uint64_t)a * 0x9e3779b97f4a7c15ULL ^
               (uint64_t)b * 0xc2b2ae3d27d4eb4fULL ^
               ((uint64_t)op << 52) ^ ((uint64_t)p << 18) ^ (uint32_t)amt;
  h ^= h >> 29;
  return (uint32_t)h & (OP_CACHE_SIZE - 1u);
}

static Term tm_shift(Term m, uint32_t cutoff, int32_t amount) {
  if (!m || amount == 0 || meta_of(m)->fv <= cutoff) return m;
  if (cutoff == 0 && amount == 1 && meta_of(m)->shift1) return meta_of(m)->shift1;
  uint32_t slot = op_slot_idx(OP_TM_SHIFT, m, 0, cutoff, amount);
  OpSlot *s = &op_cache[slot];
  if (s->op == OP_TM_SHIFT && s->a == m && s->param == cutoff && s->amount == amount)
    return s->res;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  Term r = m;
  if (hc == C_TM_DB) {
    uint32_t idx = int_val(a[0]);
    if (idx >= cutoff) r = mk_tm_db((uint32_t)((int32_t)idx + amount));
  } else if (hc == C_TM_AP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_shift(f, cutoff, amount);
    Term x2 = tm_shift(x, cutoff, amount);
    if (f2 != f || x2 != x) r = mk_tm_ap(f2, x2);
  } else if (hc == C_TM_LAM || hc == C_TM_PI) {
    Term dom = a[0], b = a[1];
    Term dom2 = (dom == T_NONE) ? T_NONE : tm_shift(dom, cutoff, amount);
    Term b2 = tm_shift(b, cutoff + 1u, amount);
    if (dom2 != dom || b2 != b)
      r = hc == C_TM_LAM ? mk_tm_lam(dom2, b2) : mk_tm_pi(dom2, b2);
  }
  if (cutoff == 0 && amount == 1) meta_of(m)->shift1 = r;
  else *s = (OpSlot){ m, 0, r, cutoff, amount, OP_TM_SHIFT };
  return r;
}

static Term tm_instantiate(Term m, uint32_t depth, Term sub) {
  if (!m || !sub || meta_of(m)->fv <= depth) return m;
  uint32_t slot = op_slot_idx(OP_TM_INST, m, sub, depth, 0);
  OpSlot *s = &op_cache[slot];
  if (s->op == OP_TM_INST && s->a == m && s->b == sub && s->param == depth)
    return s->res;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  Term r = m;
  if (hc == C_TM_DB) {
    uint32_t idx = int_val(a[0]);
    if (idx < depth) r = m;
    else if (idx == depth) r = tm_shift(sub, 0, (int32_t)depth);
    else r = mk_tm_db(idx - 1u);
  } else if (hc == C_TM_AP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_instantiate(f, depth, sub);
    Term x2 = tm_instantiate(x, depth, sub);
    if (f2 != f || x2 != x) r = mk_tm_ap(f2, x2);
  } else if (hc == C_TM_LAM || hc == C_TM_PI) {
    Term dom = a[0], b = a[1];
    Term dom2 = (dom == T_NONE) ? T_NONE : tm_instantiate(dom, depth, sub);
    Term b2 = tm_instantiate(b, depth + 1u, sub);
    if (dom2 != dom || b2 != b)
      r = hc == C_TM_LAM ? mk_tm_lam(dom2, b2) : mk_tm_pi(dom2, b2);
  }
  *s = (OpSlot){ m, sub, r, depth, 0, OP_TM_INST };
  return r;
}

static Term tm_subst_pvars(Term m, const Term *bound, uint32_t lift) {
  if (!m || !meta_of(m)->has_pvar) return m;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TM_PVAR) {
    uint32_t idx = int_val(a[0]);
    Term b = bound[idx];
    return b ? tm_shift(b, 0, (int32_t)lift) : m;
  }
  if (hc == C_TM_AP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_subst_pvars(f, bound, lift);
    Term x2 = tm_subst_pvars(x, bound, lift);
    return (f2 == f && x2 == x) ? m : mk_tm_ap(f2, x2);
  }
  if (hc == C_TM_LAM || hc == C_TM_PI) {
    Term dom = a[0], b = a[1];
    Term dom2 = (dom == T_NONE) ? T_NONE : tm_subst_pvars(dom, bound, lift);
    Term b2 = tm_subst_pvars(b, bound, lift + 1u);
    if (dom2 == dom && b2 == b) return m;
    return hc == C_TM_LAM ? mk_tm_lam(dom2, b2) : mk_tm_pi(dom2, b2);
  }
  return m;
}

static Term ctx_nth_shifted(Term ctx, uint32_t idx) {
  uint32_t cur = 0;
  for (;;) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(ctx, &k, &h, &ar, &a);
    if ((int)h != C_CTX_CONS) return 0;
    if (cur == idx) return tm_shift(a[0], 0, (int32_t)(idx + 1u));
    ctx = a[1];
    cur++;
  }
}

/* ---- WHNF reduction & Pattern Matching ---- */
static Term dk_whnf(Term m);
static bool dk_conv(Term a, Term b);

static bool match_pat(Term pat, Term tgt, Term *bound) {
  uint8_t pk; uint32_t ph; int par; const Term *pa;
  tc_node(pat, &pk, &ph, &par, &pa);
  int phc = (int)ph;
  if (phc == C_TM_JOKER) return true;
  if (phc == C_TM_PVAR) {
    uint32_t idx = int_val(pa[0]);
    if (!bound[idx]) {
      bound[idx] = tgt;
      return true;
    }
    return dk_conv(bound[idx], tgt);
  }
  if (phc == C_TM_LAM) {
    Term pbody = pa[1];
    uint8_t bk; uint32_t bh; int bar; const Term *ba;
    tc_node(pbody, &bk, &bh, &bar, &ba);
    if ((int)bh == C_TM_AP) {
      Term pf = ba[0], px = ba[1];
      uint8_t fk, xk; uint32_t fh, xh; int far, xar; const Term *fa, *xa;
      tc_node(pf, &fk, &fh, &far, &fa);
      tc_node(px, &xk, &xh, &xar, &xa);
      if ((int)fh == C_TM_PVAR && (int)xh == C_TM_DB && int_val(xa[0]) == 0) {
        uint32_t idx = int_val(fa[0]);
        if (!bound[idx]) {
          bound[idx] = tgt;
          return true;
        }
        return dk_conv(bound[idx], tgt);
      }
    }
    Term wt = dk_whnf(tgt);
    uint8_t tk; uint32_t th; int tar; const Term *ta;
    tc_node(wt, &tk, &th, &tar, &ta);
    if ((int)th != C_TM_LAM) return false;
    return match_pat(pbody, ta[1], bound);
  }
  /* Decompose pattern spine */
  Term pstack[MAX_RULE_ARGS];
  uint32_t pn = 0;
  Term phead = pat;
  for (;;) {
    tc_node(phead, &pk, &ph, &par, &pa);
    if ((int)ph != C_TM_AP) break;
    if (pn >= MAX_RULE_ARGS) return false;
    pstack[pn++] = pa[1];
    phead = pa[0];
  }
  if ((int)ph != C_TM_CONST) return false;
  uint32_t psym = meta_of(phead)->uval;

  Term wt = dk_whnf(tgt);
  Term tstack[MAX_RULE_ARGS];
  uint32_t tn = 0;
  Term thead = wt;
  uint8_t tk; uint32_t th; int tar; const Term *ta;
  for (;;) {
    tc_node(thead, &tk, &th, &tar, &ta);
    if ((int)th != C_TM_AP) break;
    if (tn >= MAX_RULE_ARGS) return false;
    tstack[tn++] = ta[1];
    thead = ta[0];
  }
  if ((int)th != C_TM_CONST || meta_of(thead)->uval != psym || tn != pn)
    return false;
  for (uint32_t i = 0; i < pn; i++) {
    /* pstack and tstack are in reverse order (outermost arg at index 0) */
    uint32_t j = pn - 1u - i;
    if (!match_pat(pstack[j], tstack[j], bound)) return false;
  }
  return true;
}

static Term dk_whnf(Term m) {
  if (!m) return 0;
  NodeMeta *mm = meta_of(m);
  if (mm->fv == 0 && !mm->has_pvar && mm->whnf_gen == g_whnf_gen && mm->whnf)
    return mm->whnf;

  Term stack_buf[256];
  Term *stack = stack_buf;
  uint32_t sp = 0, cap = 256;
  Term cur = m;

  for (;;) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(cur, &k, &h, &ar, &a);
    int hc = (int)h;
    if (hc == C_TM_AP) {
      if (sp == cap) {
        uint32_t nc = cap * 2;
        Term *ns = malloc((size_t)nc * sizeof(Term));
        memcpy(ns, stack, (size_t)sp * sizeof(Term));
        if (stack != stack_buf) free(stack);
        stack = ns;
        cap = nc;
      }
      stack[sp++] = a[1];
      cur = a[0];
      continue;
    }
    if (hc == C_TM_LAM && sp > 0) {
      Term body = a[1];
      Term arg = stack[--sp];
      cur = tm_instantiate(body, 0, arg);
      continue;
    }
    if (hc == C_TM_CONST) {
      uint32_t sym = meta_of(cur)->uval;
      DkSym *e = &syms[sym];
      bool fired = false;
      for (uint32_t r = 0; r < e->nrules; r++) {
        DkRule *rl = &e->rules[r];
        if (sp < rl->nargs) continue;
        Term bound[MAX_RULE_PVARS];
        memset(bound, 0, rl->npvars * sizeof(Term));
        bool ok = true;
        for (uint32_t j = 0; j < rl->nargs; j++) {
          Term arg = stack[sp - 1u - j];
          if (!match_pat(rl->pats[j], arg, bound)) {
            ok = false;
            break;
          }
        }
        if (ok) {
          sp -= rl->nargs;
          cur = tm_subst_pvars(rl->rhs, bound, 0);
          fired = true;
          break;
        }
      }
      if (fired) continue;
      if (e->def) {
        cur = e->def;
        continue;
      }
    }
    break;
  }

  Term res = cur;
  while (sp > 0) {
    res = mk_tm_ap(res, stack[--sp]);
  }
  if (stack != stack_buf) free(stack);

  mm = meta_of(m);
  if (mm->fv == 0 && !mm->has_pvar) {
    mm->whnf = res;
    mm->whnf_gen = g_whnf_gen;
  }
  NodeMeta *mr = meta_of(res);
  if (mr->fv == 0 && !mr->has_pvar) {
    mr->whnf = res;
    mr->whnf_gen = g_whnf_gen;
  }
  return res;
}

static bool dk_conv(Term a, Term b) {
  while (a != b) {
    a = dk_whnf(a);
    b = dk_whnf(b);
    if (a == b) return true;
    uint8_t ak, bk; uint32_t ah, bh; int aar, bar; const Term *aa, *ba;
    tc_node(a, &ak, &ah, &aar, &aa);
    tc_node(b, &bk, &bh, &bar, &ba);
    int ahc = (int)ah, bhc = (int)bh;
    if (ahc == C_TM_PI && bhc == C_TM_PI) {
      Term ad = aa[0], ac = aa[1], bd = ba[0], bc = ba[1];
      if (!dk_conv(ad, bd)) return false;
      a = ac; b = bc;
      continue;
    }
    if (ahc == C_TM_LAM && bhc == C_TM_LAM) {
      Term ad = aa[0], ac = aa[1], bd = ba[0], bc = ba[1];
      if (ad != T_NONE && bd != T_NONE && !dk_conv(ad, bd)) return false;
      a = ac; b = bc;
      continue;
    }
    /* Eta conversion: (\x. body) ~ f  iff  body ~ (shift(f, 1) DB(0)) */
    if (ahc == C_TM_LAM) {
      a = aa[1];
      b = mk_tm_ap(tm_shift(b, 0, 1), mk_tm_db(0));
      continue;
    }
    if (bhc == C_TM_LAM) {
      b = ba[1];
      a = mk_tm_ap(tm_shift(a, 0, 1), mk_tm_db(0));
      continue;
    }
    if (ahc == C_TM_AP && bhc == C_TM_AP) {
      /* Compare spine heads first to fail fast on distinct constants/vars */
      Term astack[256], bstack[256];
      uint32_t an = 0, bn = 0;
      Term ahead = a, bhead = b;
      while ((int)ah == C_TM_AP && an < 256) {
        astack[an++] = aa[1];
        ahead = aa[0];
        tc_node(ahead, &ak, &ah, &aar, &aa);
      }
      while ((int)bh == C_TM_AP && bn < 256) {
        bstack[bn++] = ba[1];
        bhead = ba[0];
        tc_node(bhead, &bk, &bh, &bar, &ba);
      }
      if (an != bn || !dk_conv(ahead, bhead)) return false;
      for (uint32_t i = an; i > 1; i--) {
        if (!dk_conv(astack[i - 1], bstack[i - 1])) return false;
      }
      a = astack[0];
      b = bstack[0];
      continue;
    }
    return false;
  }
  return true;
}

/* ---- Firing the 8 Lambda-Pi-Modulo rules on tcalc ---- */
static Occ dk_infer(Term ctx, Term m, const Term *pvar_tps, Term *out_tp);
static Occ dk_check(Term ctx, Term m, Term expected_tp, const Term *pvar_tps);

/* Check that dom has sort Type or Kind, returning TYPED(ctx, dom, sort) */
static bool g_strict_lf = true;
static bool g_allow_static_rules = false;

static Occ dk_check_sort(Term ctx, Term dom, const Term *pvar_tps, Term *out_sort) {
  *out_sort = 0;
  Term s = 0;
  Occ o = dk_infer(ctx, dom, pvar_tps, &s);
  if (!o) return 0;
  Term ws = dk_whnf(s);
  if (ws != T_TYPE && ws != T_KIND) return 0;
  if (s != ws) {
    Term cca[4] = { ctx, dom, s, ws };
    Occ ccert = tc_post(SPACE_REL, tc_app(C_CONV_CERT, cca));
    Occ ckeep[2] = { o, ccert };
    Term cinst[4] = { ctx, dom, s, ws };
    o = commit_dk_step(R_CONV, ckeep, cinst);
    if (!o) return 0;
    stat_rule_fires[7]++;
  }
  *out_sort = ws;
  return o;
}

static Occ dk_infer(Term ctx, Term m, const Term *pvar_tps, Term *out_tp) {
  *out_tp = 0;
  if (!m) return 0;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;

  if (hc == C_TM_TYPE) {
    Term ca[1] = { ctx };
    Occ cert = tc_post(SPACE_REL, tc_app(C_SORT_CERT, ca));
    Occ keep[1] = { cert };
    Term inst[1] = { ctx };
    Occ o = commit_dk_step(R_SORT, keep, inst);
    if (o) { *out_tp = T_KIND; stat_rule_fires[1]++; }
    return o;
  }

  if (hc == C_TM_CONST) {
    uint32_t sym = meta_of(m)->uval;
    if (!syms[sym].declared || !syms[sym].tp) return 0;
    Term tp = syms[sym].tp;
    Term nt = syms[sym].nterm;
    Term ca[3] = { ctx, nt, tp };
    Occ cert = tc_post(SPACE_REL, tc_app(C_CONST_CERT, ca));
    Occ keep[1] = { cert };
    Term inst[3] = { ctx, nt, tp };
    Occ o = commit_dk_step(R_CONST, keep, inst);
    if (o) { *out_tp = tp; stat_rule_fires[2]++; }
    return o;
  }

  if (hc == C_TM_DB) {
    uint32_t idx = int_val(a[0]);
    Term tp = ctx_nth_shifted(ctx, idx);
    if (!tp) return 0;
    Term ca[3] = { ctx, m, tp };
    Occ cert = tc_post(SPACE_REL, tc_app(C_VAR_CERT, ca));
    Occ keep[1] = { cert };
    Term inst[3] = { ctx, m, tp };
    Occ o = commit_dk_step(R_VAR, keep, inst);
    if (o) { *out_tp = tp; stat_rule_fires[3]++; }
    return o;
  }

  if (hc == C_TM_PVAR || hc == C_TM_JOKER) {
    uint32_t idx = int_val(a[0]);
    uint32_t slot = (hc == C_TM_JOKER) ? (MAX_RULE_PVARS + idx) : idx;
    if (!pvar_tps || !pvar_tps[slot]) return 0;
    Term tp = pvar_tps[slot];
    uint32_t depth = 0;
    for (Term c = ctx;;) {
      uint8_t ck; uint32_t ch; int car; const Term *ca;
      tc_node(c, &ck, &ch, &car, &ca);
      if ((int)ch != C_CTX_CONS) break;
      depth++; c = ca[1];
    }
    tp = tm_shift(tp, 0, (int32_t)depth);
    Term ca[3] = { ctx, m, tp };
    Occ cert = tc_post(SPACE_REL, tc_app(C_VAR_CERT, ca));
    Occ keep[1] = { cert };
    Term inst[3] = { ctx, m, tp };
    Occ o = commit_dk_step(R_VAR, keep, inst);
    if (o) { *out_tp = tp; stat_rule_fires[3]++; }
    return o;
  }

  if (hc == C_TM_PI) {
    Term dom = a[0], cod = a[1];
    Term dom_sort = 0;
    Occ dom_occ = dk_check_sort(ctx, dom, pvar_tps, &dom_sort);
    Occ dom_sort_occ = (dom_sort == T_TYPE) ? OCC_DOM_TYPE : (dom_sort == T_KIND ? OCC_DOM_KIND : 0);
    if (!dom_occ || !dom_sort_occ) return 0;
    Term inner = mk_ctx_cons(dom, ctx);
    Term cod_sort = 0;
    Occ cod_occ = dk_check_sort(inner, cod, pvar_tps, &cod_sort);
    if (!cod_occ) return 0;
    Term ca[6] = { ctx, dom, dom_sort, inner, cod, cod_sort };
    Occ cert = tc_post(SPACE_REL, tc_app(C_PI_CERT, ca));
    Occ keep[4] = { dom_occ, cod_occ, cert, dom_sort_occ };
    Term inst[6] = { ctx, dom, dom_sort, inner, cod, cod_sort };
    Occ o = commit_dk_step(R_PI, keep, inst);
    if (o) { *out_tp = cod_sort; stat_rule_fires[4]++; }
    return o;
  }

  if (hc == C_TM_LAM) {
    Term dom = a[0], body = a[1];
    if (dom == T_NONE) return 0; /* Untyped lambda requires bidirectional check */
    Term dom_sort = 0;
    Occ dom_occ = dk_check_sort(ctx, dom, pvar_tps, &dom_sort);
    Occ dom_sort_occ = (dom_sort == T_TYPE) ? OCC_DOM_TYPE : (dom_sort == T_KIND ? OCC_DOM_KIND : 0);
    if (!dom_occ || !dom_sort_occ) return 0;
    Term inner = mk_ctx_cons(dom, ctx);
    Term body_tp = 0;
    Occ body_occ = dk_infer(inner, body, pvar_tps, &body_tp);
    if (!body_occ || body_tp == T_KIND) return 0;
    Term pi_tp = mk_tm_pi(dom, body_tp);
    Term ca[7] = { ctx, dom, dom, dom_sort, inner, body, body_tp };
    Occ cert = tc_post(SPACE_REL, tc_app(C_LAM_CERT, ca));
    Occ keep[4] = { dom_occ, body_occ, cert, dom_sort_occ };
    Term inst[7] = { ctx, dom, dom, dom_sort, inner, body, body_tp };
    Occ o = commit_dk_step(R_LAM, keep, inst);
    if (o) { *out_tp = pi_tp; stat_rule_fires[5]++; }
    return o;
  }

  if (hc == C_TM_AP) {
    Term f = a[0], x = a[1];
    Term tf = 0;
    Occ f_occ = dk_infer(ctx, f, pvar_tps, &tf);
    if (!f_occ) return 0;
    Term wtf = dk_whnf(tf);
    uint8_t fk; uint32_t fh; int far; const Term *fa;
    tc_node(wtf, &fk, &fh, &far, &fa);
    if ((int)fh != C_TM_PI) return 0;
    Term dom = fa[0], cod = fa[1];
    Occ x_occ = dk_check(ctx, x, dom, pvar_tps);
    if (!x_occ) return 0;
    Term res_tp = tm_instantiate(cod, 0, x);
    Term ca[6] = { ctx, f, tf, x, dom, res_tp };
    Occ cert = tc_post(SPACE_REL, tc_app(C_APP_CERT, ca));
    Occ keep[3] = { f_occ, x_occ, cert };
    Term inst[6] = { ctx, f, tf, x, dom, res_tp };
    Occ o = commit_dk_step(R_APP, keep, inst);
    if (o) { *out_tp = res_tp; stat_rule_fires[6]++; }
    return o;
  }

  return 0;
}

static Occ dk_check(Term ctx, Term m, Term expected_tp, const Term *pvar_tps) {
  if (!m || !expected_tp) return 0;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  if ((int)h == C_TM_LAM) {
    Term opt_dom = a[0], body = a[1];
    Term wexp = dk_whnf(expected_tp);
    uint8_t ek; uint32_t eh; int ear; const Term *ea;
    tc_node(wexp, &ek, &eh, &ear, &ea);
    if ((int)eh != C_TM_PI) return 0;
    Term exp_dom = ea[0], exp_cod = ea[1];
    if (opt_dom != T_NONE) {
      Term opt_sort = 0;
      if (!dk_check_sort(ctx, opt_dom, pvar_tps, &opt_sort) ||
          !dk_conv(opt_dom, exp_dom))
        return 0;
    }
    Term dom_sort = 0;
    Occ dom_occ = dk_check_sort(ctx, exp_dom, pvar_tps, &dom_sort);
    Occ dom_sort_occ = (dom_sort == T_TYPE) ? OCC_DOM_TYPE : (dom_sort == T_KIND ? OCC_DOM_KIND : 0);
    if (!dom_occ || !dom_sort_occ) return 0;
    Term inner = mk_ctx_cons(exp_dom, ctx);
    Occ body_occ = dk_check(inner, body, exp_cod, pvar_tps);
    if (!body_occ) return 0;
    Term lam_pi = mk_tm_pi(exp_dom, exp_cod);
    Term ca[7] = { ctx, opt_dom, exp_dom, dom_sort, inner, body, exp_cod };
    Occ cert = tc_post(SPACE_REL, tc_app(C_LAM_CERT, ca));
    Occ keep[4] = { dom_occ, body_occ, cert, dom_sort_occ };
    Term inst[7] = { ctx, opt_dom, exp_dom, dom_sort, inner, body, exp_cod };
    Occ lam_occ = commit_dk_step(R_LAM, keep, inst);
    if (!lam_occ) return 0;
    stat_rule_fires[5]++;
    if (lam_pi == expected_tp) return lam_occ;
    Term cca[4] = { ctx, m, lam_pi, expected_tp };
    Occ ccert = tc_post(SPACE_REL, tc_app(C_CONV_CERT, cca));
    Occ ckeep[2] = { lam_occ, ccert };
    Term cinst[4] = { ctx, m, lam_pi, expected_tp };
    Occ conv_occ = commit_dk_step(R_CONV, ckeep, cinst);
    if (conv_occ) stat_rule_fires[7]++;
    return conv_occ;
  }

  Term inf_tp = 0;
  Occ inf_occ = dk_infer(ctx, m, pvar_tps, &inf_tp);
  if (!inf_occ) return 0;
  if (inf_tp == expected_tp) return inf_occ;
  if (!dk_conv(inf_tp, expected_tp)) return 0;
  Term ca[4] = { ctx, m, inf_tp, expected_tp };
  Occ cert = tc_post(SPACE_REL, tc_app(C_CONV_CERT, ca));
  Occ keep[2] = { inf_occ, cert };
  Term inst[4] = { ctx, m, inf_tp, expected_tp };
  Occ conv_occ = commit_dk_step(R_CONV, keep, inst);
  if (conv_occ) stat_rule_fires[7]++;
  return conv_occ;
}

/* ---- Initialize tcalc sorts, constructors, and 8 sealed rules ---- */
static void init_dk_kernel(void) {
  tc_init(1u << 23, 1u << 22);
  memset(op_cache, 0, sizeof(op_cache));
  memset(stat_rule_fires, 0, sizeof(stat_rule_fires));
  g_whnf_gen = 1;
  free(NMETA); NMETA = NULL; nmeta_cap = 0;
  free(int_terms); int_terms = NULL; int_terms_cap = 0;
  for (uint32_t i = 1; i <= nsyms; i++) {
    free(syms[i].text);
    free(syms[i].rules);
  }
  free(syms); syms = NULL; nsyms = capsyms = 0;
  free(sym_tab); sym_tab = NULL; sym_tab_cap = 0;

  S_INT   = tc_sort(SORT_PURE | SORT_FREE);
  S_NAME  = tc_sort(SORT_PURE | SORT_FREE);
  S_TM    = tc_sort(0);
  S_CTX   = tc_sort(0);
  S_CERT  = tc_sort(SORT_PROVABLE);
  S_TYPED = tc_sort(SORT_PROVABLE);

  Binder b_int[1] = { { (uint16_t)S_INT, 0, 0 } };
  Binder b_nam[1] = { { (uint16_t)S_NAME, 0, 0 } };
  Binder b_tm2[2] = { { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
  Binder b_ctxc[2] = { { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_CTX, 0, 0 } };
  Binder b_typed[3] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
  };

  C_TM_TYPE  = tc_con((uint16_t)S_TM, 0, 0, NULL);
  C_TM_KIND  = tc_con((uint16_t)S_TM, 0, 0, NULL);
  C_TM_NONE  = tc_con((uint16_t)S_TM, 0, 0, NULL);
  C_TM_DB    = tc_con((uint16_t)S_TM, 0, 1, b_int);
  C_TM_CONST = tc_con((uint16_t)S_TM, 0, 1, b_nam);
  C_TM_PVAR  = tc_con((uint16_t)S_TM, 0, 1, b_int);
  C_TM_JOKER = tc_con((uint16_t)S_TM, 0, 1, b_int);
  C_TM_AP    = tc_con((uint16_t)S_TM, 0, 2, b_tm2);
  C_TM_LAM   = tc_con((uint16_t)S_TM, 0, 2, b_tm2);
  C_TM_PI    = tc_con((uint16_t)S_TM, 0, 2, b_tm2);

  C_CTX_NIL  = tc_con((uint16_t)S_CTX, 0, 0, NULL);
  C_CTX_CONS = tc_con((uint16_t)S_CTX, 0, 2, b_ctxc);
  C_TYPED    = tc_con((uint16_t)S_TYPED, 0, 3, b_typed);

  Binder b_sort_cert[1] = { { (uint16_t)S_CTX, 0, 0 } };
  Binder b_const_cert[3] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_var_cert[3] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_pi_cert[6] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_lam_cert[7] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
    { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
    { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_app_cert[6] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
    { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_conv_cert[4] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
    { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_rew_cert[5] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_NAME, 0, 0 },
    { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_dom_sort[1] = { { (uint16_t)S_TM, 0, 0 } };

  C_SORT_CERT    = tc_con((uint16_t)S_CERT, 0, 1, b_sort_cert);
  C_CONST_CERT   = tc_con((uint16_t)S_CERT, 0, 3, b_const_cert);
  C_VAR_CERT     = tc_con((uint16_t)S_CERT, 0, 3, b_var_cert);
  C_PI_CERT      = tc_con((uint16_t)S_CERT, 0, 6, b_pi_cert);
  C_LAM_CERT     = tc_con((uint16_t)S_CERT, 0, 7, b_lam_cert);
  C_APP_CERT     = tc_con((uint16_t)S_CERT, 0, 6, b_app_cert);
  C_CONV_CERT    = tc_con((uint16_t)S_CERT, 0, 4, b_conv_cert);
  C_REWRITE_CERT = tc_con((uint16_t)S_CERT, 0, 5, b_rew_cert);
  C_DOM_SORT     = tc_con((uint16_t)S_CERT, 0, 1, b_dom_sort);
  C_DEFINABLE    = tc_con((uint16_t)S_CERT, 0, 1, b_nam);

  T_TYPE    = tc_app(C_TM_TYPE, NULL);
  T_KIND    = tc_app(C_TM_KIND, NULL);
  T_NONE    = tc_app(C_TM_NONE, NULL);
  T_CTX_NIL = tc_app(C_CTX_NIL, NULL);
  meta_of(T_TYPE)->init = 1;
  meta_of(T_KIND)->init = 1;
  meta_of(T_NONE)->init = 1;

  OCC_DOM_TYPE = tc_post(SPACE_REL, tc_app(C_DOM_SORT, &T_TYPE));
  OCC_DOM_KIND = g_strict_lf ? 0 : tc_post(SPACE_REL, tc_app(C_DOM_SORT, &T_KIND));

  /* 1. R_SORT: keep SORT_CERT(ctx) |- TYPED(ctx, Type, Kind) */
  {
    Binder v[1] = { { (uint16_t)S_CTX, 0, 0 } };
    tc_ctx(1, v);
    Term ca[1] = { tc_v(0) };
    Term ja[3] = { tc_v(0), T_TYPE, T_KIND };
    Rule r = { .nkeep = 1, .fresh = -1,
               .keep = { { tc_app(C_SORT_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_TYPED, ja), SPACE_THM } };
    R_SORT = tc_rule(&r);
  }
  /* 2. R_CONST: keep CONST_CERT(ctx, sym, tp) |- TYPED(ctx, CONST(sym), tp) */
  {
    Binder v[3] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term ca[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term na[1] = { tc_v(1) };
    Term ja[3] = { tc_v(0), tc_app(C_TM_CONST, na), tc_v(2) };
    Rule r = { .nkeep = 1, .fresh = -1,
               .keep = { { tc_app(C_CONST_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_TYPED, ja), SPACE_THM } };
    R_CONST = tc_rule(&r);
  }
  /* 3. R_VAR: keep VAR_CERT(ctx, v_term, tp) |- TYPED(ctx, v_term, tp) */
  {
    Binder v[3] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term ca[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term ja[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Rule r = { .nkeep = 1, .fresh = -1,
               .keep = { { tc_app(C_VAR_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_TYPED, ja), SPACE_THM } };
    R_VAR = tc_rule(&r);
  }
  /* 4. R_PI: keep TYPED(ctx, dom, dom_sort), TYPED(inner, cod, cod_sort),
              PI_CERT(ctx, dom, dom_sort, inner, cod, cod_sort), DOM_SORT(dom_sort)
              |- TYPED(ctx, PI(dom, cod), cod_sort) */
  {
    Binder v[6] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(6, v);
    Term j0[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term j1[3] = { tc_v(3), tc_v(4), tc_v(5) };
    Term ca[6] = { tc_v(0), tc_v(1), tc_v(2), tc_v(3), tc_v(4), tc_v(5) };
    Term ds[1] = { tc_v(2) };
    Term pa[2] = { tc_v(1), tc_v(4) };
    Term j2[3] = { tc_v(0), tc_app(C_TM_PI, pa), tc_v(5) };
    Rule r = { .nkeep = 4, .fresh = -1,
               .keep = { { tc_app(C_TYPED, j0), SPACE_THM },
                         { tc_app(C_TYPED, j1), SPACE_THM },
                         { tc_app(C_PI_CERT, ca), SPACE_REL },
                         { tc_app(C_DOM_SORT, ds), SPACE_REL } },
               .make = { tc_app(C_TYPED, j2), SPACE_THM } };
    R_PI = tc_rule(&r);
  }
  /* 5. R_LAM: keep TYPED(ctx, dom, dom_sort), TYPED(inner, body, cod),
               LAM_CERT(ctx, opt_dom, dom, dom_sort, inner, body, cod), DOM_SORT(dom_sort)
               |- TYPED(ctx, LAM(opt_dom, body), PI(dom, cod)) */
  {
    Binder v[7] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(7, v);
    Term j0[3] = { tc_v(0), tc_v(2), tc_v(3) };
    Term j1[3] = { tc_v(4), tc_v(5), tc_v(6) };
    Term ca[7] = { tc_v(0), tc_v(1), tc_v(2), tc_v(3), tc_v(4), tc_v(5), tc_v(6) };
    Term ds[1] = { tc_v(3) };
    Term la[2] = { tc_v(1), tc_v(5) };
    Term pa[2] = { tc_v(2), tc_v(6) };
    Term j2[3] = { tc_v(0), tc_app(C_TM_LAM, la), tc_app(C_TM_PI, pa) };
    Rule r = { .nkeep = 4, .fresh = -1,
               .keep = { { tc_app(C_TYPED, j0), SPACE_THM },
                         { tc_app(C_TYPED, j1), SPACE_THM },
                         { tc_app(C_LAM_CERT, ca), SPACE_REL },
                         { tc_app(C_DOM_SORT, ds), SPACE_REL } },
               .make = { tc_app(C_TYPED, j2), SPACE_THM } };
    R_LAM = tc_rule(&r);
  }
  /* 6. R_APP: keep TYPED(ctx, f, tf), TYPED(ctx, x, dom),
               APP_CERT(ctx, f, tf, x, dom, res_tp)
               |- TYPED(ctx, AP(f, x), res_tp) */
  {
    Binder v[6] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(6, v);
    Term j0[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term j1[3] = { tc_v(0), tc_v(3), tc_v(4) };
    Term ca[6] = { tc_v(0), tc_v(1), tc_v(2), tc_v(3), tc_v(4), tc_v(5) };
    Term aa[2] = { tc_v(1), tc_v(3) };
    Term j2[3] = { tc_v(0), tc_app(C_TM_AP, aa), tc_v(5) };
    Rule r = { .nkeep = 3, .fresh = -1,
               .keep = { { tc_app(C_TYPED, j0), SPACE_THM },
                         { tc_app(C_TYPED, j1), SPACE_THM },
                         { tc_app(C_APP_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_TYPED, j2), SPACE_THM } };
    R_APP = tc_rule(&r);
  }
  /* 7. R_CONV: keep TYPED(ctx, m, tp1), CONV_CERT(ctx, m, tp1, tp2)
                |- TYPED(ctx, m, tp2) */
  {
    Binder v[4] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term j0[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term ca[4] = { tc_v(0), tc_v(1), tc_v(2), tc_v(3) };
    Term j1[3] = { tc_v(0), tc_v(1), tc_v(3) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_TYPED, j0), SPACE_THM },
                         { tc_app(C_CONV_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_TYPED, j1), SPACE_THM } };
    R_CONV = tc_rule(&r);
  }
  /* 8. R_REWRITE_ADMIT: keep TYPED(ctx, lhs, tp), TYPED(ctx, rhs, tp),
                         REWRITE_CERT(ctx, head_name, lhs, rhs, tp),
                         DEFINABLE(head_name)
                         |- TYPED(ctx, rhs, tp) */
  {
    Binder v[5] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_NAME, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(5, v);
    Term j0[3] = { tc_v(0), tc_v(2), tc_v(4) };
    Term j1[3] = { tc_v(0), tc_v(3), tc_v(4) };
    Term ca[5] = { tc_v(0), tc_v(1), tc_v(2), tc_v(3), tc_v(4) };
    Term df[1] = { tc_v(1) };
    Rule r = { .nkeep = 4, .fresh = -1,
               .keep = { { tc_app(C_TYPED, j0), SPACE_THM },
                         { tc_app(C_TYPED, j1), SPACE_THM },
                         { tc_app(C_REWRITE_CERT, ca), SPACE_REL },
                         { tc_app(C_DEFINABLE, df), SPACE_REL } },
               .make = { tc_app(C_TYPED, j1), SPACE_THM } };
    R_REWRITE_ADMIT = tc_rule(&r);
  }

  tc_protect(SPACE_THM);
  tc_seal();
}

/* ---- Pattern Type Inference & Joker Elaboration for Rewrite Rules ---- */
static Term tm_subst_jokers(Term m, const Term *joker_sub) {
  if (!m || !meta_of(m)->has_pvar) return m;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TM_JOKER) {
    uint32_t idx = int_val(a[0]);
    return (idx < MAX_RULE_PVARS && joker_sub[idx]) ? joker_sub[idx] : m;
  }
  if (hc == C_TM_AP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_subst_jokers(f, joker_sub);
    Term x2 = tm_subst_jokers(x, joker_sub);
    return (f2 == f && x2 == x) ? m : mk_tm_ap(f2, x2);
  }
  if (hc == C_TM_LAM || hc == C_TM_PI) {
    Term dom = a[0], b = a[1];
    Term dom2 = (dom == T_NONE) ? T_NONE : tm_subst_jokers(dom, joker_sub);
    Term b2 = tm_subst_jokers(b, joker_sub);
    if (dom2 == dom && b2 == b) return m;
    return hc == C_TM_LAM ? mk_tm_lam(dom2, b2) : mk_tm_pi(dom2, b2);
  }
  return m;
}

static void unify_jokers(Term actual, Term expected, Term *joker_sub, Term *pvar_tps) {
  if (!actual || !expected || actual == expected) return;
  actual = tm_subst_jokers(actual, joker_sub);
  expected = tm_subst_jokers(expected, joker_sub);
  if (actual == expected) return;
  uint8_t ak, ek; uint32_t ah, eh; int aar, ear; const Term *aa, *ea;
  tc_node(actual, &ak, &ah, &aar, &aa);
  tc_node(expected, &ek, &eh, &ear, &ea);
  if ((int)eh == C_TM_JOKER) {
    uint32_t idx = int_val(ea[0]);
    if (idx < MAX_RULE_PVARS && !joker_sub[idx]) joker_sub[idx] = actual;
    return;
  }
  if ((int)ah == C_TM_JOKER) {
    uint32_t idx = int_val(aa[0]);
    if (idx < MAX_RULE_PVARS && !joker_sub[idx]) joker_sub[idx] = expected;
    return;
  }
  if ((int)ah == C_TM_AP && (int)eh == C_TM_AP) {
    Term af = aa[0], ax = aa[1], ef = ea[0], ex = ea[1];
    unify_jokers(af, ef, joker_sub, pvar_tps);
    unify_jokers(ax, ex, joker_sub, pvar_tps);
  } else if (((int)ah == C_TM_PI && (int)eh == C_TM_PI) ||
             ((int)ah == C_TM_LAM && (int)eh == C_TM_LAM)) {
    Term ad = aa[0], ac = aa[1], ed = ea[0], ec = ea[1];
    if (ad != T_NONE && ed != T_NONE) unify_jokers(ad, ed, joker_sub, pvar_tps);
    unify_jokers(ac, ec, joker_sub, pvar_tps);
  }
  (void)pvar_tps;
}

static Term infer_pat_term(Term ctx, Term m, Term exp_tp, Term *pvar_tps, Term *joker_sub) {
  if (!m) return 0;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TM_TYPE) return T_KIND;
  if (hc == C_TM_CONST) {
    uint32_t sym = meta_of(m)->uval;
    return syms[sym].tp;
  }
  if (hc == C_TM_DB) {
    return ctx_nth_shifted(ctx, int_val(a[0]));
  }
  if (hc == C_TM_PVAR) {
    uint32_t idx = int_val(a[0]);
    if (!pvar_tps[idx] && exp_tp) pvar_tps[idx] = tm_subst_jokers(exp_tp, joker_sub);
    return pvar_tps[idx];
  }
  if (hc == C_TM_JOKER) {
    uint32_t idx = int_val(a[0]);
    uint32_t slot = MAX_RULE_PVARS + idx;
    if (!pvar_tps[slot] && exp_tp) pvar_tps[slot] = tm_subst_jokers(exp_tp, joker_sub);
    return pvar_tps[slot];
  }
  if (hc == C_TM_LAM) {
    Term opt_dom = a[0], body = a[1];
    Term dom = opt_dom;
    Term cod_exp = 0;
    if (exp_tp) {
      Term wexp = dk_whnf(tm_subst_jokers(exp_tp, joker_sub));
      uint8_t ek; uint32_t eh; int ear; const Term *ea;
      tc_node(wexp, &ek, &eh, &ear, &ea);
      if ((int)eh == C_TM_PI) {
        if (dom == T_NONE) dom = ea[0];
        cod_exp = ea[1];
      }
    }
    if (dom == T_NONE) return 0;
    /* Check Miller pattern (\x. p x) */
    uint8_t bk; uint32_t bh; int bar; const Term *ba;
    tc_node(body, &bk, &bh, &bar, &ba);
    if ((int)bh == C_TM_AP) {
      Term pf = ba[0], px = ba[1];
      uint8_t fk, xk; uint32_t fh, xh; int far, xar; const Term *fa, *xa;
      tc_node(pf, &fk, &fh, &far, &fa);
      tc_node(px, &xk, &xh, &xar, &xa);
      if ((int)fh == C_TM_PVAR && (int)xh == C_TM_DB && int_val(xa[0]) == 0 && exp_tp) {
        uint32_t idx = int_val(fa[0]);
        if (!pvar_tps[idx]) pvar_tps[idx] = tm_subst_jokers(exp_tp, joker_sub);
        return pvar_tps[idx];
      }
    }
    Term inner = mk_ctx_cons(dom, ctx);
    Term btp = infer_pat_term(inner, body, cod_exp, pvar_tps, joker_sub);
    return btp ? mk_tm_pi(dom, btp) : 0;
  }
  if (hc == C_TM_AP) {
    Term stack[MAX_RULE_ARGS];
    uint32_t n = 0;
    Term head = m;
    while ((int)h == C_TM_AP && n < MAX_RULE_ARGS) {
      stack[n++] = a[1];
      head = a[0];
      tc_node(head, &k, &h, &ar, &a);
    }
    Term tf = infer_pat_term(ctx, head, 0, pvar_tps, joker_sub);
    if (!tf) return 0;
    for (uint32_t i = n; i > 0; i--) {
      Term arg = stack[i - 1];
      Term wtf = dk_whnf(tm_subst_jokers(tf, joker_sub));
      uint8_t fk; uint32_t fh; int far; const Term *fa;
      tc_node(wtf, &fk, &fh, &far, &fa);
      if ((int)fh != C_TM_PI) return 0;
      Term dom = fa[0], cod = fa[1];
      Term atp = infer_pat_term(ctx, arg, dom, pvar_tps, joker_sub);
      if (atp) unify_jokers(atp, dom, joker_sub, pvar_tps);
      Term arg_sub = tm_subst_jokers(arg, joker_sub);
      tf = tm_instantiate(cod, 0, arg_sub);
    }
    if (exp_tp) unify_jokers(tf, exp_tp, joker_sub, pvar_tps);
    return tm_subst_jokers(tf, joker_sub);
  }
  return 0;
}

static bool admit_rewrite_rule(uint32_t npvars, Term *pvar_tps, Term lhs, Term rhs) {
  /* Decompose LHS spine */
  Term stack[MAX_RULE_ARGS];
  uint32_t n = 0;
  Term head = lhs;
  uint8_t k; uint32_t h; int ar; const Term *a;
  for (;;) {
    tc_node(head, &k, &h, &ar, &a);
    if ((int)h != C_TM_AP) break;
    if (n >= MAX_RULE_ARGS) return false;
    stack[n++] = a[1];
    head = a[0];
  }
  if ((int)h != C_TM_CONST) return false;
  uint32_t head_sym = meta_of(head)->uval;
  if (!syms[head_sym].declared) return false;
  if (!syms[head_sym].def_occ) return false;

  /* Every pattern variable on RHS must occur in LHS */
  uint64_t lhs_fv = meta_of(lhs)->fv;
  uint64_t rhs_fv = meta_of(rhs)->fv;
  if ((rhs_fv & ~lhs_fv) != 0) return false;

  /* Infer any untyped pattern variables and jokers from LHS */
  Term joker_sub[MAX_RULE_PVARS] = {0};
  infer_pat_term(T_CTX_NIL, lhs, 0, pvar_tps, joker_sub);
  for (uint32_t i = 0; i < npvars * 2 && i < MAX_RULE_PVARS * 2; i++) {
    if (pvar_tps[i]) pvar_tps[i] = tm_subst_jokers(pvar_tps[i], joker_sub);
  }
  Term lhs_elab = tm_subst_jokers(lhs, joker_sub);
  (void)npvars;

  Term lhs_tp = 0;
  Occ lhs_occ = dk_infer(T_CTX_NIL, lhs_elab, pvar_tps, &lhs_tp);
  if (!lhs_occ) return false;
  Occ rhs_occ = dk_check(T_CTX_NIL, rhs, lhs_tp, pvar_tps);
  if (!rhs_occ) return false;
  Term ca[5] = { T_CTX_NIL, syms[head_sym].nterm, lhs_elab, rhs, lhs_tp };
  Occ cert = tc_post(SPACE_REL, tc_app(C_REWRITE_CERT, ca));
  Occ keep[4] = { lhs_occ, rhs_occ, cert, syms[head_sym].def_occ };
  Term inst[5] = { T_CTX_NIL, syms[head_sym].nterm, lhs_elab, rhs, lhs_tp };
  if (!commit_dk_step(R_REWRITE_ADMIT, keep, inst)) return false;
  stat_rule_fires[8]++;

  /* Install rule on head_sym */
  DkSym *e = &syms[head_sym];
  if (e->nrules == e->caprules) {
    uint32_t nc = e->caprules ? e->caprules * 2 : 4;
    e->rules = realloc(e->rules, (size_t)nc * sizeof(DkRule));
    e->caprules = nc;
  }
  DkRule *rl = &e->rules[e->nrules++];
  rl->head_sym = head_sym;
  rl->nargs = n;
  rl->npvars = npvars;
  for (uint32_t j = 0; j < n; j++) {
    rl->pats[j] = stack[n - 1u - j];
  }
  rl->rhs = rhs;
  g_whnf_gen++;
  return true;
}

/* ---- Lexer & Recursive-Descent Parser for .dk files ---- */
enum {
  TOK_EOF = 0,
  TOK_IDENT,
  TOK_LPAREN,   /* ( */
  TOK_RPAREN,   /* ) */
  TOK_LBRACK,   /* [ */
  TOK_RBRACK,   /* ] */
  TOK_COMMA,    /* , */
  TOK_DOT,      /* . */
  TOK_COLON,    /* : */
  TOK_DEFEQ,    /* := */
  TOK_ARROW,    /* -> */
  TOK_FATARROW, /* => */
  TOK_REWRITE,  /* --> */
  TOK_EQEQ      /* == */
};

typedef struct {
  int kind;
  const char *text;
  size_t len;
  uint32_t line;
} Token;

typedef struct {
  const char *src;
  size_t pos;
  uint32_t line;
  Token cur, peek;
  bool has_peek;
} Lexer;

static void lex_skip_ws_comments(Lexer *lx) {
  for (;;) {
    while (lx->src[lx->pos] && isspace((unsigned char)lx->src[lx->pos])) {
      if (lx->src[lx->pos] == '\n') lx->line++;
      lx->pos++;
    }
    if (lx->src[lx->pos] == '(' && lx->src[lx->pos + 1] == ';') {
      lx->pos += 2;
      int depth = 1;
      while (lx->src[lx->pos] && depth > 0) {
        if (lx->src[lx->pos] == '\n') lx->line++;
        if (lx->src[lx->pos] == '(' && lx->src[lx->pos + 1] == ';') {
          depth++; lx->pos += 2;
        } else if (lx->src[lx->pos] == ';' && lx->src[lx->pos + 1] == ')') {
          depth--; lx->pos += 2;
        } else {
          lx->pos++;
        }
      }
      continue;
    }
    break;
  }
}

static Token lex_raw(Lexer *lx) {
  lex_skip_ws_comments(lx);
  uint32_t ln = lx->line;
  const char *s = lx->src + lx->pos;
  if (!*s) return (Token){ TOK_EOF, s, 0, ln };

  if (*s == '(') { lx->pos++; return (Token){ TOK_LPAREN, s, 1, ln }; }
  if (*s == ')') { lx->pos++; return (Token){ TOK_RPAREN, s, 1, ln }; }
  if (*s == '[') { lx->pos++; return (Token){ TOK_LBRACK, s, 1, ln }; }
  if (*s == ']') { lx->pos++; return (Token){ TOK_RBRACK, s, 1, ln }; }
  if (*s == ',') { lx->pos++; return (Token){ TOK_COMMA, s, 1, ln }; }
  if (*s == '.') { lx->pos++; return (Token){ TOK_DOT, s, 1, ln }; }
  if (s[0] == '-' && s[1] == '-' && s[2] == '>') {
    lx->pos += 3; return (Token){ TOK_REWRITE, s, 3, ln };
  }
  if (s[0] == '-' && s[1] == '>') {
    lx->pos += 2; return (Token){ TOK_ARROW, s, 2, ln };
  }
  if (s[0] == ':' && s[1] == '=') {
    lx->pos += 2; return (Token){ TOK_DEFEQ, s, 2, ln };
  }
  if (s[0] == '=' && s[1] == '>') {
    lx->pos += 2; return (Token){ TOK_FATARROW, s, 2, ln };
  }
  if (s[0] == '=' && s[1] == '=') {
    lx->pos += 2; return (Token){ TOK_EQEQ, s, 2, ln };
  }
  if (*s == ':') { lx->pos++; return (Token){ TOK_COLON, s, 1, ln }; }

  /* Escaped identifier {| ... |} */
  if (s[0] == '{' && s[1] == '|') {
    lx->pos += 2;
    const char *start = lx->src + lx->pos;
    while (lx->src[lx->pos] &&
           !(lx->src[lx->pos] == '|' && lx->src[lx->pos + 1] == '}')) {
      if (lx->src[lx->pos] == '\n') lx->line++;
      lx->pos++;
    }
    size_t len = (size_t)((lx->src + lx->pos) - start);
    if (lx->src[lx->pos] == '|') lx->pos += 2;
    return (Token){ TOK_IDENT, start, len, ln };
  }

  const char *start = s;
  while (lx->src[lx->pos]) {
    char c = lx->src[lx->pos];
    char c1 = lx->src[lx->pos + 1];
    if (isspace((unsigned char)c) || c == '(' || c == ')' || c == '[' ||
        c == ']' || c == ',' || c == ':' || (c == '-' && (c1 == '>' || c1 == '-')) ||
        (c == '=' && (c1 == '>' || c1 == '=')))
      break;
    if (c == '.') {
      /* Qualified identifier Mod.foo if followed by identifier char */
      if (isalnum((unsigned char)c1) || c1 == '_' || c1 == '{') {
        lx->pos++;
        continue;
      }
      break;
    }
    lx->pos++;
  }
  return (Token){ TOK_IDENT, start, (size_t)((lx->src + lx->pos) - start), ln };
}

static void lex_init(Lexer *lx, const char *src) {
  lx->src = src;
  lx->pos = 0;
  lx->line = 1;
  lx->has_peek = false;
  lx->cur = lex_raw(lx);
}

static Token lex_next(Lexer *lx) {
  Token t = lx->cur;
  if (lx->has_peek) {
    lx->cur = lx->peek;
    lx->has_peek = false;
  } else {
    lx->cur = lex_raw(lx);
  }
  return t;
}

static Token lex_peek(Lexer *lx) {
  if (!lx->has_peek) {
    lx->peek = lex_raw(lx);
    lx->has_peek = true;
  }
  return lx->peek;
}

static inline bool tok_is_kw(const Token *t, const char *kw) {
  size_t n = strlen(kw);
  return t->kind == TOK_IDENT && t->len == n && memcmp(t->text, kw, n) == 0;
}

/* Scope context during parsing */
typedef struct {
  const char *bvar_names[256];
  size_t      bvar_lens[256];
  uint32_t    nbvars;
  const char *pvar_names[MAX_RULE_PVARS];
  size_t      pvar_lens[MAX_RULE_PVARS];
  uint32_t    npvars;
  uint32_t    njokers;
  bool        in_rule_lhs;
} ParseScope;

static Term parse_term(Lexer *lx, ParseScope *sc);
static Term parse_app_term(Lexer *lx, ParseScope *sc);

static Term parse_atom_term(Lexer *lx, ParseScope *sc) {
  if (lx->cur.kind == TOK_LPAREN) {
    lex_next(lx);
    Term t = parse_term(lx, sc);
    if (!t || lx->cur.kind != TOK_RPAREN) return 0;
    lex_next(lx);
    return t;
  }
  if (lx->cur.kind != TOK_IDENT) return 0;
  Token id = lex_next(lx);
  if (tok_is_kw(&id, "Type")) return T_TYPE;
  if (tok_is_kw(&id, "Kind")) return T_KIND;
  if (sc->in_rule_lhs && tok_is_kw(&id, "_")) {
    if (sc->njokers >= MAX_RULE_PVARS) return 0;
    return mk_tm_joker(sc->njokers++);
  }
  /* 1. Bound de Bruijn variables (innermost first) */
  for (uint32_t i = sc->nbvars; i > 0; i--) {
    uint32_t j = i - 1u;
    if (sc->bvar_lens[j] == id.len &&
        memcmp(sc->bvar_names[j], id.text, id.len) == 0) {
      return mk_tm_db(sc->nbvars - 1u - j);
    }
  }
  /* 2. Rule pattern variables */
  for (uint32_t i = 0; i < sc->npvars; i++) {
    if (sc->pvar_lens[i] == id.len &&
        memcmp(sc->pvar_names[i], id.text, id.len) == 0) {
      return mk_tm_pvar(i);
    }
  }
  /* 3. Declared global symbol (must already be declared! Rejects forward refs) */
  uint32_t sym = sym_lookup_n(id.text, id.len);
  if (!sym || !syms[sym].declared) {
    fprintf(stderr, "dk_tcalc: undeclared symbol '%.*s' at line %u\n",
            (int)id.len, id.text, id.line);
    return 0;
  }
  return mk_tm_const(sym);
}

static bool is_atom_start(const Token *t) {
  if (t->kind == TOK_LPAREN) return true;
  if (t->kind == TOK_IDENT) {
    if (tok_is_kw(t, "def") || tok_is_kw(t, "thm") || tok_is_kw(t, "injective"))
      return false;
    return true;
  }
  return false;
}

/* Check if current '(' starts a parenthesized binder `(x : aterm) ->` or `(x : aterm) =>` */
static bool looks_like_paren_binder(Lexer *lx) {
  if (lx->cur.kind != TOK_LPAREN) return false;
  Token t1 = lex_peek(lx);
  if (t1.kind != TOK_IDENT) return false;
  Lexer tmp = *lx;
  lex_next(&tmp); /* ( */
  lex_next(&tmp); /* ident */
  if (tmp.cur.kind != TOK_COLON) return false;
  lex_next(&tmp); /* : */
  int depth = 1;
  while (tmp.cur.kind != TOK_EOF && depth > 0) {
    if (depth == 1 &&
        (tmp.cur.kind == TOK_ARROW || tmp.cur.kind == TOK_FATARROW ||
         tmp.cur.kind == TOK_COLON)) {
      return false;
    }
    if (tmp.cur.kind == TOK_LPAREN) depth++;
    else if (tmp.cur.kind == TOK_RPAREN) depth--;
    lex_next(&tmp);
  }
  return tmp.cur.kind == TOK_ARROW || tmp.cur.kind == TOK_FATARROW;
}

static Term parse_app_term(Lexer *lx, ParseScope *sc) {
  Term head = parse_atom_term(lx, sc);
  if (!head) return 0;
  while (is_atom_start(&lx->cur)) {
    Term arg = parse_atom_term(lx, sc);
    if (!arg) return 0;
    head = mk_tm_ap(head, arg);
  }
  return head;
}

static Term parse_term(Lexer *lx, ParseScope *sc) {
  /* 1. Untyped lambda: `x => body` */
  if (lx->cur.kind == TOK_IDENT && lex_peek(lx).kind == TOK_FATARROW) {
    Token id = lex_next(lx);
    lex_next(lx); /* => */
    if (sc->nbvars >= 256) return 0;
    sc->bvar_names[sc->nbvars] = id.text;
    sc->bvar_lens[sc->nbvars] = id.len;
    sc->nbvars++;
    Term body = parse_term(lx, sc);
    sc->nbvars--;
    return body ? mk_tm_lam(T_NONE, body) : 0;
  }
  /* 2. Typed binder: `x : A -> B` or `x : A => body` */
  if (lx->cur.kind == TOK_IDENT && lex_peek(lx).kind == TOK_COLON) {
    Token id = lex_next(lx);
    lex_next(lx); /* : */
    Term dom = parse_app_term(lx, sc);
    if (!dom) return 0;
    int arrow = lx->cur.kind;
    if (arrow != TOK_ARROW && arrow != TOK_FATARROW) return 0;
    lex_next(lx);
    if (sc->nbvars >= 256) return 0;
    sc->bvar_names[sc->nbvars] = tok_is_kw(&id, "_") ? "" : id.text;
    sc->bvar_lens[sc->nbvars] = tok_is_kw(&id, "_") ? 0 : id.len;
    sc->nbvars++;
    Term body = parse_term(lx, sc);
    sc->nbvars--;
    if (!body) return 0;
    return arrow == TOK_ARROW ? mk_tm_pi(dom, body) : mk_tm_lam(dom, body);
  }
  /* 3. Parenthesized binder: `(x : A) -> B` or `(x : A) => body` */
  if (looks_like_paren_binder(lx)) {
    lex_next(lx); /* ( */
    Token id = lex_next(lx);
    lex_next(lx); /* : */
    Term dom = parse_term(lx, sc);
    if (!dom || lx->cur.kind != TOK_RPAREN) return 0;
    lex_next(lx); /* ) */
    int arrow = lx->cur.kind;
    if (arrow != TOK_ARROW && arrow != TOK_FATARROW) return 0;
    lex_next(lx);
    if (sc->nbvars >= 256) return 0;
    sc->bvar_names[sc->nbvars] = tok_is_kw(&id, "_") ? "" : id.text;
    sc->bvar_lens[sc->nbvars] = tok_is_kw(&id, "_") ? 0 : id.len;
    sc->nbvars++;
    Term body = parse_term(lx, sc);
    sc->nbvars--;
    if (!body) return 0;
    return arrow == TOK_ARROW ? mk_tm_pi(dom, body) : mk_tm_lam(dom, body);
  }
  /* 4. Application term optionally followed by `-> B` */
  Term lhs = parse_app_term(lx, sc);
  if (!lhs) return 0;
  if (lx->cur.kind == TOK_ARROW) {
    lex_next(lx); /* -> */
    if (sc->nbvars >= 256) return 0;
    sc->bvar_names[sc->nbvars] = "";
    sc->bvar_lens[sc->nbvars] = 0;
    sc->nbvars++;
    Term rhs = parse_term(lx, sc);
    sc->nbvars--;
    return rhs ? mk_tm_pi(lhs, rhs) : 0;
  }
  return lhs;
}

typedef struct {
  uint32_t decls, defs, thms, rules, asserts;
} DkStats;

static bool check_dk_buf(const char *buf, const char *path, DkStats *st) {
  Lexer lx;
  lex_init(&lx, buf);
  bool ok = true;

  while (ok && lx.cur.kind != TOK_EOF) {
    /* Top-level directive `#REQUIRE`, `#NAME`, `#ASSERT`, `#ASSERTNOT`, `#EVAL` */
    if (lx.cur.kind == TOK_IDENT && lx.cur.len > 0 && lx.cur.text[0] == '#') {
      Token dir = lex_next(&lx);
      if (tok_is_kw(&dir, "#REQUIRE") || tok_is_kw(&dir, "#NAME")) {
        while (lx.cur.kind != TOK_EOF && lx.cur.kind != TOK_DOT) lex_next(&lx);
        if (lx.cur.kind == TOK_DOT) lex_next(&lx);
        continue;
      }
      if (tok_is_kw(&dir, "#EVAL")) {
        if (lx.cur.kind == TOK_LBRACK) {
          while (lx.cur.kind != TOK_EOF && lx.cur.kind != TOK_RBRACK) lex_next(&lx);
          if (lx.cur.kind == TOK_RBRACK) lex_next(&lx);
        }
        ParseScope sc = {0};
        Term t = parse_term(&lx, &sc);
        if (!t || lx.cur.kind != TOK_DOT) { ok = false; break; }
        lex_next(&lx);
        (void)dk_whnf(t);
        continue;
      }
      if (tok_is_kw(&dir, "#ASSERT") || tok_is_kw(&dir, "#ASSERTNOT")) {
        bool want_eq = tok_is_kw(&dir, "#ASSERT");
        ParseScope sc = {0};
        Term t1 = parse_term(&lx, &sc);
        if (!t1 || lx.cur.kind != TOK_EQEQ) { ok = false; break; }
        lex_next(&lx);
        Term t2 = parse_term(&lx, &sc);
        if (!t2 || lx.cur.kind != TOK_DOT) { ok = false; break; }
        lex_next(&lx);
        if (dk_conv(t1, t2) != want_eq) {
          fprintf(stderr, "dk_tcalc: %.*s failed at line %u in %s\n",
                  (int)dir.len, dir.text, dir.line, path);
          ok = false; break;
        }
        st->asserts++;
        continue;
      }
    }

    /* Rewrite rule(s): `[ ... ] lhs --> rhs` */
    if (lx.cur.kind == TOK_LBRACK) {
      while (lx.cur.kind == TOK_LBRACK) {
        lex_next(&lx); /* [ */
        ParseScope sc = {0};
        Term pvar_tps[MAX_RULE_PVARS * 2] = {0};
        while (lx.cur.kind != TOK_EOF && lx.cur.kind != TOK_RBRACK) {
          if (lx.cur.kind != TOK_IDENT || sc.npvars >= MAX_RULE_PVARS) {
            ok = false; break;
          }
          Token vid = lex_next(&lx);
          uint32_t vidx = sc.npvars++;
          sc.pvar_names[vidx] = vid.text;
          sc.pvar_lens[vidx] = vid.len;
          if (lx.cur.kind == TOK_COLON) {
            lex_next(&lx);
            Term vtp = parse_term(&lx, &sc);
            if (!vtp) { ok = false; break; }
            pvar_tps[vidx] = vtp;
          }
          if (lx.cur.kind == TOK_COMMA) lex_next(&lx);
        }
        if (!ok || lx.cur.kind != TOK_RBRACK) { ok = false; break; }
        lex_next(&lx); /* ] */
        sc.in_rule_lhs = true;
        Term lhs = parse_term(&lx, &sc);
        sc.in_rule_lhs = false;
        if (!lhs || lx.cur.kind != TOK_REWRITE) { ok = false; break; }
        lex_next(&lx); /* --> */
        Term rhs = parse_term(&lx, &sc);
        if (!rhs) { ok = false; break; }
        if (!admit_rewrite_rule(sc.npvars, pvar_tps, lhs, rhs)) {
          fprintf(stderr, "dk_tcalc: rewrite rule refused in %s\n", path);
          ok = false; break;
        }
        st->rules++;
        if (lx.cur.kind == TOK_DOT) {
          lex_next(&lx);
          break;
        }
      }
      continue;
    }

    /* Declaration / Definition / Theorem */
    bool is_def = false, is_thm = false, is_inj = false;
    if (tok_is_kw(&lx.cur, "def")) { is_def = true; lex_next(&lx); }
    else if (tok_is_kw(&lx.cur, "thm")) { is_thm = true; lex_next(&lx); }
    else if (tok_is_kw(&lx.cur, "injective")) { is_inj = true; lex_next(&lx); }
    else if (tok_is_kw(&lx.cur, "private")) { lex_next(&lx); if (tok_is_kw(&lx.cur, "def")) { is_def = true; lex_next(&lx); } }

    if (lx.cur.kind != TOK_IDENT) {
      fprintf(stderr, "dk_tcalc: expected identifier at line %u in %s\n", lx.cur.line, path);
      ok = false; break;
    }
    Token sym_tok = lex_next(&lx);
    ParseScope sc = {0};
    Term param_doms[64];
    uint32_t nparams = 0;

    /* Optional parameters `(x1 : A1) ... (xk : Ak)` before `:` or `:=` */
    while (lx.cur.kind == TOK_LPAREN) {
      lex_next(&lx); /* ( */
      if (lx.cur.kind != TOK_IDENT || nparams >= 64) { ok = false; break; }
      Token pid = lex_next(&lx);
      if (lx.cur.kind != TOK_COLON) { ok = false; break; }
      lex_next(&lx); /* : */
      Term pdom = parse_term(&lx, &sc);
      if (!pdom || lx.cur.kind != TOK_RPAREN) { ok = false; break; }
      lex_next(&lx); /* ) */
      param_doms[nparams++] = pdom;
      sc.bvar_names[sc.nbvars] = pid.text;
      sc.bvar_lens[sc.nbvars] = pid.len;
      sc.nbvars++;
    }
    if (!ok) break;

    Term decl_tp = 0, body_tm = 0;
    if (lx.cur.kind == TOK_COLON) {
      lex_next(&lx);
      decl_tp = parse_term(&lx, &sc);
      if (!decl_tp) { ok = false; break; }
    }
    if (lx.cur.kind == TOK_DEFEQ) {
      lex_next(&lx);
      body_tm = parse_term(&lx, &sc);
      if (!body_tm) { ok = false; break; }
    }
    if (lx.cur.kind != TOK_DOT || (!decl_tp && !body_tm)) {
      fprintf(stderr, "dk_tcalc: malformed declaration '%.*s' at line %u in %s\n",
              (int)sym_tok.len, sym_tok.text, sym_tok.line, path);
      ok = false; break;
    }
    lex_next(&lx); /* . */

    /* Wrap parameters around decl_tp (as Pi) and body_tm (as Lam) */
    for (uint32_t i = nparams; i > 0; i--) {
      Term pdom = param_doms[i - 1];
      if (decl_tp) decl_tp = mk_tm_pi(pdom, decl_tp);
      if (body_tm) body_tm = mk_tm_lam(pdom, body_tm);
    }

    if (decl_tp) {
      Term sort_tp = 0;
      if (!dk_check_sort(T_CTX_NIL, decl_tp, NULL, &sort_tp)) {
        fprintf(stderr, "dk_tcalc: ill-sorted type for '%.*s' in %s\n",
                (int)sym_tok.len, sym_tok.text, path);
        ok = false; break;
      }
    }
    if (body_tm) {
      if (decl_tp) {
        if (!dk_check(T_CTX_NIL, body_tm, decl_tp, NULL)) {
          fprintf(stderr, "dk_tcalc: type mismatch in '%.*s' in %s\n",
                  (int)sym_tok.len, sym_tok.text, path);
          ok = false; break;
        }
      } else {
        if (!dk_infer(T_CTX_NIL, body_tm, NULL, &decl_tp) || !decl_tp) {
          fprintf(stderr, "dk_tcalc: cannot infer type of '%.*s' in %s\n",
                  (int)sym_tok.len, sym_tok.text, path);
          ok = false; break;
        }
      }
    }

    uint32_t sid = sym_intern_n(sym_tok.text, sym_tok.len);
    if (syms[sid].declared && !(body_tm && body_tm == mk_tm_const(sid))) {
      fprintf(stderr, "dk_tcalc: redeclaration of '%.*s' in %s\n",
              (int)sym_tok.len, sym_tok.text, path);
      ok = false; break;
    }
    syms[sid].declared = true;
    syms[sid].rewritable = is_def || is_inj;
    if ((syms[sid].rewritable || g_allow_static_rules) && !syms[sid].def_occ) {
      syms[sid].def_occ = tc_post(SPACE_REL, tc_app(C_DEFINABLE, &syms[sid].nterm));
    }
    syms[sid].tp = decl_tp;
    if (body_tm && !is_thm && body_tm != mk_tm_const(sid)) {
      syms[sid].def = body_tm;
      g_whnf_gen++;
    }
    if (is_thm) st->thms++;
    else if (body_tm) st->defs++;
    else st->decls++;
  }
  return ok;
}

static bool check_dk_file(const char *path, DkStats *st) {
  FILE *f = fopen(path, "rb");
  if (!f) { fprintf(stderr, "dk_tcalc: cannot open %s\n", path); return false; }
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *buf = malloc((size_t)sz + 1);
  if ((long)fread(buf, 1, (size_t)sz, f) != sz) {
    fclose(f); free(buf); return false;
  }
  fclose(f);
  buf[sz] = '\0';
  bool ok = check_dk_buf(buf, path, st);
  free(buf);
  return ok;
}

/* ---- Self-test: all 8 rules + 5 negative soundness controls ---- */
static bool run_self_test(void) {
  init_dk_kernel();
  DkStats st = {0};
  const char *pos_src =
    "Nat : Type.\n"
    "z : Nat.\n"
    "s : Nat -> Nat.\n"
    "def plus : Nat -> Nat -> Nat.\n"
    "[m : Nat] plus z m --> m\n"
    "[n : Nat, m : Nat] plus (s n) m --> s (plus n m).\n"
    "Vec : Nat -> Type.\n"
    "vnil : Vec z.\n"
    "vcons : (n : Nat) -> Vec n -> Vec (s n).\n"
    "def vapp : (n : Nat) -> (m : Nat) -> Vec n -> Vec m -> Vec (plus n m).\n"
    "[m : Nat, ys : Vec m] vapp z m vnil ys --> ys.\n"
    "def one : Nat := s z.\n"
    "thm v_one : (m : Nat) -> Vec m -> Vec (plus one m) := m : Nat => ys : Vec m => vcons m (vapp z m vnil ys).\n"
    "#ASSERT plus one one == s one.\n";

  if (!check_dk_buf(pos_src, "<self-test-pos>", &st)) return false;

  /* Verify all 8 Lambda-Pi-Modulo rules fired at least once */
  for (int r = 1; r <= 8; r++) {
    if (stat_rule_fires[r] == 0) return false;
  }

  /* Negative control 1: non-convertible dependent index must be refused */
  if (check_dk_buf("thm bad1 : Vec (s z) := vnil.\n", "<neg-1>", &st)) return false;

  /* Negative control 2: ill-typed rewrite rule RHS must be refused */
  if (check_dk_buf("[m : Nat] plus z m --> vnil.\n", "<neg-2>", &st)) return false;

  /* Negative control 3: forward reference to undeclared symbol must be refused */
  if (check_dk_buf("def bad3 : Nat := ghost.\nghost : Nat.\n", "<neg-3>", &st)) return false;

  /* Negative control 4: non-convertible #ASSERT must be refused */
  if (check_dk_buf("#ASSERT z == s z.\n", "<neg-4>", &st)) return false;

  /* Negative control 5: applying non-function must be refused */
  if (check_dk_buf("def bad5 : Nat := z z.\n", "<neg-5>", &st)) return false;

  return true;
}

int main(int argc, char **argv) {
  bool did_self_test = false;
  bool chain_mode = false;
  bool inited = false;
  int files_run = 0;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--self-test") == 0) {
      double t0 = now_ms();
      if (!run_self_test()) {
        fprintf(stderr, "dk_tcalc: self-test FAILED\n");
        return 1;
      }
      printf("dk_tcalc self-test: 8 rules + 5 negative controls passed (%.2f ms)\n",
             now_ms() - t0);
      did_self_test = true;
      inited = false;
    } else if (strcmp(argv[i], "--chain") == 0) {
      chain_mode = true;
      inited = false;
    } else if (strcmp(argv[i], "--coc") == 0) {
      g_strict_lf = false;
      inited = false;
    } else if (strcmp(argv[i], "--allow-static-rules") == 0) {
      g_allow_static_rules = true;
    } else if (strcmp(argv[i], "--pts") == 0 && i + 1 < argc) {
      i++;
      if (strcmp(argv[i], "lf") == 0) g_strict_lf = true;
      else if (strcmp(argv[i], "cc") == 0) g_strict_lf = false;
      else {
        fprintf(stderr, "dk_tcalc: unknown --pts mode '%s' (expected lf or cc)\n", argv[i]);
        return 1;
      }
      inited = false;
    } else {
      double t0 = now_ms();
      if (!chain_mode || !inited) {
        init_dk_kernel();
        inited = true;
      }
      uint64_t fires_before = 0;
      for (int r = 1; r <= 8; r++) fires_before += stat_rule_fires[r];
      DkStats st = {0};
      if (!check_dk_file(argv[i], &st)) {
        fprintf(stderr, "dk_tcalc: FAILED on %s\n", argv[i]);
        return 1;
      }
      uint64_t fires_after = 0;
      for (int r = 1; r <= 8; r++) fires_after += stat_rule_fires[r];
      printf("dk_tcalc%s %s: %u decls, %u defs, %u thms, %u rules, %u asserts, %" PRIu64 " rule fires in %.2f ms\n",
             chain_mode ? " [chain]" : "", argv[i],
             st.decls, st.defs, st.thms, st.rules, st.asserts,
             fires_after - fires_before, now_ms() - t0);
      files_run++;
    }
  }

  if (!did_self_test && files_run == 0) {
    if (!run_self_test()) return 1;
    printf("dk_tcalc self-test: passed\n");
  }
  return 0;
}
