/* Megalodon (Egal HoTTG & HF) proof-kernel & -sexprinfo verifier on tcalc.
   Types, terms, type/hypothesis lists, binder contexts, side-condition
   certificates (SPACE_REL), subproof spaces (birthed via SpacesCreation and
   gated by NamedSpacesReach), and theorem judgments J(ctx, prop) (SPACE_THM,
   protected) are hash-consed tcalc terms and occurrences. Once sealed
   (tc_seal), SPACE_THM can only be populated by firing the installed tcalc
   rules for the 8 Megalodon inference rules (hyp, known, termApp, proofApp,
   termLam, proofLam, typeApp, typeLam), subproof-space hypothesis discharge,
   and top-level theorem/axiom admission. */
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
enum { PROF_EGAL = 0, PROF_HF = 1, PROF_MIZAR = 2, PROF_HOAS = 3 };
static bool g_allow_axioms = true;

static int S_INT, S_NAME, S_TP, S_TM, S_TPL, S_TML, S_CTX, S_CERT, S_THM, S_HANDLE;
static int C_TP_PROP, C_TP_BASE, C_TP_VAR, C_TP_ARR, C_TP_ALL;
static int C_TM_DB, C_TM_NAME, C_TM_PRIM, C_TM_AP, C_TM_LAM;
static int C_TM_IMP, C_TM_ALL, C_TM_TAP, C_TM_TLAM, C_TM_TALL;
static int C_TPLN, C_TPLC, C_TMLN, C_TMLC, C_CTX;
static int C_THM;
static int C_HYP_CERT, C_KNOWN_CERT, C_TERM_APP_CERT, C_PROOF_APP_CERT;
static int C_TERM_LAM_CERT, C_PROOF_LAM_CERT, C_TYPE_APP_CERT, C_TYPE_LAM_CERT;
static int C_THM_IMPORT_CERT, C_AXIOM_CERT;
static int C_HANDLE, C_SUB_MARK, C_SUB_HYP, C_SUB_AUTH;

static int R_HYP, R_KNOWN, R_TERM_APP, R_PROOF_APP;
static int R_TERM_LAM, R_PROOF_LAM, R_TYPE_APP, R_TYPE_LAM;
static int R_THM_IMPORT, R_AXIOM;
static int R_SUB_BIRTH, R_SUB_USE_HYP;

static Term T_TP_PROP, T_TP_SET, T_TPLN, T_TMLN, T_CTX_EMPTY;

/* ---- Interned names & declarations ---- */
typedef struct {
  char *text;
  uint32_t len, hash;
  Term nterm;
  /* term namespace */
  bool has_term;
  bool is_param;
  uint64_t term_seq;
  Term tp;
  Term def;        /* beta-eta normal form if defined, 0 if parameter */
  /* known namespace */
  bool has_known;
  Term prop;
  Occ  known_occ;  /* SPACE_THM occurrence for ({}, prop) */
} MgSym;

static MgSym *syms;
static uint32_t nsyms, capsyms;
static uint32_t *sym_tab;
static size_t sym_tab_cap;
static uint64_t next_decl_seq = 1;

static uint32_t hash_bytes(const char *s, size_t n) {
  uint32_t h = 2166136261u;
  for (size_t i = 0; i < n; i++) {
    h ^= (uint8_t)s[i];
    h *= 16777619u;
  }
  return h ? h : 1u;
}

/* ---- Per-Term metadata cache (fv, ftv, plain, nf, shift1) ---- */
typedef struct {
  uint32_t fv;       /* 1 + max free DB index, 0 if closed */
  uint32_t ftv;      /* 1 + max free type-var index, 0 if closed */
  uint32_t uval;     /* integer value for S_INT or symbol id for S_NAME */
  Term     nf;       /* beta-eta normal form */
  Term     shift1;   /* shift(0, +1) */
  uint8_t  init;
  uint8_t  plain;    /* for types: 1 if no C_TP_ALL */
  uint8_t  has_name; /* for terms: 1 if contains C_TM_NAME */
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

static uint32_t sym_intern_n(const char *s, size_t len) {
  uint32_t h = hash_bytes(s, len);
  if (sym_tab_cap) {
    size_t mask = sym_tab_cap - 1;
    for (size_t i = h & mask;; i = (i + 1) & mask) {
      uint32_t id = sym_tab[i];
      if (!id) break;
      if (syms[id].hash == h && syms[id].len == len &&
          memcmp(syms[id].text, s, len) == 0)
        return id;
    }
  }
  if (nsyms + 1 >= capsyms) {
    uint32_t nc = capsyms ? capsyms * 2 : 1024;
    syms = realloc(syms, (size_t)nc * sizeof(MgSym));
    capsyms = nc;
  }
  if ((size_t)(nsyms + 1) * 2 >= sym_tab_cap) {
    size_t nc = sym_tab_cap ? sym_tab_cap * 2 : 2048;
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
  MgSym *e = &syms[id];
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

static uint32_t sym_intern(const char *s) {
  return sym_intern_n(s, strlen(s));
}

/* ---- Term & Type constructors on tcalc ---- */
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

static Term mk_tp_prop(void) {
  NodeMeta *m = meta_of(T_TP_PROP);
  if (!m->init) { m->init = 1; m->plain = 1; m->ftv = 0; }
  return T_TP_PROP;
}
static Term mk_tp_base(uint32_t idx) {
  if (idx == 0 && T_TP_SET) return T_TP_SET;
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TP_BASE, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) { m->init = 1; m->plain = 1; m->ftv = 0; }
  return t;
}
static Term mk_tp_var(uint32_t idx) {
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TP_VAR, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) { m->init = 1; m->plain = 1; m->ftv = idx + 1u; }
  return t;
}
static Term mk_tp_arr(Term dom, Term cod) {
  Term a[2] = { dom, cod };
  Term t = tc_app(C_TP_ARR, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta md = *meta_of(dom), mc = *meta_of(cod);
    m = meta_of(t);
    m->init = 1;
    m->plain = (uint8_t)(md.plain & mc.plain);
    m->ftv = md.ftv > mc.ftv ? md.ftv : mc.ftv;
  }
  return t;
}
static Term mk_tp_all(Term body) {
  Term a[1] = { body };
  Term t = tc_app(C_TP_ALL, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    m->plain = 0;
    m->ftv = mb.ftv > 0 ? mb.ftv - 1u : 0u;
  }
  return t;
}

static inline bool tp_plain_wf(Term tp, uint32_t depth) {
  NodeMeta *m = meta_of(tp);
  return m->plain && m->ftv <= depth;
}

static Term mk_tm_db(uint32_t idx) {
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TM_DB, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    m->init = 1; m->fv = idx + 1u; m->ftv = 0; m->has_name = 0; m->nf = t;
  }
  return t;
}
static Term mk_tm_name(uint32_t sym_id) {
  Term a[1] = { syms[sym_id].nterm };
  Term t = tc_app(C_TM_NAME, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    m->init = 1; m->fv = 0; m->ftv = 0; m->has_name = 1; m->nf = t;
  }
  return t;
}
static Term mk_tm_prim(uint32_t idx) {
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TM_PRIM, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    m->init = 1; m->fv = 0; m->ftv = 0; m->has_name = 0; m->nf = t;
  }
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
    m->ftv = mf.ftv > mx.ftv ? mf.ftv : mx.ftv;
    m->has_name = (uint8_t)(mf.has_name | mx.has_name);
  }
  return t;
}
static Term mk_tm_imp(Term p, Term q) {
  Term a[2] = { p, q };
  Term t = tc_app(C_TM_IMP, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mp = *meta_of(p), mq = *meta_of(q);
    m = meta_of(t);
    m->init = 1;
    m->fv = mp.fv > mq.fv ? mp.fv : mq.fv;
    m->ftv = mp.ftv > mq.ftv ? mp.ftv : mq.ftv;
    m->has_name = (uint8_t)(mp.has_name | mq.has_name);
  }
  return t;
}
static Term mk_tm_lam(Term tp, Term body) {
  Term a[2] = { tp, body };
  Term t = tc_app(C_TM_LAM, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mt = *meta_of(tp), mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    m->fv = mb.fv > 0 ? mb.fv - 1u : 0u;
    m->ftv = mt.ftv > mb.ftv ? mt.ftv : mb.ftv;
    m->has_name = mb.has_name;
  }
  return t;
}
static Term mk_tm_all(Term tp, Term body) {
  Term a[2] = { tp, body };
  Term t = tc_app(C_TM_ALL, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mt = *meta_of(tp), mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    m->fv = mb.fv > 0 ? mb.fv - 1u : 0u;
    m->ftv = mt.ftv > mb.ftv ? mt.ftv : mb.ftv;
    m->has_name = mb.has_name;
  }
  return t;
}
static Term mk_tm_tap(Term f, Term tp) {
  Term a[2] = { f, tp };
  Term t = tc_app(C_TM_TAP, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mf = *meta_of(f), mt = *meta_of(tp);
    m = meta_of(t);
    m->init = 1;
    m->fv = mf.fv;
    m->ftv = mf.ftv > mt.ftv ? mf.ftv : mt.ftv;
    m->has_name = mf.has_name;
  }
  return t;
}
static Term mk_tm_tlam(Term body) {
  Term a[1] = { body };
  Term t = tc_app(C_TM_TLAM, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    m->fv = mb.fv;
    m->ftv = mb.ftv > 0 ? mb.ftv - 1u : 0u;
    m->has_name = mb.has_name;
  }
  return t;
}
static Term mk_tm_tall(Term body) {
  Term a[1] = { body };
  Term t = tc_app(C_TM_TALL, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    m->fv = mb.fv;
    m->ftv = mb.ftv > 0 ? mb.ftv - 1u : 0u;
    m->has_name = mb.has_name;
  }
  return t;
}

static Term mk_tplc(Term h, Term t) {
  Term a[2] = { h, t };
  return tc_app(C_TPLC, a);
}
static Term mk_tmlc(Term h, Term t) {
  Term a[2] = { h, t };
  return tc_app(C_TMLC, a);
}
static Term mk_ctx(uint32_t depth, Term tpl, Term tml) {
  if (depth == 0 && tpl == T_TPLN && tml == T_TMLN && T_CTX_EMPTY)
    return T_CTX_EMPTY;
  Term a[3] = { mk_int(depth), tpl, tml };
  return tc_app(C_CTX, a);
}

static void unpack_ctx(Term ctx, uint32_t *depth, Term *tpl, Term *tml) {
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(ctx, &k, &h, &ar, &a);
  Term d_t = a[0], tp_t = a[1], tm_t = a[2];
  *depth = int_val(d_t);
  *tpl = tp_t;
  *tml = tm_t;
}

static Term list_nth(Term l, int cons_con, uint32_t idx) {
  for (;;) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(l, &k, &h, &ar, &a);
    if ((int)h != cons_con) return 0;
    if (idx == 0) return a[0];
    l = a[1];
    idx--;
  }
}

/* ---- Direct-mapped operation cache ---- */
enum {
  OP_TP_SHIFT = 1, OP_TP_INST, OP_TM_SHIFT, OP_TM_TSHIFT,
  OP_TM_INST, OP_TM_TINST, OP_INFER
};
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

static inline Term op_cache_get(uint8_t op, Term a, Term b, uint32_t p, int32_t amt) {
  OpSlot *s = &op_cache[op_slot_idx(op, a, b, p, amt)];
  if (s->op == op && s->a == a && s->b == b && s->param == p && s->amount == amt)
    return s->res;
  return 0;
}

static inline void op_cache_put(uint8_t op, Term a, Term b, uint32_t p, int32_t amt, Term res) {
  if (!res) return;
  OpSlot *s = &op_cache[op_slot_idx(op, a, b, p, amt)];
  *s = (OpSlot){ a, b, res, p, amt, op };
}

/* ---- Shifting & Instantiation ---- */
static Term tp_shift(Term tp, uint32_t cutoff, int32_t amount) {
  if (!tp || amount == 0 || meta_of(tp)->ftv <= cutoff) return tp;
  if (cutoff == 0 && amount == 1 && meta_of(tp)->shift1) return meta_of(tp)->shift1;
  Term hit = op_cache_get(OP_TP_SHIFT, tp, 0, cutoff, amount);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(tp, &k, &h, &ar, &a);
  Term r = tp;
  if ((int)h == C_TP_VAR) {
    uint32_t idx = int_val(a[0]);
    if (idx >= cutoff) r = mk_tp_var((uint32_t)((int32_t)idx + amount));
  } else if ((int)h == C_TP_ARR) {
    Term d = a[0], c = a[1];
    Term d2 = tp_shift(d, cutoff, amount);
    Term c2 = tp_shift(c, cutoff, amount);
    r = (d2 == d && c2 == c) ? tp : mk_tp_arr(d2, c2);
  } else if ((int)h == C_TP_ALL) {
    Term b = a[0];
    Term b2 = tp_shift(b, cutoff + 1u, amount);
    r = (b2 == b) ? tp : mk_tp_all(b2);
  }
  if (cutoff == 0 && amount == 1) meta_of(tp)->shift1 = r;
  else op_cache_put(OP_TP_SHIFT, tp, 0, cutoff, amount, r);
  return r;
}

static Term tp_instantiate(Term tp, uint32_t depth, Term sub) {
  if (!tp || !sub || meta_of(tp)->ftv <= depth) return tp;
  Term hit = op_cache_get(OP_TP_INST, tp, sub, depth, 0);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(tp, &k, &h, &ar, &a);
  Term r = tp;
  if ((int)h == C_TP_VAR) {
    uint32_t idx = int_val(a[0]);
    if (idx < depth) r = tp;
    else if (idx == depth) r = tp_shift(sub, 0, (int32_t)depth);
    else r = mk_tp_var(idx - 1u);
  } else if ((int)h == C_TP_ARR) {
    Term d = a[0], c = a[1];
    Term d2 = tp_instantiate(d, depth, sub);
    Term c2 = tp_instantiate(c, depth, sub);
    r = (d2 == d && c2 == c) ? tp : mk_tp_arr(d2, c2);
  } else if ((int)h == C_TP_ALL) {
    Term b = a[0];
    Term b2 = tp_instantiate(b, depth + 1u, sub);
    r = (b2 == b) ? tp : mk_tp_all(b2);
  }
  op_cache_put(OP_TP_INST, tp, sub, depth, 0, r);
  return r;
}

static Term tm_shift(Term m, uint32_t cutoff, int32_t amount) {
  if (!m || amount == 0 || meta_of(m)->fv <= cutoff) return m;
  if (cutoff == 0 && amount == 1 && meta_of(m)->shift1) return meta_of(m)->shift1;
  Term hit = op_cache_get(OP_TM_SHIFT, m, 0, cutoff, amount);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  Term r = m;
  int hc = (int)h;
  if (hc == C_TM_DB) {
    uint32_t idx = int_val(a[0]);
    if (idx >= cutoff) r = mk_tm_db((uint32_t)((int32_t)idx + amount));
  } else if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_shift(f, cutoff, amount);
    Term x2 = tm_shift(x, cutoff, amount);
    if (f2 != f || x2 != x) r = hc == C_TM_AP ? mk_tm_ap(f2, x2) : mk_tm_imp(f2, x2);
  } else if (hc == C_TM_LAM || hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    Term b2 = tm_shift(b, cutoff + 1u, amount);
    if (b2 != b) r = hc == C_TM_LAM ? mk_tm_lam(tp, b2) : mk_tm_all(tp, b2);
  } else if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    Term f2 = tm_shift(f, cutoff, amount);
    if (f2 != f) r = mk_tm_tap(f2, tp);
  } else if (hc == C_TM_TLAM || hc == C_TM_TALL) {
    Term b = a[0];
    Term b2 = tm_shift(b, cutoff, amount);
    if (b2 != b) r = hc == C_TM_TLAM ? mk_tm_tlam(b2) : mk_tm_tall(b2);
  }
  if (cutoff == 0 && amount == 1) meta_of(m)->shift1 = r;
  else op_cache_put(OP_TM_SHIFT, m, 0, cutoff, amount, r);
  return r;
}

static Term tm_tshift(Term m, uint32_t cutoff, int32_t amount) {
  if (!m || amount == 0 || meta_of(m)->ftv <= cutoff) return m;
  Term hit = op_cache_get(OP_TM_TSHIFT, m, 0, cutoff, amount);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  Term r = m;
  int hc = (int)h;
  if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_tshift(f, cutoff, amount);
    Term x2 = tm_tshift(x, cutoff, amount);
    if (f2 != f || x2 != x) r = hc == C_TM_AP ? mk_tm_ap(f2, x2) : mk_tm_imp(f2, x2);
  } else if (hc == C_TM_LAM || hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    Term tp2 = tp_shift(tp, cutoff, amount);
    Term b2 = tm_tshift(b, cutoff, amount);
    if (tp2 != tp || b2 != b) r = hc == C_TM_LAM ? mk_tm_lam(tp2, b2) : mk_tm_all(tp2, b2);
  } else if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    Term f2 = tm_tshift(f, cutoff, amount);
    Term tp2 = tp_shift(tp, cutoff, amount);
    if (f2 != f || tp2 != tp) r = mk_tm_tap(f2, tp2);
  } else if (hc == C_TM_TLAM || hc == C_TM_TALL) {
    Term b = a[0];
    Term b2 = tm_tshift(b, cutoff + 1u, amount);
    if (b2 != b) r = hc == C_TM_TLAM ? mk_tm_tlam(b2) : mk_tm_tall(b2);
  }
  op_cache_put(OP_TM_TSHIFT, m, 0, cutoff, amount, r);
  return r;
}

static Term tm_instantiate(Term m, uint32_t depth, Term sub) {
  if (!m || !sub || meta_of(m)->fv <= depth) return m;
  Term hit = op_cache_get(OP_TM_INST, m, sub, depth, 0);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  Term r = m;
  int hc = (int)h;
  if (hc == C_TM_DB) {
    uint32_t idx = int_val(a[0]);
    if (idx < depth) r = m;
    else if (idx == depth) r = tm_shift(sub, 0, (int32_t)depth);
    else r = mk_tm_db(idx - 1u);
  } else if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_instantiate(f, depth, sub);
    Term x2 = tm_instantiate(x, depth, sub);
    if (f2 != f || x2 != x) r = hc == C_TM_AP ? mk_tm_ap(f2, x2) : mk_tm_imp(f2, x2);
  } else if (hc == C_TM_LAM || hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    Term b2 = tm_instantiate(b, depth + 1u, sub);
    if (b2 != b) r = hc == C_TM_LAM ? mk_tm_lam(tp, b2) : mk_tm_all(tp, b2);
  } else if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    Term f2 = tm_instantiate(f, depth, sub);
    if (f2 != f) r = mk_tm_tap(f2, tp);
  } else if (hc == C_TM_TLAM || hc == C_TM_TALL) {
    Term b = a[0];
    Term b2 = tm_instantiate(b, depth, sub);
    if (b2 != b) r = hc == C_TM_TLAM ? mk_tm_tlam(b2) : mk_tm_tall(b2);
  }
  op_cache_put(OP_TM_INST, m, sub, depth, 0, r);
  return r;
}

static Term tm_tinstantiate(Term m, uint32_t depth, Term sub_tp) {
  if (!m || !sub_tp || meta_of(m)->ftv <= depth) return m;
  Term hit = op_cache_get(OP_TM_TINST, m, sub_tp, depth, 0);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  Term r = m;
  int hc = (int)h;
  if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_tinstantiate(f, depth, sub_tp);
    Term x2 = tm_tinstantiate(x, depth, sub_tp);
    if (f2 != f || x2 != x) r = hc == C_TM_AP ? mk_tm_ap(f2, x2) : mk_tm_imp(f2, x2);
  } else if (hc == C_TM_LAM || hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    Term tp2 = tp_instantiate(tp, depth, sub_tp);
    Term b2 = tm_tinstantiate(b, depth, sub_tp);
    if (tp2 != tp || b2 != b) r = hc == C_TM_LAM ? mk_tm_lam(tp2, b2) : mk_tm_all(tp2, b2);
  } else if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    Term f2 = tm_tinstantiate(f, depth, sub_tp);
    Term tp2 = tp_instantiate(tp, depth, sub_tp);
    if (f2 != f || tp2 != tp) r = mk_tm_tap(f2, tp2);
  } else if (hc == C_TM_TLAM || hc == C_TM_TALL) {
    Term b = a[0];
    Term b2 = tm_tinstantiate(b, depth + 1u, sub_tp);
    if (b2 != b) r = hc == C_TM_TLAM ? mk_tm_tlam(b2) : mk_tm_tall(b2);
  }
  op_cache_put(OP_TM_TINST, m, sub_tp, depth, 0, r);
  return r;
}

static Term tpl_shift1(Term l) {
  if (l == T_TPLN) return l;
  if (meta_of(l)->shift1) return meta_of(l)->shift1;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(l, &k, &h, &ar, &a);
  Term hd = a[0], tl = a[1];
  Term r = mk_tplc(tp_shift(hd, 0, 1), tpl_shift1(tl));
  meta_of(l)->shift1 = r;
  return r;
}

static Term tml_shift1(Term l) {
  if (l == T_TMLN) return l;
  if (meta_of(l)->shift1) return meta_of(l)->shift1;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(l, &k, &h, &ar, &a);
  Term hd = a[0], tl = a[1];
  Term r = mk_tmlc(tm_shift(hd, 0, 1), tml_shift1(tl));
  meta_of(l)->shift1 = r;
  return r;
}

static bool tm_free_db(Term m, uint32_t idx) {
  if (meta_of(m)->fv <= idx) return false;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TM_DB) return int_val(a[0]) == idx;
  if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    return tm_free_db(f, idx) || tm_free_db(x, idx);
  }
  if (hc == C_TM_LAM || hc == C_TM_ALL) return tm_free_db(a[1], idx + 1u);
  if (hc == C_TM_TAP || hc == C_TM_TLAM || hc == C_TM_TALL) return tm_free_db(a[0], idx);
  return false;
}

static bool tp_free_tv(Term tp, uint32_t idx) {
  if (meta_of(tp)->ftv <= idx) return false;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(tp, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TP_VAR) return int_val(a[0]) == idx;
  if (hc == C_TP_ARR) {
    Term d = a[0], c = a[1];
    return tp_free_tv(d, idx) || tp_free_tv(c, idx);
  }
  if (hc == C_TP_ALL) return tp_free_tv(a[0], idx + 1u);
  return false;
}

static bool tm_free_tv(Term m, uint32_t idx) {
  if (meta_of(m)->ftv <= idx) return false;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    return tm_free_tv(f, idx) || tm_free_tv(x, idx);
  }
  if (hc == C_TM_LAM || hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    return tp_free_tv(tp, idx) || tm_free_tv(b, idx);
  }
  if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    return tm_free_tv(f, idx) || tp_free_tv(tp, idx);
  }
  if (hc == C_TM_TLAM || hc == C_TM_TALL) return tm_free_tv(a[0], idx + 1u);
  return false;
}

/* ---- Beta-eta normal form (for DEF bodies) ---- */
static Term tm_nf(Term m) {
  if (!m) return 0;
  if (meta_of(m)->nf) return meta_of(m)->nf;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  Term r = m;
  if (hc == C_TM_AP) {
    Term f0 = a[0], x0 = a[1];
    Term f = tm_nf(f0);
    Term x = tm_nf(x0);
    uint8_t fk; uint32_t fh; int far; const Term *fa;
    tc_node(f, &fk, &fh, &far, &fa);
    if ((int)fh == C_TM_LAM) {
      r = tm_nf(tm_instantiate(fa[1], 0, x));
    } else {
      r = (f == f0 && x == x0) ? m : mk_tm_ap(f, x);
    }
  } else if (hc == C_TM_LAM) {
    Term tp = a[0], b0 = a[1];
    Term b = tm_nf(b0);
    uint8_t bk; uint32_t bh; int bar; const Term *ba;
    tc_node(b, &bk, &bh, &bar, &ba);
    if ((int)bh == C_TM_AP) {
      Term bf = ba[0], bx = ba[1];
      uint8_t xk; uint32_t xh; int xar; const Term *xa;
      tc_node(bx, &xk, &xh, &xar, &xa);
      if ((int)xh == C_TM_DB && int_val(xa[0]) == 0 && !tm_free_db(bf, 0)) {
        r = tm_shift(bf, 0, -1);
      } else {
        r = (b == b0) ? m : mk_tm_lam(tp, b);
      }
    } else {
      r = (b == b0) ? m : mk_tm_lam(tp, b);
    }
  } else if (hc == C_TM_TAP) {
    Term f0 = a[0], tp = a[1];
    Term f = tm_nf(f0);
    uint8_t fk; uint32_t fh; int far; const Term *fa;
    tc_node(f, &fk, &fh, &far, &fa);
    if ((int)fh == C_TM_TLAM) {
      r = tm_nf(tm_tinstantiate(fa[0], 0, tp));
    } else {
      r = (f == f0) ? m : mk_tm_tap(f, tp);
    }
  } else if (hc == C_TM_TLAM) {
    Term b0 = a[0];
    Term b = tm_nf(b0);
    uint8_t bk; uint32_t bh; int bar; const Term *ba;
    tc_node(b, &bk, &bh, &bar, &ba);
    if ((int)bh == C_TM_TAP) {
      Term bf = ba[0], btp = ba[1];
      uint8_t tk; uint32_t th; int tar; const Term *ta;
      tc_node(btp, &tk, &th, &tar, &ta);
      if ((int)th == C_TP_VAR && int_val(ta[0]) == 0 && !tm_free_tv(bf, 0)) {
        r = tm_tshift(bf, 0, -1);
      } else {
        r = (b == b0) ? m : mk_tm_tlam(b);
      }
    } else {
      r = (b == b0) ? m : mk_tm_tlam(b);
    }
  } else if (hc == C_TM_IMP) {
    Term p0 = a[0], q0 = a[1];
    Term p = tm_nf(p0), q = tm_nf(q0);
    r = (p == p0 && q == q0) ? m : mk_tm_imp(p, q);
  } else if (hc == C_TM_ALL) {
    Term tp = a[0], b0 = a[1];
    Term b = tm_nf(b0);
    r = (b == b0) ? m : mk_tm_all(tp, b);
  } else if (hc == C_TM_TALL) {
    Term b0 = a[0];
    Term b = tm_nf(b0);
    r = (b == b0) ? m : mk_tm_tall(b);
  }
  meta_of(m)->nf = r;
  meta_of(r)->nf = r;
  return r;
}

/* ---- Profile primitive tables (Egal HoTTG, HF, Mizar, HOAS) ---- */
static Term prim_types[8];
static uint32_t nprims;

static const char *profile_label(int profile) {
  switch (profile) {
  case PROF_EGAL:  return "egal";
  case PROF_HF:    return "hf";
  case PROF_MIZAR: return "mizar";
  case PROF_HOAS:  return "hoas";
  default:         return "unknown";
  }
}

static void init_profile_prims(int profile) {
  memset(prim_types, 0, sizeof(prim_types));
  T_TP_SET = mk_tp_base(0);
  Term set = T_TP_SET;
  Term prop = mk_tp_prop();
  Term set_set = mk_tp_arr(set, set);
  Term set_set_prop = mk_tp_arr(set, mk_tp_arr(set, prop));
  /* 0: Choice : Pi A. (A -> prop) -> A */
  Term v0 = mk_tp_var(0);
  prim_types[0] = mk_tp_all(mk_tp_arr(mk_tp_arr(v0, prop), v0));
  if (profile == PROF_HOAS) {
    nprims = 1;
    return;
  }
  /* 1: In : set -> set -> prop */
  prim_types[1] = set_set_prop;
  /* 3: Union : set -> set */
  prim_types[3] = set_set;
  if (profile == PROF_MIZAR) {
    nprims = 4;
    return;
  }
  /* 2: Empty : set */
  prim_types[2] = set;
  /* 4: Power : set -> set */
  prim_types[4] = set_set;
  /* 5: Repl : set -> (set -> set) -> set */
  prim_types[5] = mk_tp_arr(set, mk_tp_arr(set_set, set));
  if (profile == PROF_EGAL) {
    /* 6: UnivOf : set -> set */
    prim_types[6] = set_set;
    nprims = 7;
  } else {
    nprims = 6;
  }
}

/* ---- Type inference & proposition checking ---- */
static Term infer_term(uint32_t depth, Term tpl, Term m) {
  if (!m) return 0;
  Term key_tpl = meta_of(m)->fv == 0 ? T_TPLN : tpl;
  Term hit = op_cache_get(OP_INFER, m, key_tpl, depth, 0);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  Term r = 0;
  if (hc == C_TM_DB) {
    r = list_nth(tpl, C_TPLC, int_val(a[0]));
  } else if (hc == C_TM_PRIM) {
    uint32_t idx = int_val(a[0]);
    if (idx < nprims) r = prim_types[idx];
  } else if (hc == C_TM_NAME) {
    uint32_t id = meta_of(a[0])->uval;
    if (id <= nsyms && syms[id].has_term) r = syms[id].tp;
  } else if (hc == C_TM_AP) {
    Term f = a[0], x = a[1];
    Term tf = infer_term(depth, tpl, f);
    if (tf) {
      uint8_t tk; uint32_t th; int tar; const Term *ta;
      tc_node(tf, &tk, &th, &tar, &ta);
      if ((int)th == C_TP_ARR) {
        Term dom = ta[0], cod = ta[1];
        Term tx = infer_term(depth, tpl, x);
        if (tx == dom) r = cod;
      }
    }
  } else if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    if (tp_plain_wf(tp, depth)) {
      Term tf = infer_term(depth, tpl, f);
      if (tf) {
        uint8_t tk; uint32_t th; int tar; const Term *ta;
        tc_node(tf, &tk, &th, &tar, &ta);
        if ((int)th == C_TP_ALL) r = tp_instantiate(ta[0], 0, tp);
      }
    }
  } else if (hc == C_TM_LAM) {
    Term tp = a[0], b = a[1];
    if (tp_plain_wf(tp, depth)) {
      Term tb = infer_term(depth, mk_tplc(tp, tpl), b);
      if (tb) r = mk_tp_arr(tp, tb);
    }
  } else if (hc == C_TM_TLAM) {
    Term b = a[0];
    Term tb = infer_term(depth + 1u, tpl_shift1(tpl), b);
    if (tb) r = mk_tp_all(tb);
  } else if (hc == C_TM_IMP) {
    Term p = a[0], q = a[1];
    if (infer_term(depth, tpl, p) == T_TP_PROP &&
        infer_term(depth, tpl, q) == T_TP_PROP)
      r = T_TP_PROP;
  } else if (hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    if (tp_plain_wf(tp, depth) &&
        infer_term(depth, mk_tplc(tp, tpl), b) == T_TP_PROP)
      r = T_TP_PROP;
  }
  if (r) op_cache_put(OP_INFER, m, key_tpl, depth, 0, r);
  return r;
}

static bool check_proposition(uint32_t depth, Term tpl, Term m) {
  while (m) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(m, &k, &h, &ar, &a);
    if ((int)h != C_TM_TALL) break;
    m = a[0];
    depth++;
    tpl = T_TPLN;
  }
  return infer_term(depth, tpl, m) == T_TP_PROP;
}

/* ---- Lazy WHNF & Conversion (beta-delta-eta) ---- */
typedef struct {
  Term arg;
  bool is_type;
} SpineArg;

typedef struct {
  SpineArg *args;
  uint32_t len, cap;
  Term head;
} Spine;

static void spine_of(Spine *sp, Term m) {
  uint32_t n = 0;
  for (Term t = m;;) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(t, &k, &h, &ar, &a);
    if ((int)h != C_TM_AP && (int)h != C_TM_TAP) break;
    t = a[0];
    n++;
  }
  if (n > sp->cap) {
    sp->args = realloc(sp->args, (size_t)n * sizeof(SpineArg));
    sp->cap = n;
  }
  sp->len = n;
  Term t = m;
  for (uint32_t i = n; i > 0; i--) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(t, &k, &h, &ar, &a);
    sp->args[i - 1] = (SpineArg){ a[1], (int)h == C_TM_TAP };
    t = a[0];
  }
  sp->head = t;
}

static Term spine_build(Term head, const SpineArg *args, uint32_t from, uint32_t to) {
  Term m = head;
  for (uint32_t i = from; i < to; i++) {
    m = args[i].is_type ? mk_tm_tap(m, args[i].arg) : mk_tm_ap(m, args[i].arg);
  }
  return m;
}

static uint32_t defined_head_sym(Term head) {
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(head, &k, &h, &ar, &a);
  if ((int)h != C_TM_NAME) return 0;
  uint32_t id = meta_of(a[0])->uval;
  return (id <= nsyms && syms[id].has_term && syms[id].def) ? id : 0;
}

static uint32_t head_def_sym(Term m) {
  for (;;) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(m, &k, &h, &ar, &a);
    if ((int)h != C_TM_AP && (int)h != C_TM_TAP) return defined_head_sym(m);
    m = a[0];
  }
}

static Term whnf_beta(Term m) {
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  if ((int)h != C_TM_AP && (int)h != C_TM_TAP) return m;
  Spine sp = {0};
  for (;;) {
    tc_node(m, &k, &h, &ar, &a);
    if ((int)h != C_TM_AP && (int)h != C_TM_TAP) break;
    spine_of(&sp, m);
    tc_node(sp.head, &k, &h, &ar, &a);
    Term red = 0;
    if ((int)h == C_TM_LAM && !sp.args[0].is_type)
      red = tm_instantiate(a[1], 0, sp.args[0].arg);
    else if ((int)h == C_TM_TLAM && sp.args[0].is_type)
      red = tm_tinstantiate(a[0], 0, sp.args[0].arg);
    else
      break;
    m = spine_build(red, sp.args, 1, sp.len);
  }
  free(sp.args);
  return m;
}

static Term unfold_head(Term m) {
  Spine sp = {0};
  spine_of(&sp, m);
  uint32_t id = defined_head_sym(sp.head);
  Term r = id ? spine_build(syms[id].def, sp.args, 0, sp.len) : 0;
  free(sp.args);
  return r;
}

static Term mg_whnf(Term m) {
  for (;;) {
    m = whnf_beta(m);
    if (!head_def_sym(m)) return m;
    m = unfold_head(m);
  }
}

static bool is_structure_con(int hc) {
  return hc == C_TM_LAM || hc == C_TM_ALL || hc == C_TM_IMP ||
         hc == C_TM_TLAM || hc == C_TM_TALL;
}

typedef struct {
  Term a, b;
  uint8_t res; /* 1 = equal, 2 = not equal */
} ConvSlot;

typedef struct {
  ConvSlot *slots;
  size_t cap, len;
} ConvMemo;

static size_t conv_slot_idx(Term a, Term b, size_t cap) {
  uint64_t h = (uint64_t)a * 0x9e3779b97f4a7c15ULL ^
               (uint64_t)b * 0xc2b2ae3d27d4eb4fULL;
  h ^= h >> 29;
  return (size_t)h & (cap - 1u);
}

static uint8_t conv_memo_get(const ConvMemo *cm, Term a, Term b) {
  if (!cm->cap) return 0;
  for (size_t i = conv_slot_idx(a, b, cm->cap);; i = (i + 1) & (cm->cap - 1)) {
    if (!cm->slots[i].a) return 0;
    if (cm->slots[i].a == a && cm->slots[i].b == b) return cm->slots[i].res;
  }
}

static void conv_memo_put(ConvMemo *cm, Term a, Term b, bool eq) {
  if ((cm->len + 1) * 2 > cm->cap) {
    size_t nc = cm->cap ? cm->cap * 2 : 256;
    ConvSlot *ns = calloc(nc, sizeof(ConvSlot));
    for (size_t j = 0; j < cm->cap; j++) {
      if (!cm->slots[j].a) continue;
      size_t k = conv_slot_idx(cm->slots[j].a, cm->slots[j].b, nc);
      while (ns[k].a) k = (k + 1) & (nc - 1);
      ns[k] = cm->slots[j];
    }
    free(cm->slots);
    cm->slots = ns;
    cm->cap = nc;
  }
  size_t i = conv_slot_idx(a, b, cm->cap);
  while (cm->slots[i].a) i = (i + 1) & (cm->cap - 1);
  cm->slots[i] = (ConvSlot){ a, b, (uint8_t)(eq ? 1 : 2) };
  cm->len++;
}

static bool conv_rec(ConvMemo *cm, Term a, Term b) {
  if (a == b) return true;
  uint8_t hit = conv_memo_get(cm, a, b);
  if (hit) return hit == 1;
  Term key_a = a, key_b = b;
  bool result = false;
  for (;;) {
    a = whnf_beta(a);
    b = whnf_beta(b);
    if (a == b) { result = true; break; }
    uint8_t ak, bk; uint32_t ah, bh; int aar, bar; const Term *aa, *ba;
    tc_node(a, &ak, &ah, &aar, &aa);
    Term a0 = aar > 0 ? aa[0] : 0, a1 = aar > 1 ? aa[1] : 0;
    tc_node(b, &bk, &bh, &bar, &ba);
    Term b0 = bar > 0 ? ba[0] : 0, b1 = bar > 1 ? ba[1] : 0;
    int ha = (int)ah, hb = (int)bh;
    if (ha == C_TM_LAM && hb == C_TM_LAM) {
      result = (a0 == b0) && conv_rec(cm, a1, b1);
      break;
    }
    if (ha == C_TM_TLAM && hb == C_TM_TLAM) {
      result = conv_rec(cm, a0, b0);
      break;
    }
    if (ha == C_TM_LAM || hb == C_TM_LAM || ha == C_TM_TLAM || hb == C_TM_TLAM) {
      bool left = (ha == C_TM_LAM || ha == C_TM_TLAM);
      int hlam = left ? ha : hb;
      int hother = left ? hb : ha;
      Term lam_body = left ? (ha == C_TM_LAM ? a1 : a0) : (hb == C_TM_LAM ? b1 : b0);
      Term other = left ? b : a;
      if (is_structure_con(hother)) break;
      Term app = (hlam == C_TM_LAM)
                   ? mk_tm_ap(tm_shift(other, 0, 1), mk_tm_db(0))
                   : mk_tm_tap(tm_tshift(other, 0, 1), mk_tp_var(0));
      result = conv_rec(cm, lam_body, app);
      break;
    }
    bool sa = is_structure_con(ha), sb = is_structure_con(hb);
    if (sa && sb) {
      if (ha != hb) break;
      if (ha == C_TM_ALL) result = (a0 == b0) && conv_rec(cm, a1, b1);
      else if (ha == C_TM_IMP) result = conv_rec(cm, a0, b0) && conv_rec(cm, a1, b1);
      else if (ha == C_TM_TALL) result = conv_rec(cm, a0, b0);
      break;
    }
    if (sa || sb) {
      Term neutral = sa ? b : a;
      if (!head_def_sym(neutral)) break;
      Term u = unfold_head(neutral);
      if (sa) b = u; else a = u;
      continue;
    }
    Spine sx = {0}, sy = {0};
    spine_of(&sx, a);
    spine_of(&sy, b);
    bool same_args = (sx.head == sy.head && sx.len == sy.len);
    for (uint32_t i = 0; same_args && i < sx.len; i++) {
      if (sx.args[i].is_type != sy.args[i].is_type) same_args = false;
      else if (sx.args[i].is_type) same_args = (sx.args[i].arg == sy.args[i].arg);
      else same_args = conv_rec(cm, sx.args[i].arg, sy.args[i].arg);
    }
    uint32_t da = defined_head_sym(sx.head);
    uint32_t db = defined_head_sym(sy.head);
    free(sx.args);
    free(sy.args);
    if (same_args) { result = true; break; }
    if (!da && !db) break;
    if (da && db) {
      if (da == db) { a = unfold_head(a); b = unfold_head(b); }
      else if (syms[da].term_seq >= syms[db].term_seq) a = unfold_head(a);
      else b = unfold_head(b);
    } else if (da) {
      a = unfold_head(a);
    } else {
      b = unfold_head(b);
    }
  }
  conv_memo_put(cm, key_a, key_b, result);
  return result;
}

static bool mg_conv(Term a, Term b) {
  if (a == b) return true;
  ConvMemo cm = {0};
  bool r = conv_rec(&cm, a, b);
  free(cm.slots);
  return r;
}

/* ---- Proof AST ---- */
enum {
  PF_GPA = 1, PF_HYP, PF_KNOWN, PF_TMAP, PF_PFAP,
  PF_PLAM, PF_TLAM, PF_TPAP, PF_TPLAM
};
typedef struct MgPf {
  uint8_t tag;
  uint32_t n;       /* HYP index or KNOWN/GPA sym id */
  struct MgPf *p, *q;
  Term t;           /* TMAP arg or PLAM source prop */
  Term tp;          /* TLAM type or TPAP type */
} MgPf;

typedef struct PfChunk {
  struct PfChunk *next;
  size_t used;
  MgPf nodes[4096];
} PfChunk;

static PfChunk *pf_chunks;

static MgPf *alloc_pf(uint8_t tag) {
  if (!pf_chunks || pf_chunks->used == 4096) {
    PfChunk *c = calloc(1, sizeof(PfChunk));
    c->next = pf_chunks;
    pf_chunks = c;
  }
  MgPf *p = &pf_chunks->nodes[pf_chunks->used++];
  p->tag = tag;
  return p;
}

static void free_pf_chunks(void) {
  while (pf_chunks) {
    PfChunk *n = pf_chunks->next;
    free(pf_chunks);
    pf_chunks = n;
  }
}

/* ---- Firing the 8 Megalodon rules on tcalc ---- */
typedef struct {
  const MgPf *pf;
  Term ctx;
  Term prop;
  Occ  occ;
} PfMemoSlot;

typedef struct {
  PfMemoSlot *slots;
  size_t cap, len;
} PfMemo;

static size_t pf_memo_idx(const MgPf *pf, Term ctx, size_t cap) {
  uint64_t h = (uint64_t)(uintptr_t)pf * 0x9e3779b97f4a7c15ULL ^
               (uint64_t)ctx * 0xc2b2ae3d27d4eb4fULL;
  h ^= h >> 29;
  return (size_t)h & (cap - 1u);
}

static const PfMemoSlot *pf_memo_get(const PfMemo *pm, const MgPf *pf, Term ctx) {
  if (!pm->cap) return NULL;
  for (size_t i = pf_memo_idx(pf, ctx, pm->cap);; i = (i + 1) & (pm->cap - 1)) {
    if (!pm->slots[i].pf) return NULL;
    if (pm->slots[i].pf == pf && pm->slots[i].ctx == ctx) return &pm->slots[i];
  }
}

static void pf_memo_put(PfMemo *pm, const MgPf *pf, Term ctx, Term prop, Occ occ) {
  if ((pm->len + 1) * 2 > pm->cap) {
    size_t nc = pm->cap ? pm->cap * 2 : 256;
    PfMemoSlot *ns = calloc(nc, sizeof(PfMemoSlot));
    for (size_t j = 0; j < pm->cap; j++) {
      if (!pm->slots[j].pf) continue;
      size_t k = pf_memo_idx(pm->slots[j].pf, pm->slots[j].ctx, nc);
      while (ns[k].pf) k = (k + 1) & (nc - 1);
      ns[k] = pm->slots[j];
    }
    free(pm->slots);
    pm->slots = ns;
    pm->cap = nc;
  }
  size_t i = pf_memo_idx(pf, ctx, pm->cap);
  while (pm->slots[i].pf) i = (i + 1) & (pm->cap - 1);
  pm->slots[i] = (PfMemoSlot){ pf, ctx, prop, occ };
  pm->len++;
}

static uint64_t stat_rule_fires[9];

static inline Occ commit_mg_step(int rule, const Occ *keep, const Term *inst) {
  TcPreparedStep step = { .rule = rule, .keep = keep, .inst = inst };
  TcAdmissionReceipt rec;
  return tc_commit_prepared(&step, &rec) ? rec.out : 0;
}

static Occ check_pf_rec(PfMemo *pm, Term ctx, const MgPf *pf, Term *out_prop) {
  *out_prop = 0;
  if (!pf) return 0;
  const PfMemoSlot *hit = pf_memo_get(pm, pf, ctx);
  if (hit) {
    *out_prop = hit->prop;
    return hit->occ;
  }
  uint32_t depth; Term tpl, tml;
  unpack_ctx(ctx, &depth, &tpl, &tml);
  Occ res_occ = 0;
  Term res_prop = 0;

  switch (pf->tag) {
  case PF_GPA:
    /* Automation placeholder is never a valid proof */
    return 0;

  case PF_HYP: {
    Term h = list_nth(tml, C_TMLC, pf->n);
    if (!h) return 0;
    Term idx_t = mk_int(pf->n);
    Term ca[3] = { ctx, idx_t, h };
    Occ cert = tc_post(SPACE_REL, tc_app(C_HYP_CERT, ca));
    Occ keep[1] = { cert };
    Term inst[3] = { ctx, idx_t, h };
    res_occ = commit_mg_step(R_HYP, keep, inst);
    if (res_occ) { res_prop = h; stat_rule_fires[1]++; }
    break;
  }

  case PF_KNOWN: {
    if (pf->n == 0 || pf->n > nsyms || !syms[pf->n].has_known) return 0;
    Term p = syms[pf->n].prop;
    Term nt = syms[pf->n].nterm;
    Term ca[3] = { ctx, nt, p };
    Occ cert = tc_post(SPACE_REL, tc_app(C_KNOWN_CERT, ca));
    Occ keep[2] = { syms[pf->n].known_occ, cert };
    Term inst[4] = { T_CTX_EMPTY, ctx, nt, p };
    res_occ = commit_mg_step(R_KNOWN, keep, inst);
    if (res_occ) { res_prop = p; stat_rule_fires[2]++; }
    break;
  }

  case PF_TMAP: {
    Term qprop = 0;
    Occ qocc = check_pf_rec(pm, ctx, pf->p, &qprop);
    if (!qocc) return 0;
    Term h = mg_whnf(qprop);
    uint8_t hk; uint32_t hh; int har; const Term *ha;
    tc_node(h, &hk, &hh, &har, &ha);
    if ((int)hh != C_TM_ALL) return 0;
    Term dom_tp = ha[0], body = ha[1];
    Term actual_tp = infer_term(depth, tpl, pf->t);
    if (actual_tp != dom_tp) return 0;
    Term concl = tm_instantiate(body, 0, pf->t);
    Term ca[4] = { ctx, qprop, pf->t, concl };
    Occ cert = tc_post(SPACE_REL, tc_app(C_TERM_APP_CERT, ca));
    Occ keep[2] = { qocc, cert };
    Term inst[4] = { ctx, qprop, pf->t, concl };
    res_occ = commit_mg_step(R_TERM_APP, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[3]++; }
    break;
  }

  case PF_PFAP: {
    Term iprop = 0;
    Occ iocc = check_pf_rec(pm, ctx, pf->p, &iprop);
    if (!iocc) return 0;
    Term h = mg_whnf(iprop);
    uint8_t hk; uint32_t hh; int har; const Term *ha;
    tc_node(h, &hk, &hh, &har, &ha);
    if ((int)hh != C_TM_IMP) return 0;
    Term dom = ha[0], concl = ha[1];
    Term aprop = 0;
    Occ aocc = check_pf_rec(pm, ctx, pf->q, &aprop);
    if (!aocc) return 0;
    if (!mg_conv(aprop, dom)) return 0;
    Term ca[4] = { ctx, iprop, aprop, concl };
    Occ cert = tc_post(SPACE_REL, tc_app(C_PROOF_APP_CERT, ca));
    Occ keep[3] = { iocc, aocc, cert };
    Term inst[4] = { ctx, iprop, aprop, concl };
    res_occ = commit_mg_step(R_PROOF_APP, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[4]++; }
    break;
  }

  case PF_TLAM: {
    if (!tp_plain_wf(pf->tp, depth)) return 0;
    Term inner = mk_ctx(depth, mk_tplc(pf->tp, tpl), tml_shift1(tml));
    Term bprop = 0;
    Occ bocc = check_pf_rec(pm, inner, pf->p, &bprop);
    if (!bocc) return 0;
    Term concl = mk_tm_all(pf->tp, bprop);
    Term ca[3] = { ctx, pf->tp, inner };
    Occ cert = tc_post(SPACE_REL, tc_app(C_TERM_LAM_CERT, ca));
    Occ keep[2] = { bocc, cert };
    Term inst[4] = { ctx, pf->tp, inner, bprop };
    res_occ = commit_mg_step(R_TERM_LAM, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[5]++; }
    break;
  }

  case PF_PLAM: {
    if (infer_term(depth, tpl, pf->t) != T_TP_PROP) return 0;
    Term inner = mk_ctx(depth, tpl, mk_tmlc(pf->t, tml));
    Term bprop = 0;
    Occ bocc = check_pf_rec(pm, inner, pf->p, &bprop);
    if (!bocc) return 0;
    Term concl = mk_tm_imp(pf->t, bprop);
    Term ca[3] = { ctx, pf->t, inner };
    Occ cert = tc_post(SPACE_REL, tc_app(C_PROOF_LAM_CERT, ca));
    Occ keep[2] = { bocc, cert };
    Term inst[4] = { ctx, pf->t, inner, bprop };
    res_occ = commit_mg_step(R_PROOF_LAM, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[6]++; }
    break;
  }

  case PF_TPAP: {
    if (!tp_plain_wf(pf->tp, depth)) return 0;
    Term qprop = 0;
    Occ qocc = check_pf_rec(pm, ctx, pf->p, &qprop);
    if (!qocc) return 0;
    Term h = mg_whnf(qprop);
    uint8_t hk; uint32_t hh; int har; const Term *ha;
    tc_node(h, &hk, &hh, &har, &ha);
    if ((int)hh != C_TM_TALL) return 0;
    Term body = ha[0];
    Term concl = tm_tinstantiate(body, 0, pf->tp);
    Term ca[4] = { ctx, qprop, pf->tp, concl };
    Occ cert = tc_post(SPACE_REL, tc_app(C_TYPE_APP_CERT, ca));
    Occ keep[2] = { qocc, cert };
    Term inst[4] = { ctx, qprop, pf->tp, concl };
    res_occ = commit_mg_step(R_TYPE_APP, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[7]++; }
    break;
  }

  case PF_TPLAM: {
    if (tpl != T_TPLN || tml != T_TMLN) return 0;
    Term inner = mk_ctx(depth + 1u, T_TPLN, T_TMLN);
    Term bprop = 0;
    Occ bocc = check_pf_rec(pm, inner, pf->p, &bprop);
    if (!bocc) return 0;
    Term concl = mk_tm_tall(bprop);
    Term ca[2] = { ctx, inner };
    Occ cert = tc_post(SPACE_REL, tc_app(C_TYPE_LAM_CERT, ca));
    Occ keep[2] = { bocc, cert };
    Term inst[3] = { ctx, inner, bprop };
    res_occ = commit_mg_step(R_TYPE_LAM, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[8]++; }
    break;
  }
  }

  if (res_occ && res_prop) {
    pf_memo_put(pm, pf, ctx, res_prop, res_occ);
    *out_prop = res_prop;
  }
  return res_occ;
}

static Occ check_proof_tree(Term ctx, const MgPf *pf, Term *out_prop) {
  PfMemo pm = {0};
  Occ o = check_pf_rec(&pm, ctx, pf, out_prop);
  free(pm.slots);
  return o;
}

/* ---- Initialize tcalc sorts, constructors, and sealed rules ---- */
static void init_mg_kernel(int profile) {
  tc_init(1u << 23, 1u << 22);
  memset(op_cache, 0, sizeof(op_cache));
  memset(stat_rule_fires, 0, sizeof(stat_rule_fires));
  free(NMETA); NMETA = NULL; nmeta_cap = 0;
  free(int_terms); int_terms = NULL; int_terms_cap = 0;
  for (uint32_t i = 1; i <= nsyms; i++) free(syms[i].text);
  free(syms); syms = NULL; nsyms = capsyms = 0;
  free(sym_tab); sym_tab = NULL; sym_tab_cap = 0;
  next_decl_seq = 1;
  T_TP_PROP = T_TP_SET = T_TPLN = T_TMLN = T_CTX_EMPTY = 0;

  S_INT    = tc_sort(SORT_PURE | SORT_FREE);
  S_NAME   = tc_sort(SORT_PURE | SORT_FREE);
  S_TP     = tc_sort(0);
  S_TM     = tc_sort(0);
  S_TPL    = tc_sort(0);
  S_TML    = tc_sort(0);
  S_CTX    = tc_sort(0);
  S_CERT   = tc_sort(SORT_PROVABLE);
  S_THM    = tc_sort(SORT_PROVABLE);
  S_HANDLE = tc_sort(0);
  uint16_t sp_sort = tc_space_sort();

  Binder b_int[1] = { { (uint16_t)S_INT, 0, 0 } };
  Binder b_nam[1] = { { (uint16_t)S_NAME, 0, 0 } };
  Binder b_tp1[1] = { { (uint16_t)S_TP, 0, 0 } };
  Binder b_tp2[2] = { { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TP, 0, 0 } };
  Binder b_tm1[1] = { { (uint16_t)S_TM, 0, 0 } };
  Binder b_tm2[2] = { { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
  Binder b_tptm[2] = { { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
  Binder b_tmtp[2] = { { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TP, 0, 0 } };

  C_TP_PROP = tc_con((uint16_t)S_TP, 0, 0, NULL);
  C_TP_BASE = tc_con((uint16_t)S_TP, 0, 1, b_int);
  C_TP_VAR  = tc_con((uint16_t)S_TP, 0, 1, b_int);
  C_TP_ARR  = tc_con((uint16_t)S_TP, 0, 2, b_tp2);
  C_TP_ALL  = tc_con((uint16_t)S_TP, 0, 1, b_tp1);

  C_TM_DB   = tc_con((uint16_t)S_TM, 0, 1, b_int);
  C_TM_NAME = tc_con((uint16_t)S_TM, 0, 1, b_nam);
  C_TM_PRIM = tc_con((uint16_t)S_TM, 0, 1, b_int);
  C_TM_AP   = tc_con((uint16_t)S_TM, 0, 2, b_tm2);
  C_TM_LAM  = tc_con((uint16_t)S_TM, 0, 2, b_tptm);
  C_TM_IMP  = tc_con((uint16_t)S_TM, 0, 2, b_tm2);
  C_TM_ALL  = tc_con((uint16_t)S_TM, 0, 2, b_tptm);
  C_TM_TAP  = tc_con((uint16_t)S_TM, 0, 2, b_tmtp);
  C_TM_TLAM = tc_con((uint16_t)S_TM, 0, 1, b_tm1);
  C_TM_TALL = tc_con((uint16_t)S_TM, 0, 1, b_tm1);

  Binder b_tplc[2] = { { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TPL, 0, 0 } };
  Binder b_tmlc[2] = { { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TML, 0, 0 } };
  Binder b_ctx[3]  = {
    { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 }, { (uint16_t)S_TML, 0, 0 }
  };
  C_TPLN = tc_con((uint16_t)S_TPL, 0, 0, NULL);
  C_TPLC = tc_con((uint16_t)S_TPL, 0, 2, b_tplc);
  C_TMLN = tc_con((uint16_t)S_TML, 0, 0, NULL);
  C_TMLC = tc_con((uint16_t)S_TML, 0, 2, b_tmlc);
  C_CTX  = tc_con((uint16_t)S_CTX, 0, 3, b_ctx);

  Binder b_thm[2] = { { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
  C_THM = tc_con((uint16_t)S_THM, 0, 2, b_thm);

  Binder b_hyp_cert[3] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_known_cert[3] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_tmap_cert[4] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
    { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_pfap_cert[4] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
    { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_tlam_cert[3] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_CTX, 0, 0 }
  };
  Binder b_plam_cert[3] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_CTX, 0, 0 }
  };
  Binder b_tpap_cert[4] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
    { (uint16_t)S_TP, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_tplam_cert[2] = {
    { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_CTX, 0, 0 }
  };
  C_HYP_CERT        = tc_con((uint16_t)S_CERT, 0, 3, b_hyp_cert);
  C_KNOWN_CERT      = tc_con((uint16_t)S_CERT, 0, 3, b_known_cert);
  C_TERM_APP_CERT   = tc_con((uint16_t)S_CERT, 0, 4, b_tmap_cert);
  C_PROOF_APP_CERT  = tc_con((uint16_t)S_CERT, 0, 4, b_pfap_cert);
  C_TERM_LAM_CERT   = tc_con((uint16_t)S_CERT, 0, 3, b_tlam_cert);
  C_PROOF_LAM_CERT  = tc_con((uint16_t)S_CERT, 0, 3, b_plam_cert);
  C_TYPE_APP_CERT   = tc_con((uint16_t)S_CERT, 0, 4, b_tpap_cert);
  C_TYPE_LAM_CERT   = tc_con((uint16_t)S_CERT, 0, 2, b_tplam_cert);
  C_THM_IMPORT_CERT = tc_con((uint16_t)S_CERT, 0, 2, b_tm2);
  C_AXIOM_CERT      = tc_con((uint16_t)S_CERT, 0, 1, b_tm1);

  /* NamedSpaces / SpacesCreation / NamedSpacesReach subproof constructors */
  Binder b_sp[1] = { { sp_sort, 0, 0 } };
  C_HANDLE   = tc_con((uint16_t)S_HANDLE, 0, 1, b_sp);
  C_SUB_MARK = tc_con((uint16_t)S_CERT, 0, 1, b_sp);
  C_SUB_HYP  = tc_con((uint16_t)S_CERT, 0, 2, b_thm);
  C_SUB_AUTH = tc_con((uint16_t)S_CERT, 0, 2, b_thm);
  tc_set_handle_con(C_HANDLE);

  T_TP_PROP   = tc_app(C_TP_PROP, NULL);
  meta_of(T_TP_PROP)->init = 1;
  meta_of(T_TP_PROP)->plain = 1;
  T_TPLN      = tc_app(C_TPLN, NULL);
  T_TMLN      = tc_app(C_TMLN, NULL);
  Term a_empty[3] = { mk_int(0), T_TPLN, T_TMLN };
  T_CTX_EMPTY = tc_app(C_CTX, a_empty);

  init_profile_prims(profile);

  /* Install the 8 Megalodon rules + top-level admission + subproof space rules */
  {
    /* 1. R_HYP: keep HYP_CERT(ctx, idx, prop) |- THM(ctx, prop) */
    Binder v[3] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term ca[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term ja[2] = { tc_v(0), tc_v(2) };
    Rule r = { .nkeep = 1, .fresh = -1,
               .keep = { { tc_app(C_HYP_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_THM, ja), SPACE_THM } };
    R_HYP = tc_rule(&r);
  }
  {
    /* 2. R_KNOWN: keep THM(ctx0, prop), KNOWN_CERT(ctx, name, prop) |- THM(ctx, prop) */
    Binder v[4] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_CTX, 0, 0 },
      { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term j0[2] = { tc_v(0), tc_v(3) };
    Term ca[3] = { tc_v(1), tc_v(2), tc_v(3) };
    Term j1[2] = { tc_v(1), tc_v(3) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_KNOWN_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_KNOWN = tc_rule(&r);
  }
  {
    /* 3. R_TERM_APP: keep THM(ctx, qprop), TERM_APP_CERT(ctx, qprop, arg, concl) |- THM(ctx, concl) */
    Binder v[4] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term j0[2] = { tc_v(0), tc_v(1) };
    Term ca[4] = { tc_v(0), tc_v(1), tc_v(2), tc_v(3) };
    Term j1[2] = { tc_v(0), tc_v(3) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_TERM_APP_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_TERM_APP = tc_rule(&r);
  }
  {
    /* 4. R_PROOF_APP: keep THM(ctx, iprop), THM(ctx, aprop), PROOF_APP_CERT(ctx, iprop, aprop, concl) |- THM(ctx, concl) */
    Binder v[4] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term j0[2] = { tc_v(0), tc_v(1) };
    Term j1[2] = { tc_v(0), tc_v(2) };
    Term ca[4] = { tc_v(0), tc_v(1), tc_v(2), tc_v(3) };
    Term j2[2] = { tc_v(0), tc_v(3) };
    Rule r = { .nkeep = 3, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_THM, j1), SPACE_THM },
                         { tc_app(C_PROOF_APP_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_THM, j2), SPACE_THM } };
    R_PROOF_APP = tc_rule(&r);
  }
  {
    /* 5. R_TERM_LAM: keep THM(inner, body), TERM_LAM_CERT(ctx, tp, inner) |- THM(ctx, All(tp, body)) */
    Binder v[4] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TP, 0, 0 },
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term j0[2] = { tc_v(2), tc_v(3) };
    Term ca[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term al[2] = { tc_v(1), tc_v(3) };
    Term j1[2] = { tc_v(0), tc_app(C_TM_ALL, al) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_TERM_LAM_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_TERM_LAM = tc_rule(&r);
  }
  {
    /* 6. R_PROOF_LAM: keep THM(inner, body), PROOF_LAM_CERT(ctx, src, inner) |- THM(ctx, Imp(src, body)) */
    Binder v[4] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term j0[2] = { tc_v(2), tc_v(3) };
    Term ca[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term im[2] = { tc_v(1), tc_v(3) };
    Term j1[2] = { tc_v(0), tc_app(C_TM_IMP, im) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_PROOF_LAM_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_PROOF_LAM = tc_rule(&r);
  }
  {
    /* 7. R_TYPE_APP: keep THM(ctx, qprop), TYPE_APP_CERT(ctx, qprop, tp, concl) |- THM(ctx, concl) */
    Binder v[4] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TP, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term j0[2] = { tc_v(0), tc_v(1) };
    Term ca[4] = { tc_v(0), tc_v(1), tc_v(2), tc_v(3) };
    Term j1[2] = { tc_v(0), tc_v(3) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_TYPE_APP_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_TYPE_APP = tc_rule(&r);
  }
  {
    /* 8. R_TYPE_LAM: keep THM(inner, body), TYPE_LAM_CERT(ctx, inner) |- THM(ctx, TAll(body)) */
    Binder v[3] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term j0[2] = { tc_v(1), tc_v(2) };
    Term ca[2] = { tc_v(0), tc_v(1) };
    Term ta[1] = { tc_v(2) };
    Term j1[2] = { tc_v(0), tc_app(C_TM_TALL, ta) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_TYPE_LAM_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_TYPE_LAM = tc_rule(&r);
  }
  {
    /* R_THM_IMPORT: keep THM(ctx0, inferred), THM_IMPORT_CERT(claim, inferred) |- THM(ctx0, claim) */
    Binder v[3] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term j0[2] = { tc_v(0), tc_v(2) };
    Term ca[2] = { tc_v(1), tc_v(2) };
    Term j1[2] = { tc_v(0), tc_v(1) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_THM_IMPORT_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_THM_IMPORT = tc_rule(&r);
  }
  {
    /* R_AXIOM: keep AXIOM_CERT(claim) |- THM(ctx0, claim) */
    Binder v[2] = { { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
    tc_ctx(2, v);
    Term ca[1] = { tc_v(1) };
    Term j1[2] = { tc_v(0), tc_v(1) };
    Rule r = { .nkeep = 1, .fresh = -1,
               .keep = { { tc_app(C_AXIOM_CERT, ca), SPACE_REL } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_AXIOM = tc_rule(&r);
  }
  {
    /* R_SUB_BIRTH (SpacesCreation + NamedSpaces):
       births subproof space s, posts birth marker SUB_MARK(s) at s,
       posts SUB_HYP(ctx, h) at s, and returns HANDLE(s) in SPACE_REL. */
    Binder v[3] = {
      { sp_sort, 0, 0 }, { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term s = tc_v(0), ctx = tc_v(1), h = tc_v(2);
    Term sa[1] = { s };
    Term ha[2] = { ctx, h };
    Rule r = {
      .nkeep = 1, .nmake_extra = 2, .birth_law = 1, .fresh = -1,
      .keep = { { tc_app(C_SUB_AUTH, ha), SPACE_REL } },
      .make = { tc_app(C_HANDLE, sa), SPACE_REL },
      .make_extra = {
        { tc_at_birth(s, tc_app(C_SUB_MARK, sa)), 0 },
        { tc_at_space(s, tc_app(C_SUB_HYP, ha)), 0 }
      }
    };
    R_SUB_BIRTH = tc_rule(&r);
  }
  {
    /* R_SUB_USE_HYP (NamedSpacesReach):
       reads SUB_HYP(ctx, h) at dynamic subproof space s (requires s in Reach(seeds))
       and produces THM(ctx, h) in SPACE_THM. */
    Binder v[3] = {
      { sp_sort, 0, 0 }, { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term s = tc_v(0), ctx = tc_v(1), h = tc_v(2);
    Term ha[2] = { ctx, h };
    Rule r = {
      .birth_law = 1, .nkeep = 1, .fresh = -1,
      .keep = { { tc_at_space(s, tc_app(C_SUB_HYP, ha)), 0 } },
      .make = { tc_app(C_THM, ha), SPACE_THM }
    };
    R_SUB_USE_HYP = tc_rule(&r);
  }

  /* Post birth markers for static spaces SPACE_REL and SPACE_THM so birth_law
     rules can read/write them alongside dynamic subproof spaces. */
  Term sp_rel = tc_space_term(SPACE_REL);
  Term sp_thm = tc_space_term(SPACE_THM);
  Term m_rel[1] = { sp_rel };
  Term m_thm[1] = { sp_thm };
  tc_post_at(sp_rel, tc_app(C_SUB_MARK, m_rel), true);
  tc_post_at(sp_thm, tc_app(C_SUB_MARK, m_thm), true);

  tc_protect(SPACE_THM);
  tc_seal();
}

/* ---- S-expression parser for -sexprinfo files ---- */
enum { SX_ATOM = 1, SX_STR, SX_INT, SX_LIST };
typedef struct Sx {
  uint8_t kind;
  uint32_t len;
  uint64_t val;
  const char *text; /* points into file buffer (null-terminated in place) */
  struct Sx **items;
} Sx;

typedef struct SxChunk {
  struct SxChunk *next;
  size_t used;
  Sx nodes[8192];
} SxChunk;

typedef struct PtrChunk {
  struct PtrChunk *next;
  size_t used;
  Sx *ptrs[32768];
} PtrChunk;

static SxChunk *sx_chunks;
static PtrChunk *ptr_chunks;

static Sx *alloc_sx(uint8_t kind) {
  if (!sx_chunks || sx_chunks->used == 8192) {
    SxChunk *c = calloc(1, sizeof(SxChunk));
    c->next = sx_chunks;
    sx_chunks = c;
  }
  Sx *s = &sx_chunks->nodes[sx_chunks->used++];
  s->kind = kind;
  return s;
}

static Sx **alloc_ptrs(uint32_t n) {
  if (!n) return NULL;
  if (n > 32768) return malloc((size_t)n * sizeof(Sx *));
  if (!ptr_chunks || ptr_chunks->used + n > 32768) {
    PtrChunk *c = calloc(1, sizeof(PtrChunk));
    c->next = ptr_chunks;
    ptr_chunks = c;
  }
  Sx **p = &ptr_chunks->ptrs[ptr_chunks->used];
  ptr_chunks->used += n;
  return p;
}

static void free_sx_arena(void) {
  while (sx_chunks) {
    SxChunk *n = sx_chunks->next;
    free(sx_chunks);
    sx_chunks = n;
  }
  while (ptr_chunks) {
    PtrChunk *n = ptr_chunks->next;
    free(ptr_chunks);
    ptr_chunks = n;
  }
}

static void skip_ws(char **p) {
  char *s = *p;
  for (;;) {
    while (*s && isspace((unsigned char)*s)) s++;
    if (*s == ';') {
      while (*s && *s != '\n') s++;
      continue;
    }
    break;
  }
  *p = s;
}

static Sx *parse_sx(char **p) {
  skip_ws(p);
  char *s = *p;
  if (!*s) return NULL;
  if (*s == '(') {
    s++;
    *p = s;
    Sx *tmp[256];
    Sx **dyn = NULL;
    uint32_t len = 0, cap = 256;
    for (;;) {
      skip_ws(p);
      if (!**p) { free(dyn); return NULL; }
      if (**p == ')') { (*p)++; break; }
      Sx *it = parse_sx(p);
      if (!it) { free(dyn); return NULL; }
      if (len == cap) {
        uint32_t nc = cap * 2;
        Sx **nd = malloc((size_t)nc * sizeof(Sx *));
        memcpy(nd, dyn ? dyn : tmp, (size_t)len * sizeof(Sx *));
        free(dyn);
        dyn = nd;
        cap = nc;
      }
      if (dyn) dyn[len++] = it;
      else tmp[len++] = it;
    }
    Sx *l = alloc_sx(SX_LIST);
    l->len = len;
    if (dyn) {
      l->items = dyn;
    } else {
      l->items = alloc_ptrs(len);
      if (len) memcpy(l->items, tmp, (size_t)len * sizeof(Sx *));
    }
    return l;
  }
  if (*s == '"') {
    s++;
    char *start = s, *w = s;
    while (*s && *s != '"') {
      if (*s == '\\' && s[1]) s++;
      *w++ = *s++;
    }
    if (*s == '"') s++;
    *w = '\0';
    *p = s;
    Sx *st = alloc_sx(SX_STR);
    st->text = start;
    st->len = (uint32_t)(w - start);
    return st;
  }
  char *start = s;
  while (*s && !isspace((unsigned char)*s) && *s != '(' && *s != ')' && *s != '"')
    s++;
  size_t len = (size_t)(s - start);
  bool all_digits = len > 0;
  uint64_t val = 0;
  for (size_t i = 0; i < len; i++) {
    if (start[i] < '0' || start[i] > '9') { all_digits = false; break; }
    val = val * 10u + (uint64_t)(start[i] - '0');
  }
  if (*s == ')' || *s == '(') {
    /* copy short atom or move? We can overwrite only if we save char, or we can
       check if we only need strncmp for atoms! Wait: for SX_ATOM we only ever
       compare against literal strings, so st->text + st->len is enough! */
  }
  *p = s;
  if (all_digits) {
    Sx *in = alloc_sx(SX_INT);
    in->val = val;
    return in;
  }
  Sx *at = alloc_sx(SX_ATOM);
  at->text = start;
  at->len = (uint32_t)len;
  return at;
}

static inline bool sx_is_atom(const Sx *x, const char *lit) {
  size_t n = strlen(lit);
  return x && x->kind == SX_ATOM && x->len == n && memcmp(x->text, lit, n) == 0;
}

/* ---- Decoding upstream types, terms, and proofs ---- */
static Term decode_tp(const Sx *x, uint32_t levels) {
  if (!x || x->kind != SX_LIST || x->len == 0) return 0;
  if (x->len == 1 && sx_is_atom(x->items[0], "PROP")) return mk_tp_prop();
  if (x->len == 1 && sx_is_atom(x->items[0], "SET")) return mk_tp_base(0);
  if (x->len == 2 && sx_is_atom(x->items[0], "TPVAR") && x->items[1]->kind == SX_INT) {
    uint64_t i = x->items[1]->val;
    return i < levels ? mk_tp_var(levels - (uint32_t)i - 1u) : 0;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "AR")) {
    Term a = decode_tp(x->items[1], levels);
    Term b = a ? decode_tp(x->items[2], levels) : 0;
    return b ? mk_tp_arr(a, b) : 0;
  }
  return 0;
}

static Term wrap_poly_tp(Term body, uint32_t levels) {
  for (uint32_t i = 0; body && i < levels; i++) body = mk_tp_all(body);
  return body;
}

static Term decode_tm(const Sx *x, uint32_t levels) {
  if (!x || x->kind != SX_LIST || x->len == 0) return 0;
  if (x->len == 2 && sx_is_atom(x->items[0], "DB") && x->items[1]->kind == SX_INT)
    return mk_tm_db((uint32_t)x->items[1]->val);
  if (x->len == 2 && sx_is_atom(x->items[0], "TMH") && x->items[1]->kind == SX_STR)
    return mk_tm_name(sym_intern_n(x->items[1]->text, x->items[1]->len));
  if (x->len == 2 && sx_is_atom(x->items[0], "PRIM") && x->items[1]->kind == SX_INT)
    return mk_tm_prim((uint32_t)x->items[1]->val);
  if (x->len == 3 && sx_is_atom(x->items[0], "TPAP")) {
    Term f = decode_tm(x->items[1], levels);
    Term a = f ? decode_tp(x->items[2], levels) : 0;
    return a ? mk_tm_tap(f, a) : 0;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "AP")) {
    Term f = decode_tm(x->items[1], levels);
    Term a = f ? decode_tm(x->items[2], levels) : 0;
    return a ? mk_tm_ap(f, a) : 0;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "LAM")) {
    Term a = decode_tp(x->items[1], levels);
    Term b = a ? decode_tm(x->items[2], levels) : 0;
    return b ? mk_tm_lam(a, b) : 0;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "IMP")) {
    Term a = decode_tm(x->items[1], levels);
    Term b = a ? decode_tm(x->items[2], levels) : 0;
    return b ? mk_tm_imp(a, b) : 0;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "ALL")) {
    Term a = decode_tp(x->items[1], levels);
    Term b = a ? decode_tm(x->items[2], levels) : 0;
    return b ? mk_tm_all(a, b) : 0;
  }
  return 0;
}

static Term wrap_poly_tm(Term body, uint32_t levels, bool is_lam) {
  for (uint32_t i = 0; body && i < levels; i++)
    body = is_lam ? mk_tm_tlam(body) : mk_tm_tall(body);
  return body;
}

static MgPf *decode_pf(const Sx *x, uint32_t levels) {
  if (!x || x->kind != SX_LIST || x->len == 0) return NULL;
  if (x->len == 2 && sx_is_atom(x->items[0], "HYP") && x->items[1]->kind == SX_INT) {
    MgPf *p = alloc_pf(PF_HYP);
    p->n = (uint32_t)x->items[1]->val;
    return p;
  }
  if (x->len == 2 && sx_is_atom(x->items[0], "KNOWN") && x->items[1]->kind == SX_STR) {
    MgPf *p = alloc_pf(PF_KNOWN);
    p->n = sym_intern_n(x->items[1]->text, x->items[1]->len);
    return p;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "PTPAP")) {
    MgPf *d = decode_pf(x->items[1], levels);
    Term a = d ? decode_tp(x->items[2], levels) : 0;
    if (!a) return NULL;
    MgPf *p = alloc_pf(PF_TPAP);
    p->p = d; p->tp = a;
    return p;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "PTMAP")) {
    MgPf *d = decode_pf(x->items[1], levels);
    Term a = d ? decode_tm(x->items[2], levels) : 0;
    if (!a) return NULL;
    MgPf *p = alloc_pf(PF_TMAP);
    p->p = d; p->t = a;
    return p;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "PPFAP")) {
    MgPf *d1 = decode_pf(x->items[1], levels);
    MgPf *d2 = d1 ? decode_pf(x->items[2], levels) : NULL;
    if (!d2) return NULL;
    MgPf *p = alloc_pf(PF_PFAP);
    p->p = d1; p->q = d2;
    return p;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "PLAM")) {
    Term s = decode_tm(x->items[1], levels);
    MgPf *d = s ? decode_pf(x->items[2], levels) : NULL;
    if (!d) return NULL;
    MgPf *p = alloc_pf(PF_PLAM);
    p->t = s; p->p = d;
    return p;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "TLAM")) {
    Term a = decode_tp(x->items[1], levels);
    MgPf *d = a ? decode_pf(x->items[2], levels) : NULL;
    if (!d) return NULL;
    MgPf *p = alloc_pf(PF_TLAM);
    p->tp = a; p->p = d;
    return p;
  }
  return NULL;
}

static MgPf *wrap_poly_pf(MgPf *pf, uint32_t levels) {
  for (uint32_t i = 0; pf && i < levels; i++) {
    MgPf *w = alloc_pf(PF_TPLAM);
    w->p = pf;
    pf = w;
  }
  return pf;
}

/* ---- Replay a Megalodon -sexprinfo file ---- */
typedef struct {
  uint32_t prims, params, defs, axioms, thms, repeated;
} ReplayStats;

static bool replay_sexpr_file(const char *path, ReplayStats *st) {
  FILE *f = fopen(path, "rb");
  if (!f) { fprintf(stderr, "mg_tcalc: cannot open %s\n", path); return false; }
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *buf = malloc((size_t)sz + 1);
  if ((long)fread(buf, 1, (size_t)sz, f) != sz) {
    fclose(f); free(buf); return false;
  }
  fclose(f);
  buf[sz] = '\0';

  char *cur = buf;
  bool ok = true;
  bool pending = false;
  uint32_t pending_sym = 0, pending_levels = 0;
  Term pending_prop = 0;
  const char *pending_name = "";

  while (ok) {
    skip_ws(&cur);
    if (!*cur) break;
    Sx *x = parse_sx(&cur);
    if (!x || x->kind != SX_LIST || x->len == 0) {
      fprintf(stderr, "mg_tcalc: malformed top-level S-expression in %s\n", path);
      ok = false; break;
    }
    const Sx *hd = x->items[0];
    if (sx_is_atom(hd, "PRIM") && x->len == 6) {
      uint32_t j = (uint32_t)x->items[1]->val;
      const char *name = x->items[2]->text;
      uint32_t h = sym_intern_n(x->items[3]->text, x->items[3]->len);
      if (j >= nprims || !prim_types[j]) {
        fprintf(stderr, "mg_tcalc: PRIM %s index %u out of range\n", name, j);
        ok = false; break;
      }
      uint32_t lv = 0;
      for (Term t = prim_types[j];;) {
        uint8_t tk; uint32_t th; int tar; const Term *ta;
        tc_node(t, &tk, &th, &tar, &ta);
        if ((int)th != C_TP_ALL) break;
        t = ta[0]; lv++;
      }
      Term tp = wrap_poly_tp(decode_tp(x->items[4], lv), lv);
      if (tp != prim_types[j]) {
        fprintf(stderr, "mg_tcalc: PRIM %s type mismatch\n", name);
        ok = false; break;
      }
      Term body = mk_tm_prim(j);
      if (syms[h].has_term) {
        if (syms[h].tp == tp && syms[h].def == body) { st->repeated++; }
        else { ok = false; break; }
      } else {
        syms[h].has_term = true;
        syms[h].tp = tp;
        syms[h].def = body;
        syms[h].term_seq = next_decl_seq++;
        st->prims++;
      }
    } else if (sx_is_atom(hd, "PARAM") && x->len == 6) {
      const char *name = x->items[1]->text;
      uint32_t h = sym_intern_n(x->items[2]->text, x->items[2]->len);
      uint32_t lv = (uint32_t)x->items[3]->val;
      Term body_tp = decode_tp(x->items[4], lv);
      if (!body_tp || !tp_plain_wf(body_tp, lv)) {
        fprintf(stderr, "mg_tcalc: PARAM %s ill-formed type\n", name);
        ok = false; break;
      }
      Term tp = wrap_poly_tp(body_tp, lv);
      if (syms[h].has_term) {
        if (syms[h].tp == tp) st->repeated++;
        else { ok = false; break; }
      } else {
        syms[h].has_term = true;
        syms[h].is_param = true;
        syms[h].tp = tp;
        syms[h].def = 0;
        syms[h].term_seq = next_decl_seq++;
        st->params++;
      }
    } else if (sx_is_atom(hd, "DEF") && x->len == 7) {
      const char *name = x->items[1]->text;
      uint32_t h = sym_intern_n(x->items[2]->text, x->items[2]->len);
      uint32_t lv = (uint32_t)x->items[3]->val;
      Term tp = wrap_poly_tp(decode_tp(x->items[4], lv), lv);
      Term raw_body = wrap_poly_tm(decode_tm(x->items[5], lv), lv, true);
      Term body = tm_nf(raw_body);
      Term inf_tp = infer_term(0, T_TPLN, body);
      if (!tp || !body || inf_tp != tp) {
        fprintf(stderr, "mg_tcalc: DEF %s type check failed\n", name);
        ok = false; break;
      }
      if (syms[h].has_term && !syms[h].is_param) {
        if (syms[h].tp == tp) st->repeated++;
        else { ok = false; break; }
      } else {
        syms[h].has_term = true;
        syms[h].is_param = false;
        syms[h].tp = tp;
        syms[h].def = body;
        syms[h].term_seq = next_decl_seq++;
        st->defs++;
      }
    } else if (sx_is_atom(hd, "AXIOM") && x->len == 6) {
      const char *name = x->items[1]->text;
      uint32_t h = sym_intern_n(x->items[2]->text, x->items[2]->len);
      uint32_t lv = (uint32_t)x->items[3]->val;
      Term prop = wrap_poly_tm(decode_tm(x->items[4], lv), lv, false);
      if (!prop || !check_proposition(0, T_TPLN, prop)) {
        fprintf(stderr, "mg_tcalc: AXIOM %s is not a proposition\n", name);
        ok = false; break;
      }
      if (syms[h].has_known) {
        if (!mg_conv(syms[h].prop, prop)) {
          fprintf(stderr, "mg_tcalc: restated AXIOM %s proposition mismatch\n", name);
          ok = false; break;
        }
        st->repeated++;
      } else {
        if (!g_allow_axioms) {
          fprintf(stderr, "mg_tcalc: AXIOM %s refused by --axioms none policy\n", name);
          ok = false; break;
        }
        Term ca[1] = { prop };
        Occ cert = tc_post(SPACE_REL, tc_app(C_AXIOM_CERT, ca));
        Occ keep[1] = { cert };
        Term inst[2] = { T_CTX_EMPTY, prop };
        Occ kocc = commit_mg_step(R_AXIOM, keep, inst);
        if (!kocc) { ok = false; break; }
        syms[h].has_known = true;
        syms[h].prop = prop;
        syms[h].known_occ = kocc;
        st->axioms++;
      }
    } else if ((sx_is_atom(hd, "THM") || sx_is_atom(hd, "CONJ")) && x->len == 7) {
      if (pending) { ok = false; break; }
      pending_name = x->items[1]->text;
      pending_sym  = sym_intern_n(x->items[2]->text, x->items[2]->len);
      pending_levels = (uint32_t)x->items[4]->val;
      pending_prop = wrap_poly_tm(decode_tm(x->items[5], pending_levels), pending_levels, false);
      if (!pending_prop || !check_proposition(0, T_TPLN, pending_prop)) {
        fprintf(stderr, "mg_tcalc: THM %s is not a proposition\n", pending_name);
        ok = false; break;
      }
      pending = !sx_is_atom(hd, "CONJ");
    } else if (sx_is_atom(hd, "PROOF") && x->len == 3) {
      if (!pending) { ok = false; break; }
      MgPf *pf = wrap_poly_pf(decode_pf(x->items[2], pending_levels), pending_levels);
      Term inferred = 0;
      Occ pocc = check_proof_tree(T_CTX_EMPTY, pf, &inferred);
      if (!pocc || !mg_conv(inferred, pending_prop)) {
        fprintf(stderr, "mg_tcalc: PROOF of %s refused\n", pending_name);
        ok = false; break;
      }
      if (syms[pending_sym].has_known) {
        st->repeated++;
      } else {
        Term ca[2] = { pending_prop, inferred };
        Occ cert = tc_post(SPACE_REL, tc_app(C_THM_IMPORT_CERT, ca));
        Occ keep[2] = { pocc, cert };
        Term inst[3] = { T_CTX_EMPTY, pending_prop, inferred };
        Occ kocc = commit_mg_step(R_THM_IMPORT, keep, inst);
        if (!kocc) { ok = false; break; }
        syms[pending_sym].has_known = true;
        syms[pending_sym].prop = pending_prop;
        syms[pending_sym].known_occ = kocc;
        st->thms++;
      }
      free_pf_chunks();
    } else if (sx_is_atom(hd, "QED") && x->len == 1) {
      pending = false;
    } else if (sx_is_atom(hd, "DELTA") || sx_is_atom(hd, "USESKNOWN")) {
      /* informational dependency lines in upstream exports */
    } else {
      fprintf(stderr, "mg_tcalc: unexpected form in %s\n", path);
      ok = false; break;
    }
    free_sx_arena();
  }

  free_pf_chunks();
  free_sx_arena();
  free(buf);
  return ok && !pending;
}

/* ---- Self-test: all 8 rules + negative controls + Subproof Space Reach ---- */
static bool run_self_test(void) {
  init_mg_kernel(PROF_EGAL);

  /* Admit a polymorphic known axiom K: TAll A. All x:A. (x -> x) is ill-typed unless x:prop;
     let's use TAll A. All x:A. Imp(P x, P x) where P : Pi A. A -> prop */
  uint32_t sym_P = sym_intern("P_self");
  syms[sym_P].has_term = true;
  syms[sym_P].is_param = true;
  syms[sym_P].tp = mk_tp_all(mk_tp_arr(mk_tp_var(0), T_TP_PROP));
  syms[sym_P].term_seq = next_decl_seq++;

  /* Construct proof of: TAll A. All x:A. Imp(P A x, P A x)
     using typeLam, termLam, proofLam, hyp! */
  Term vA = mk_tp_var(0);
  Term px = mk_tm_ap(mk_tm_tap(mk_tm_name(sym_P), vA), mk_tm_db(0));
  MgPf *p_hyp = alloc_pf(PF_HYP); p_hyp->n = 0;
  MgPf *p_plam = alloc_pf(PF_PLAM); p_plam->t = px; p_plam->p = p_hyp;
  MgPf *p_tlam = alloc_pf(PF_TLAM); p_tlam->tp = vA; p_tlam->p = p_plam;
  MgPf *p_tplam = alloc_pf(PF_TPLAM); p_tplam->p = p_tlam;

  Term prop_poly = 0;
  Occ occ_poly = check_proof_tree(T_CTX_EMPTY, p_tplam, &prop_poly);
  if (!occ_poly) return false;

  /* Publish as known K_id */
  uint32_t sym_K = sym_intern("K_id");
  Term ca[2] = { prop_poly, prop_poly };
  Occ cert = tc_post(SPACE_REL, tc_app(C_THM_IMPORT_CERT, ca));
  Occ keep_imp[2] = { occ_poly, cert };
  Term inst_imp[3] = { T_CTX_EMPTY, prop_poly, prop_poly };
  Occ kocc = tc_fire(R_THM_IMPORT, NULL, keep_imp, inst_imp);
  if (!kocc) return false;
  syms[sym_K].has_known = true;
  syms[sym_K].prop = prop_poly;
  syms[sym_K].known_occ = kocc;

  /* Now use known, typeApp (A := set), termApp (x := Empty), proofLam, and proofApp
     to prove Imp(P set Empty, P set Empty) */
  Term p_empty = mk_tm_ap(mk_tm_tap(mk_tm_name(sym_P), T_TP_SET), mk_tm_prim(2));
  MgPf *p_kn = alloc_pf(PF_KNOWN); p_kn->n = sym_K;
  MgPf *p_tpap = alloc_pf(PF_TPAP); p_tpap->p = p_kn; p_tpap->tp = T_TP_SET;
  MgPf *p_tmap = alloc_pf(PF_TMAP); p_tmap->p = p_tpap; p_tmap->t = mk_tm_prim(2);
  MgPf *p_pfap = alloc_pf(PF_PFAP); p_pfap->p = p_tmap; p_pfap->q = p_hyp;
  MgPf *p_full = alloc_pf(PF_PLAM); p_full->t = p_empty; p_full->p = p_pfap;

  Term prop_inst = 0;
  Occ occ_inst = check_proof_tree(T_CTX_EMPTY, p_full, &prop_inst);
  if (!occ_inst || prop_inst != mk_tm_imp(p_empty, p_empty)) return false;

  /* Verify all 8 rules fired at least once */
  for (int r = 1; r <= 8; r++) {
    if (stat_rule_fires[r] == 0) return false;
  }

  /* Negative control 1: Gpa placeholder must be refused */
  MgPf *p_gpa = alloc_pf(PF_GPA);
  Term bad_prop = 0;
  if (check_proof_tree(T_CTX_EMPTY, p_gpa, &bad_prop) != 0) return false;

  /* Negative control 2: ill-typed termApp (applying All x:set to a Prop term) must be refused */
  MgPf *p_bad_tmap = alloc_pf(PF_TMAP);
  p_bad_tmap->p = p_tpap;
  p_bad_tmap->t = p_empty; /* has type Prop, not set */
  if (check_proof_tree(T_CTX_EMPTY, p_bad_tmap, &bad_prop) != 0) return false;

  /* Negative control 3: typeLam in non-empty context must be refused */
  Term non_empty_ctx = mk_ctx(0, T_TPLN, mk_tmlc(p_empty, T_TMLN));
  if (check_proof_tree(non_empty_ctx, p_tplam, &bad_prop) != 0) return false;

  /* Subproof Space Birth + Reach (Rows 3-5: NamedSpaces, SpacesCreation, NamedSpacesReach):
     Birth a fresh subproof space s1 for hypothesis p_empty in non_empty_ctx. */
  Term s1 = tc_name(tc_space_sort(), tc_fresh_name());
  Term auth_args[2] = { non_empty_ctx, p_empty };
  Occ auth_occ = tc_post(SPACE_REL, tc_app(C_SUB_AUTH, auth_args));
  Occ keep_b[1] = { auth_occ };
  Term inst_b[3] = { s1, non_empty_ctx, p_empty };
  Occ h1_occ = tc_fire(R_SUB_BIRTH, NULL, keep_b, inst_b);
  if (!h1_occ || !tc_space_born(s1)) return false;
  Occ sub_hyp_occ = tc_last_extra(1);
  if (!sub_hyp_occ || tc_occ_space(sub_hyp_occ) != s1) return false;

  /* Negative control 4 (Births.fresh): birthing s1 a second time must be refused */
  if (tc_fire(R_SUB_BIRTH, NULL, keep_b, inst_b) != 0) return false;

  /* Negative control 5 (NamedSpacesReach): sibling subproof with only handle(s2)
     cannot discharge sub_hyp_occ in s1 */
  Term s2 = tc_name(tc_space_sort(), tc_fresh_name());
  Term s2a[1] = { s2 };
  Term seeds_wrong[2] = { tc_space_term(SPACE_THM), tc_app(C_HANDLE, s2a) };
  Occ keep_u[1] = { sub_hyp_occ };
  if (tc_fire_reach(R_SUB_USE_HYP, NULL, keep_u, inst_b, seeds_wrong, 2) != 0)
    return false;

  /* Positive control (NamedSpacesReach): holder of handle(s1) CAN discharge sub_hyp_occ */
  Term seeds_right[2] = { tc_space_term(SPACE_THM), tc_term(h1_occ) };
  Occ sub_thm = tc_fire_reach(R_SUB_USE_HYP, NULL, keep_u, inst_b, seeds_right, 2);
  if (!sub_thm) return false;

  free_pf_chunks();
  return true;
}

int main(int argc, char **argv) {
  int profile = PROF_EGAL;
  bool did_self_test = false;
  bool chain_mode = false;
  bool inited = false;
  int files_run = 0;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--self-test") == 0) {
      double t0 = now_ms();
      if (!run_self_test()) {
        fprintf(stderr, "mg_tcalc: self-test FAILED\n");
        return 1;
      }
      printf("mg_tcalc self-test: 8 rules + 5 negative controls + subproof-reach passed (%.2f ms)\n",
             now_ms() - t0);
      did_self_test = true;
      inited = false;
    } else if (strcmp(argv[i], "--chain") == 0) {
      chain_mode = true;
      inited = false;
    } else if (strcmp(argv[i], "--no-axioms") == 0) {
      g_allow_axioms = false;
    } else if (strcmp(argv[i], "--axioms") == 0 && i + 1 < argc) {
      i++;
      if (strcmp(argv[i], "all") == 0) g_allow_axioms = true;
      else if (strcmp(argv[i], "none") == 0) g_allow_axioms = false;
      else {
        fprintf(stderr, "mg_tcalc: unknown --axioms policy '%s' (expected all or none)\n", argv[i]);
        return 1;
      }
    } else if (strcmp(argv[i], "--profile") == 0 && i + 1 < argc) {
      i++;
      if (strcmp(argv[i], "egal") == 0) profile = PROF_EGAL;
      else if (strcmp(argv[i], "hf") == 0) profile = PROF_HF;
      else if (strcmp(argv[i], "mizar") == 0) profile = PROF_MIZAR;
      else if (strcmp(argv[i], "hoas") == 0) profile = PROF_HOAS;
      else {
        fprintf(stderr, "mg_tcalc: unknown profile '%s' (expected egal, hf, mizar, or hoas)\n", argv[i]);
        return 1;
      }
      inited = false;
    } else {
      double t0 = now_ms();
      if (!chain_mode || !inited) {
        init_mg_kernel(profile);
        inited = true;
      }
      uint64_t fires_before = 0;
      for (int r = 1; r <= 8; r++) fires_before += stat_rule_fires[r];
      ReplayStats st = {0};
      if (!replay_sexpr_file(argv[i], &st)) {
        fprintf(stderr, "mg_tcalc: FAILED on %s\n", argv[i]);
        return 1;
      }
      uint64_t fires_after = 0;
      for (int r = 1; r <= 8; r++) fires_after += stat_rule_fires[r];
      printf("mg_tcalc [%s%s] %s: %u prims, %u params, %u defs, %u axioms, %u thms, %" PRIu64 " rule fires in %.2f ms\n",
             profile_label(profile),
             chain_mode ? ":chain" : "", argv[i],
             st.prims, st.params, st.defs, st.axioms, st.thms,
             fires_after - fires_before, now_ms() - t0);
      files_run++;
    }
  }

  if (!did_self_test && files_run == 0) {
    if (!run_self_test()) return 1;
    printf("mg_tcalc self-test: passed\n");
  }
  return 0;
}
