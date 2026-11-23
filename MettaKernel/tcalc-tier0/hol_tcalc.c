/* HOL Light LCF kernel & HOLRPLY1 stream verifier on tcalc.
   Types, terms, hypothesis lists, axiom-dependency sets, well-typed term
   judgments (SPACE_WT, protected) and theorem sequents (SPACE_THM, protected)
   are hash-consed tcalc terms and occurrences. Once sealed (tc_seal),
   SPACE_WT and SPACE_THM can only be populated by firing the installed tcalc
   rules for term formation, the 10 primitive HOL Light inference rules
   (REFL, TRANS, MK_COMB, ABS, BETA, ASSUME, EQ_MP, DEDUCT_ANTISYM_RULE,
   INST_TYPE, INST), and the conservative/axiom theory extensions
   (NEW_AXIOM, NEW_DEFINITION, NEW_TYPEDEF). */
#define _POSIX_C_SOURCE 200809L
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

enum { SPACE_REL = 0, SPACE_WT = 1, SPACE_THM = 2 };
enum { POL_OPEN = 0, POL_STANDARD = 1, POL_SEALED = 2 };
enum {
  DECL_TYPE = 1, DECL_CONST = 2, DECL_AXIOM = 3, DECL_DEF = 4,
  DECL_TYDEF = 5, DECL_TYDEF_ABS = 6, DECL_TYDEF_REP = 7, DECL_POLICY = 8
};
enum {
  AUTH_PRIM = 1, AUTH_DECL = 2, AUTH_DEF = 3, AUTH_USER_AX = 4,
  AUTH_STD_ETA = 5, AUTH_STD_SELECT = 6, AUTH_STD_INFINITY = 7, AUTH_POLICY = 8
};

static int S_NAME, S_TYPE, S_TERM, S_HYPS, S_DEPS, S_CERT, S_WT, S_THM;
static int C_TYVAR, C_BOOL, C_FUN;
static int C_VAR, C_CONST, C_COMB, C_ABS;
static int C_HNIL, C_HCONS, C_DNIL, C_DCONS;
static int C_WT, C_THM;
static int C_CONST_INST, C_ACONV, C_HDUNION, C_NOT_FREE_HYPS, C_DEDUCT_CERT;
static int C_SUBST_CERT, C_AXIOM_CERT, C_DEF_CERT, C_TYDEF_CERT;
static int R_WT_VAR, R_WT_CONST, R_WT_COMB, R_WT_ABS;
static int R_REFL, R_BETA, R_ASSUME;
static int R_TRANS_FAST, R_TRANS, R_MK_COMB_FAST, R_MK_COMB;
static int R_ABS_FAST, R_ABS, R_EQ_MP_FAST, R_EQ_MP;
static int R_DEDUCT, R_INST_TYPE, R_INST;
static int R_NEW_AXIOM, R_NEW_DEF, R_NEW_TYDEF1, R_NEW_TYDEF2;
static Term T_BOOL, T_ATY, T_HNIL, T_DNIL;

typedef uint32_t HolName;

typedef struct {
  char *bytes;
  uint32_t len, hash;
  Term nterm;
  uint32_t types, consts;
} NameRec;

typedef struct {
  uint32_t id, parent, next_same, arity;
  uint8_t kind, auth, policy, std_cert;
  HolName name;
  Term dterm, gtype, body;
  int tcon;
  uint32_t witness_thm, thm1, thm2;
} Decl;

typedef struct {
  uint64_t fv_sig, tv_sig;
  uint32_t stamp, anchor;
  Occ wt_occ;
  uint8_t init, flags;
} TMeta;
#define TMF_PARENT 1u
#define TMF_SHARED 2u

typedef struct {
  Occ occ;
  Term thm_term, hyps_term, concl, deps_term;
  uint32_t nhyps, ndeps, anchor;
  Term *hyps;
  uint32_t *deps;
} ThmRec;

static NameRec *names;
static uint32_t nnames, capnames;
static uint32_t *name_idx;
static size_t name_idx_cap;
static HolName N_FUN, N_BOOL, N_EQ, N_A, N_a, N_r;

static Decl *decls;
static uint32_t ndecls, capdecls;
static uint32_t D_FUN, D_BOOL, D_EQ;
static uint32_t tcon_to_decl[16384];

static TMeta *TM;
static uint32_t tm_cap, cur_stamp;

static ThmRec *thms;
static uint32_t nthms, capthms;

typedef struct {
  uint32_t key;
  Term val;
  uint32_t ctx, gen, tag;
} MemoEntry;
static MemoEntry *memo_tab;
static size_t memo_cap, memo_used;
static uint32_t memo_gen = 1, memo_ctx_id = 1;

static uint64_t fnv1a(const void *data, size_t n, uint64_t h) {
  const unsigned char *p = (const unsigned char *)data;
  for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 0x100000001b3ULL; }
  return h;
}
#define FNV_OFFSET 0xcbf29ce484222325ULL

static inline uint64_t sig_bit(uint32_t h) {
  return 1ULL << ((h ^ (h >> 6) ^ (h >> 12)) & 63u);
}

static void ensure_tm(Term t) {
  if (t < tm_cap) return;
  uint32_t ncap = tm_cap ? tm_cap : (1u << 20);
  while (ncap <= t) ncap *= 2;
  TMeta *nt = (TMeta *)realloc(TM, (size_t)ncap * sizeof(TMeta));
  if (!nt) { fprintf(stderr, "hol_tcalc: out of memory\n"); exit(3); }
  memset(nt + tm_cap, 0, (size_t)(ncap - tm_cap) * sizeof(TMeta));
  TM = nt;
  tm_cap = ncap;
}

static uint32_t next_memo_ctx(void) {
  if (!memo_cap) {
    memo_cap = 1u << 14;
    memo_tab = (MemoEntry *)calloc(memo_cap, sizeof(MemoEntry));
    memo_gen = 1;
  } else if (memo_used * 4 > memo_cap * 3) {
    if (memo_cap < (1u << 20)) {
      free(memo_tab);
      memo_cap *= 2;
      memo_tab = (MemoEntry *)calloc(memo_cap, sizeof(MemoEntry));
      memo_gen = 1;
      memo_used = 0;
    } else {
      if (++memo_gen == 0) { memset(memo_tab, 0, memo_cap * sizeof(MemoEntry)); memo_gen = 1; }
      memo_used = 0;
    }
  }
  if (++memo_ctx_id == 0) {
    if (++memo_gen == 0) { memset(memo_tab, 0, memo_cap * sizeof(MemoEntry)); memo_gen = 1; }
    memo_used = 0;
    memo_ctx_id = 1;
  }
  return memo_ctx_id;
}

static inline bool memo_get(Term key, uint32_t ctx, Term *val, uint32_t *tag) {
  if (!ctx || !memo_tab) return false;
  size_t mask = memo_cap - 1;
  size_t j = ((size_t)key * 0x9e3779b1u ^ ctx * 0x85ebca6bu) & mask;
  for (size_t p = 0; p < 8; p++, j = (j + 1) & mask) {
    MemoEntry *e = &memo_tab[j];
    if (e->gen != memo_gen) return false;
    if (e->key == key && e->ctx == ctx) { *val = e->val; *tag = e->tag; return true; }
  }
  return false;
}

static inline void memo_put(Term key, uint32_t ctx, Term val, uint32_t tag) {
  if (!ctx || !memo_tab) return;
  size_t mask = memo_cap - 1;
  size_t j = ((size_t)key * 0x9e3779b1u ^ ctx * 0x85ebca6bu) & mask;
  for (size_t p = 0; p < 8; p++, j = (j + 1) & mask) {
    MemoEntry *e = &memo_tab[j];
    if (e->gen != memo_gen) memo_used++;
    else if (e->key != key || e->ctx != ctx) continue;
    e->key = key; e->val = val; e->ctx = ctx; e->gen = memo_gen; e->tag = tag;
    return;
  }
}

/* ---- Names ---- */
static HolName name_intern(const char *s, size_t len) {
  uint64_t h64 = fnv1a(s, len, FNV_OFFSET);
  uint32_t h = (uint32_t)(h64 ^ (h64 >> 32));
  if (name_idx_cap) {
    size_t mask = name_idx_cap - 1;
    for (size_t j = h & mask;; j = (j + 1) & mask) {
      uint32_t id = name_idx[j];
      if (!id) break;
      const NameRec *r = &names[id];
      if (r->hash == h && r->len == len && memcmp(r->bytes, s, len) == 0) return id;
    }
  }
  if ((size_t)(nnames + 1) * 2 > name_idx_cap) {
    size_t ncap = name_idx_cap ? name_idx_cap * 2 : 1024;
    uint32_t *ni = (uint32_t *)calloc(ncap, sizeof(uint32_t));
    for (size_t i = 0; i < name_idx_cap; i++) {
      uint32_t id = name_idx[i];
      if (!id) continue;
      size_t j = names[id].hash & (ncap - 1);
      while (ni[j]) j = (j + 1) & (ncap - 1);
      ni[j] = id;
    }
    free(name_idx);
    name_idx = ni;
    name_idx_cap = ncap;
  }
  if (nnames + 1 >= capnames) {
    capnames = capnames ? capnames * 2 : 1024;
    names = (NameRec *)realloc(names, (size_t)capnames * sizeof(NameRec));
  }
  uint32_t id = ++nnames;
  char *b = (char *)malloc(len + 1);
  memcpy(b, s, len);
  b[len] = 0;
  uint64_t nid = tc_fresh_name();
  Term nt = tc_name((uint16_t)S_NAME, nid);
  ensure_tm(nt);
  TM[nt].anchor = id;
  names[id] = (NameRec){ b, (uint32_t)len, h, nt, 0, 0 };
  size_t mask = name_idx_cap - 1, j = h & mask;
  while (name_idx[j]) j = (j + 1) & mask;
  name_idx[j] = id;
  return id;
}

static int name_cmp(HolName a, HolName b) {
  if (a == b) return 0;
  const NameRec *x = &names[a], *y = &names[b];
  size_t n = x->len < y->len ? x->len : y->len;
  int c = memcmp(x->bytes, y->bytes, n);
  if (c) return c < 0 ? -1 : 1;
  return x->len < y->len ? -1 : (x->len > y->len ? 1 : 0);
}

static HolName name_prime(HolName n) {
  uint32_t len = names[n].len;
  char small[256], *buf = len + 1 <= sizeof(small) ? small : (char *)malloc(len + 1);
  memcpy(buf, names[n].bytes, len);
  buf[len] = '\'';
  HolName out = name_intern(buf, len + 1);
  if (buf != small) free(buf);
  return out;
}

/* ---- Types (S_TYPE terms in tcalc) ---- */
static inline void ty_inspect(Term ty, uint32_t *con, int *ar, const Term **args) {
  uint8_t k;
  tc_node(ty, &k, con, ar, args);
}

static Term ty_var(HolName name) {
  Term a[1] = { names[name].nterm };
  Term t = tc_app(C_TYVAR, a);
  ensure_tm(t);
  if (!TM[t].init) {
    TM[t].init = 1;
    TM[t].tv_sig = sig_bit(names[name].hash);
    TM[t].anchor = 0;
  }
  return t;
}

static Term ty_app(uint32_t decl_id, const Term *args, uint32_t n) {
  Decl *d = &decls[decl_id];
  if (n != d->arity || n > TC_ARGS) return 0;
  uint32_t anchor = decl_id;
  uint64_t sig = 0;
  for (uint32_t i = 0; i < n; i++) {
    if (TM[args[i]].anchor > anchor) anchor = TM[args[i]].anchor;
    sig |= TM[args[i]].tv_sig;
  }
  Term t = tc_app(d->tcon, n ? args : NULL);
  if (!t) return 0;
  ensure_tm(t);
  if (!TM[t].init) {
    TM[t].init = 1;
    TM[t].tv_sig = sig;
    TM[t].anchor = anchor;
  }
  return t;
}

static Term ty_fun(Term a, Term b) {
  Term args[2] = { a, b };
  return ty_app(D_FUN, args, 2);
}

static inline bool ty_is_fun(Term ty, Term *dom, Term *cod) {
  uint32_t con; int ar; const Term *a;
  ty_inspect(ty, &con, &ar, &a);
  if ((int)con != C_FUN || ar != 2) return false;
  if (dom) *dom = a[0];
  if (cod) *cod = a[1];
  return true;
}

static int ty_compare(Term a, Term b) {
  if (a == b) return 0;
  uint32_t ca, cb; int na, nb; const Term *aa, *ab;
  ty_inspect(a, &ca, &na, &aa);
  ty_inspect(b, &cb, &nb, &ab);
  bool va = ((int)ca == C_TYVAR), vb = ((int)cb == C_TYVAR);
  if (va != vb) return va ? -1 : 1;
  if (va) {
    HolName nma = (HolName)TM[aa[0]].anchor;
    HolName nmb = (HolName)TM[ab[0]].anchor;
    return name_cmp(nma, nmb);
  }
  uint32_t da = tcon_to_decl[ca], db = tcon_to_decl[cb];
  int c = name_cmp(decls[da].name, decls[db].name);
  if (c) return c;
  int n = na < nb ? na : nb;
  Term la[TC_ARGS], lb[TC_ARGS];
  for (int i = 0; i < na; i++) la[i] = aa[i];
  for (int i = 0; i < nb; i++) lb[i] = ab[i];
  for (int i = 0; i < n; i++) {
    c = ty_compare(la[i], lb[i]);
    if (c) return c;
  }
  if (na != nb) return na < nb ? -1 : 1;
  return da < db ? -1 : (da > db ? 1 : 0);
}

typedef struct { Term repl, key; } TyPair;
typedef struct { const TyPair *p; size_t n; uint64_t dom_sig; } TySubst;

static void tysubst_init(TySubst *s, const TyPair *p, size_t n) {
  s->p = p; s->n = n; s->dom_sig = 0;
  for (size_t i = 0; i < n; i++) {
    uint32_t con; int ar; const Term *a;
    ty_inspect(p[i].key, &con, &ar, &a);
    if ((int)con == C_TYVAR) s->dom_sig |= TM[p[i].key].tv_sig;
  }
}

static Term type_subst_rec(const TySubst *s, Term ty, uint32_t ctx) {
  if ((TM[ty].tv_sig & s->dom_sig) == 0) return ty;
  uint32_t con; int ar; const Term *a;
  ty_inspect(ty, &con, &ar, &a);
  if ((int)con == C_TYVAR) {
    for (size_t i = 0; i < s->n; i++)
      if (s->p[i].key == ty) return s->p[i].repl;
    return ty;
  }
  Term mv; uint32_t mtag;
  if (memo_get(ty, ctx, &mv, &mtag) && mtag == 1) return mv;
  Term orig[TC_ARGS], args[TC_ARGS];
  for (int i = 0; i < ar; i++) orig[i] = a[i];
  bool changed = false;
  for (int i = 0; i < ar; i++) {
    args[i] = type_subst_rec(s, orig[i], ctx);
    if (!args[i]) return 0;
    if (args[i] != orig[i]) changed = true;
  }
  Term out = changed ? ty_app(tcon_to_decl[con], args, (uint32_t)ar) : ty;
  if (out) memo_put(ty, ctx, out, 1);
  return out;
}

/* ---- Terms (S_TERM terms in tcalc) ---- */
static inline void note_child(Term c) {
  if (TM[c].flags & TMF_PARENT) TM[c].flags |= TMF_SHARED;
  else TM[c].flags |= TMF_PARENT;
}

static inline void tm_inspect(Term tm, uint32_t *con, Term *ty, Term *l, Term *r) {
  uint8_t k; int ar; const Term *a;
  tc_node(tm, &k, con, &ar, &a);
  if (ty) *ty = a[0];
  if (l) *l = a[1];
  if (r) *r = ar > 2 ? a[2] : 0;
}

static inline Term tm_type(Term tm) {
  uint8_t k; uint32_t con; int ar; const Term *a;
  tc_node(tm, &k, &con, &ar, &a);
  return a[0];
}

static inline uint32_t tm_con(Term tm) {
  uint8_t k; uint32_t con; int ar; const Term *a;
  tc_node(tm, &k, &con, &ar, &a);
  return con;
}

static Term tm_var(HolName name, Term ty) {
  Term a[2] = { ty, names[name].nterm };
  Term t = tc_app(C_VAR, a);
  if (!t) return 0;
  ensure_tm(t);
  if (!TM[t].init) {
    TM[t].init = 1;
    TM[t].fv_sig = sig_bit(t * 0x9e3779b1u);
    TM[t].tv_sig = TM[ty].tv_sig;
    TM[t].anchor = TM[ty].anchor;
  }
  return t;
}

static Term tm_const(uint32_t decl_id, Term ty) {
  Decl *d = &decls[decl_id];
  Term a[2] = { ty, d->dterm };
  Term t = tc_app(C_CONST, a);
  if (!t) return 0;
  ensure_tm(t);
  if (!TM[t].init) {
    TM[t].init = 1;
    TM[t].fv_sig = 0;
    TM[t].tv_sig = TM[ty].tv_sig;
    TM[t].anchor = decl_id > TM[ty].anchor ? decl_id : TM[ty].anchor;
  }
  return t;
}

static Term tm_node(int con, Term l, Term r, Term ty) {
  Term a[3] = { ty, l, r };
  Term t = tc_app(con, a);
  if (!t) return 0;
  ensure_tm(t);
  if (!TM[t].init) {
    TM[t].init = 1;
    TM[t].fv_sig = con == C_ABS ? TM[r].fv_sig : (TM[l].fv_sig | TM[r].fv_sig);
    TM[t].tv_sig = TM[l].tv_sig | TM[r].tv_sig;
    TM[t].anchor = TM[l].anchor > TM[r].anchor ? TM[l].anchor : TM[r].anchor;
    note_child(l);
    note_child(r);
  }
  return t;
}

static Term tm_comb(Term f, Term x) {
  Term dom, cod;
  if (!ty_is_fun(tm_type(f), &dom, &cod) || dom != tm_type(x)) return 0;
  return tm_node(C_COMB, f, x, cod);
}

static Term tm_abs(Term v, Term body) {
  if ((int)tm_con(v) != C_VAR) return 0;
  Term ty = ty_fun(tm_type(v), tm_type(body));
  if (!ty) return 0;
  return tm_node(C_ABS, v, body, ty);
}

static Term tm_eq(Term l, Term r) {
  Term ty = tm_type(l);
  Term t2 = ty_fun(ty, T_BOOL);
  Term t1 = t2 ? ty_fun(ty, t2) : 0;
  Term c = t1 ? tm_const(D_EQ, t1) : 0;
  Term cl = c ? tm_comb(c, l) : 0;
  return cl ? tm_comb(cl, r) : 0;
}

static inline bool tm_is_eq(Term t, Term *lhs, Term *rhs) {
  uint32_t c1, c2, c3; Term ty1, l1, r1, ty2, l2, r2, ty3, l3, r3;
  tm_inspect(t, &c1, &ty1, &l1, &r1);
  if ((int)c1 != C_COMB) return false;
  tm_inspect(l1, &c2, &ty2, &l2, &r2);
  if ((int)c2 != C_COMB) return false;
  tm_inspect(l2, &c3, &ty3, &l3, &r3);
  if ((int)c3 != C_CONST || l3 != decls[D_EQ].dterm) return false;
  if (lhs) *lhs = r2;
  if (rhs) *rhs = r1;
  return true;
}

static inline int tm_kind_ord(uint32_t con) {
  if ((int)con == C_VAR) return 0;
  if ((int)con == C_CONST) return 1;
  if ((int)con == C_COMB) return 2;
  return 3;
}

static inline HolName tm_leaf_name(Term t) {
  uint32_t con; Term ty, l, r;
  tm_inspect(t, &con, &ty, &l, &r);
  if ((int)con == C_VAR) return (HolName)TM[l].anchor;
  uint32_t did = TM[l].anchor;
  return decls[did].name;
}

static int tm_compare(Term a, Term b) {
  while (a != b) {
    uint32_t ca, cb; Term tya, la, ra, tyb, lb, rb;
    tm_inspect(a, &ca, &tya, &la, &ra);
    tm_inspect(b, &cb, &tyb, &lb, &rb);
    int ka = tm_kind_ord(ca), kb = tm_kind_ord(cb);
    if (ka != kb) return ka < kb ? -1 : 1;
    if (ka <= 1) {
      int c = name_cmp(tm_leaf_name(a), tm_leaf_name(b));
      if (c) return c;
      c = ty_compare(tya, tyb);
      if (c) return c;
      if (ka == 1 && la != lb)
        return TM[la].anchor < TM[lb].anchor ? -1 : 1;
      return 0;
    }
    int c = tm_compare(la, lb);
    if (c) return c;
    a = ra;
    b = rb;
  }
  return 0;
}

/* ---- Alpha order ---- */
typedef struct { Term x1, x2; } OrdaPair;
typedef struct { OrdaPair *p; size_t n, cap, nonid; } OrdaEnv;

static int ordav(const OrdaEnv *env, Term x1, Term x2) {
  for (size_t i = env->n; i-- > 0;) {
    if (x1 == env->p[i].x1) return x2 == env->p[i].x2 ? 0 : -1;
    if (x2 == env->p[i].x2) return 1;
  }
  return tm_compare(x1, x2);
}

static int orda(OrdaEnv *env, Term t1, Term t2) {
  for (;;) {
    if (t1 == t2 && env->nonid == 0) return 0;
    uint32_t c1, c2; Term ty1, l1, r1, ty2, l2, r2;
    tm_inspect(t1, &c1, &ty1, &l1, &r1);
    tm_inspect(t2, &c2, &ty2, &l2, &r2);
    int a = tm_kind_ord(c1), b = tm_kind_ord(c2);
    if (a == b) {
      if (a == 0) return ordav(env, t1, t2);
      if (a == 1) return tm_compare(t1, t2);
      if (a == 2) {
        int c = orda(env, l1, l2);
        if (c) return c;
        t1 = r1; t2 = r2;
        continue;
      }
      int c = ty_compare(tm_type(l1), tm_type(l2));
      if (c) return c;
      if (env->n == env->cap) {
        env->cap = env->cap ? env->cap * 2 : 32;
        env->p = (OrdaPair *)realloc(env->p, env->cap * sizeof(OrdaPair));
      }
      env->p[env->n++] = (OrdaPair){ l1, l2 };
      if (l1 != l2) env->nonid++;
      int res = orda(env, r1, r2);
      env->n--;
      if (l1 != l2) env->nonid--;
      return res;
    }
    if (a == 1) return -1;
    if (b == 1) return 1;
    if (a == 0) return -1;
    if (b == 0) return 1;
    return a == 2 ? -1 : 1;
  }
}

static int alphaorder(Term a, Term b) {
  if (a == b) return 0;
  OrdaEnv env = {0};
  int r = orda(&env, a, b);
  free(env.p);
  return r;
}

/* ---- Free variables, vsubst, inst ---- */
static uint32_t next_stamp(void) {
  if (++cur_stamp == 0) {
    for (uint32_t i = 0; i < tm_cap; i++) TM[i].stamp = 0;
    cur_stamp = 1;
  }
  return cur_stamp;
}

static bool vfree_rec(Term v, uint64_t vbit, uint32_t stamp, Term tm) {
  if (vbit && !(TM[tm].fv_sig & vbit)) return false;
  if (TM[tm].stamp == stamp) return false;
  uint32_t con; Term ty, l, r;
  tm_inspect(tm, &con, &ty, &l, &r);
  bool res;
  if ((int)con == C_ABS) {
    res = (l != v) && vfree_rec(v, vbit, stamp, r);
  } else if ((int)con == C_COMB) {
    res = vfree_rec(v, vbit, stamp, l) || vfree_rec(v, vbit, stamp, r);
  } else {
    res = (tm == v);
  }
  if (!res) TM[tm].stamp = stamp;
  return res;
}

static bool vfree_in(Term v, Term tm) {
  uint64_t vbit = (int)tm_con(v) == C_VAR ? TM[v].fv_sig : 0;
  if (vbit && !(TM[tm].fv_sig & vbit)) return false;
  uint32_t con = tm_con(tm);
  if ((int)con == C_VAR || (int)con == C_CONST) return tm == v;
  return vfree_rec(v, vbit, next_stamp(), tm);
}

typedef struct { Term *v; size_t n, cap; } TermVec;
static void tvec_push(TermVec *vec, Term x) {
  if (vec->n == vec->cap) {
    vec->cap = vec->cap ? vec->cap * 2 : 16;
    vec->v = (Term *)realloc(vec->v, vec->cap * sizeof(Term));
  }
  vec->v[vec->n++] = x;
}
static bool tvec_mem(const TermVec *v, Term x) {
  for (size_t i = 0; i < v->n; i++) if (v->v[i] == x) return true;
  return false;
}
static void tvec_union_into(const TermVec *l1, TermVec *l2) {
  TermVec out = {0};
  for (size_t i = 0; i < l1->n; i++) {
    Term x = l1->v[i];
    bool later = false;
    for (size_t j = i + 1; j < l1->n && !later; j++) later = (l1->v[j] == x);
    if (later || tvec_mem(l2, x)) continue;
    tvec_push(&out, x);
  }
  for (size_t i = 0; i < l2->n; i++) tvec_push(&out, l2->v[i]);
  free(l2->v);
  *l2 = out;
}

static bool freesin_rec(TermVec *acc, Term tm) {
  for (;;) {
    uint32_t con; Term ty, l, r;
    tm_inspect(tm, &con, &ty, &l, &r);
    if ((int)con == C_VAR) {
      for (size_t i = acc->n; i-- > 0;) if (acc->v[i] == tm) return true;
      return false;
    }
    if ((int)con == C_CONST) return true;
    if ((int)con == C_ABS) {
      tvec_push(acc, l);
      bool ok = freesin_rec(acc, r);
      acc->n--;
      return ok;
    }
    if (!freesin_rec(acc, l)) return false;
    tm = r;
  }
}

static bool freesin_closed(Term tm) {
  if (TM[tm].fv_sig == 0) return true;
  TermVec v = {0};
  bool ok = freesin_rec(&v, tm);
  free(v.v);
  return ok;
}

static void frees_exact(Term tm, TermVec *out) {
  uint32_t con; Term ty, l, r;
  tm_inspect(tm, &con, &ty, &l, &r);
  if ((int)con == C_VAR) { tvec_push(out, tm); return; }
  if ((int)con == C_CONST) return;
  if ((int)con == C_ABS) {
    TermVec b = {0};
    frees_exact(r, &b);
    for (size_t i = 0; i < b.n; i++) if (b.v[i] != l) tvec_push(out, b.v[i]);
    free(b.v);
    return;
  }
  TermVec s = {0}, t = {0};
  frees_exact(l, &s);
  frees_exact(r, &t);
  tvec_union_into(&s, &t);
  for (size_t i = 0; i < t.n; i++) tvec_push(out, t.v[i]);
  free(s.v);
  free(t.v);
}

static void tyvars_exact(Term ty, TermVec *out) {
  uint32_t con; int ar; const Term *a;
  ty_inspect(ty, &con, &ar, &a);
  if ((int)con == C_TYVAR) { tvec_push(out, ty); return; }
  Term args[TC_ARGS];
  for (int i = 0; i < ar; i++) args[i] = a[i];
  TermVec acc = {0};
  for (int i = ar; i-- > 0;) {
    TermVec sub = {0};
    tyvars_exact(args[i], &sub);
    tvec_union_into(&sub, &acc);
    free(sub.v);
  }
  for (size_t i = 0; i < acc.n; i++) tvec_push(out, acc.v[i]);
  free(acc.v);
}

static void type_vars_in_term_exact(Term tm, TermVec *out) {
  uint32_t con; Term ty, l, r;
  tm_inspect(tm, &con, &ty, &l, &r);
  if ((int)con == C_VAR || (int)con == C_CONST) { tyvars_exact(ty, out); return; }
  TermVec s = {0}, t = {0};
  if ((int)con == C_ABS) tyvars_exact(tm_type(l), &s);
  else type_vars_in_term_exact(l, &s);
  type_vars_in_term_exact(r, &t);
  tvec_union_into(&s, &t);
  for (size_t i = 0; i < t.n; i++) tvec_push(out, t.v[i]);
  free(s.v);
  free(t.v);
}

static Term variant(const Term *avoid, size_t n, Term v) {
  for (;;) {
    bool hit = false;
    for (size_t i = 0; i < n && !hit; i++) hit = vfree_in(v, avoid[i]);
    if (!hit) return v;
    if ((int)tm_con(v) != C_VAR) return 0;
    HolName n2 = name_prime(tm_leaf_name(v));
    v = tm_var(n2, tm_type(v));
  }
}

typedef struct { Term t, x; } TmPair;
typedef struct { const TmPair *p; size_t n; uint64_t dom_sig; uint32_t ctx; } VsList;

static uint64_t vs_dom_sig(const TmPair *p, size_t n) {
  uint64_t s = 0;
  for (size_t i = 0; i < n; i++) s |= TM[p[i].x].fv_sig;
  return s;
}

static Term vs_rec(const VsList *il, Term tm) {
  if (!(TM[tm].fv_sig & il->dom_sig)) return tm;
  uint32_t con; Term ty, l, r;
  tm_inspect(tm, &con, &ty, &l, &r);
  if ((int)con == C_VAR) {
    for (size_t i = 0; i < il->n; i++) if (il->p[i].x == tm) return il->p[i].t;
    return tm;
  }
  if ((int)con == C_CONST) return tm;
  bool shared = (TM[tm].flags & TMF_SHARED) != 0;
  Term mv; uint32_t mtag;
  if (shared && memo_get(tm, il->ctx, &mv, &mtag)) return mv;
  if ((int)con == C_COMB) {
    Term s = vs_rec(il, l);
    Term t = vs_rec(il, r);
    Term res = (s == l && t == r) ? tm : tm_node(C_COMB, s, t, ty);
    if (res && shared) memo_put(tm, il->ctx, res, 2);
    return res;
  }
  Term v = l, s = r;
  size_t m = 0;
  for (size_t i = 0; i < il->n; i++) if (il->p[i].x != v) m++;
  if (m == 0) return tm;
  VsList il2 = *il;
  TmPair *buf = NULL;
  if (m != il->n) {
    buf = (TmPair *)malloc((m + 1) * sizeof(TmPair));
    size_t j = 1;
    for (size_t i = 0; i < il->n; i++) if (il->p[i].x != v) buf[j++] = il->p[i];
    il2.p = buf + 1;
    il2.n = m;
    il2.dom_sig = vs_dom_sig(il2.p, m);
    il2.ctx = next_memo_ctx();
  }
  Term s1 = vs_rec(&il2, s), res = 0;
  if (s1 == s) { res = tm; goto out; }
  {
    bool capture = false;
    for (size_t i = 0; i < il2.n && !capture; i++)
      if (vfree_in(v, il2.p[i].t) && vfree_in(il2.p[i].x, s)) capture = true;
    if (!capture) {
      res = tm_node(C_ABS, v, s1, ty);
    } else {
      Term avoid[1] = { s1 };
      Term v1 = variant(avoid, 1, v);
      if (!buf) {
        buf = (TmPair *)malloc((il->n + 1) * sizeof(TmPair));
        for (size_t i = 0; i < il->n; i++) buf[i + 1] = il->p[i];
      }
      buf[0] = (TmPair){ v1, v };
      VsList il3 = { buf, il2.n + 1, il2.dom_sig | TM[v].fv_sig, next_memo_ctx() };
      Term s2 = vs_rec(&il3, s);
      res = tm_node(C_ABS, v1, s2, ty);
    }
  }
out:
  free(buf);
  if (res && shared) memo_put(tm, il->ctx, res, 2);
  return res;
}

static bool vsubst_check(const TmPair *p, size_t n) {
  for (size_t i = 0; i < n; i++)
    if ((int)tm_con(p[i].x) != C_VAR || tm_type(p[i].t) != tm_type(p[i].x))
      return false;
  return true;
}

typedef struct { Term y, yp; } InstPair;
typedef struct {
  TySubst ts;
  uint32_t tctx, ctx;
  InstPair *env;
  size_t n, cap, changed;
  uint64_t changed_sig;
} InstCtx;

static Term inst_ty(InstCtx *c, Term ty) {
  if ((TM[ty].tv_sig & c->ts.dom_sig) == 0) return ty;
  return type_subst_rec(&c->ts, ty, c->tctx);
}

static int inst_rec(InstCtx *c, Term tm, Term *out, Term *clash) {
  if (!(TM[tm].tv_sig & c->ts.dom_sig) &&
      (c->changed == 0 || !(TM[tm].fv_sig & c->changed_sig))) {
    *out = tm;
    return 0;
  }
  uint32_t con; Term ty, l, r;
  tm_inspect(tm, &con, &ty, &l, &r);
  if ((int)con == C_VAR) {
    Term ty1 = inst_ty(c, ty);
    Term tm1 = ty1 == ty ? tm : tm_var(tm_leaf_name(tm), ty1);
    Term orig = tm;
    for (size_t i = c->n; i-- > 0;)
      if (c->env[i].yp == tm1) { orig = c->env[i].y; break; }
    if (orig == tm) { *out = tm1; return 0; }
    *clash = tm1;
    return 1;
  }
  if ((int)con == C_CONST) {
    Term ty1 = inst_ty(c, ty);
    *out = ty1 == ty ? tm : tm_const(TM[l].anchor, ty1);
    return 0;
  }
  bool shared = (TM[tm].flags & TMF_SHARED) != 0;
  Term mv; uint32_t mtag;
  if (shared && memo_get(tm, c->ctx, &mv, &mtag)) {
    if (mtag == 2) { *out = mv; return 0; }
    *clash = mv;
    return 1;
  }
  if ((int)con == C_COMB) {
    Term f1 = 0, x1 = 0;
    int rc = inst_rec(c, l, &f1, clash);
    if (rc == 0) rc = inst_rec(c, r, &x1, clash);
    if (rc == 1) {
      if (shared) memo_put(tm, c->ctx, *clash, 3);
      return 1;
    }
    Term res = (f1 == l && x1 == r) ? tm : tm_comb(f1, x1);
    if (shared) memo_put(tm, c->ctx, res, 2);
    *out = res;
    return 0;
  }
  Term y = l, t = r;
  Term yty = inst_ty(c, tm_type(y));
  Term y1 = yty == tm_type(y) ? y : tm_var(tm_leaf_name(y), yty);
  if (c->n == c->cap) {
    c->cap = c->cap ? c->cap * 2 : 32;
    c->env = (InstPair *)realloc(c->env, c->cap * sizeof(InstPair));
  }
  uint32_t saved_ctx = c->ctx;
  size_t saved_changed = c->changed;
  uint64_t saved_sig = c->changed_sig;
  c->env[c->n++] = (InstPair){ y, y1 };
  if (y1 != y) { c->changed++; c->changed_sig |= TM[y1].fv_sig; }
  c->ctx = next_memo_ctx();
  Term t1 = 0, w = 0;
  int rc = inst_rec(c, t, &t1, &w);
  c->n--;
  c->ctx = saved_ctx;
  c->changed = saved_changed;
  c->changed_sig = saved_sig;
  if (rc == 0) {
    Term res = (y1 == y && t1 == t) ? tm : tm_node(C_ABS, y1, t1, ty_fun(tm_type(y1), tm_type(t1)));
    if (shared) memo_put(tm, c->ctx, res, 2);
    *out = res;
    return 0;
  }
  if (w != y1) {
    if (shared) memo_put(tm, c->ctx, w, 3);
    *clash = w;
    return 1;
  }
  TermVec fr = {0};
  frees_exact(t, &fr);
  for (size_t i = 0; i < fr.n; i++) {
    Term fv = fr.v[i];
    Term fty = inst_ty(c, tm_type(fv));
    fr.v[i] = fty == tm_type(fv) ? fv : tm_var(tm_leaf_name(fv), fty);
  }
  Term y2 = variant(fr.v, fr.n, y1);
  free(fr.v);
  Term z = tm_var(tm_leaf_name(y2), tm_type(y));
  TmPair pr = { z, y };
  VsList il = { &pr, 1, TM[y].fv_sig, next_memo_ctx() };
  Term body = vs_rec(&il, t);
  Term renamed = tm_node(C_ABS, z, body, ty);
  int rc2 = inst_rec(c, renamed, out, clash);
  if (shared && rc2 == 0) memo_put(tm, c->ctx, *out, 2);
  else if (shared && rc2 == 1) memo_put(tm, c->ctx, *clash, 3);
  return rc2;
}

static Term hol_inst(const TyPair *p, size_t n, Term tm) {
  if (n == 0) return tm;
  InstCtx c = {0};
  tysubst_init(&c.ts, p, n);
  c.tctx = next_memo_ctx();
  c.ctx = next_memo_ctx();
  Term out = 0, clash = 0;
  int rc = inst_rec(&c, tm, &out, &clash);
  free(c.env);
  return rc == 0 ? out : 0;
}

/* ---- Hypothesis lists & axiom dependency sets in tcalc ---- */
static Term hyps_build(const Term *hyps, uint32_t n) {
  Term t = T_HNIL;
  for (uint32_t i = n; i-- > 0;) {
    Term a[2] = { hyps[i], t };
    t = tc_app(C_HCONS, a);
    ensure_tm(t);
  }
  return t;
}

static Term deps_build(const uint32_t *deps, uint32_t n) {
  Term t = T_DNIL;
  for (uint32_t i = n; i-- > 0;) {
    Term a[2] = { decls[deps[i]].dterm, t };
    t = tc_app(C_DCONS, a);
    ensure_tm(t);
  }
  return t;
}

static void term_union(const Term *a, uint32_t na, const Term *b, uint32_t nb,
                       Term **out, uint32_t *nout) {
  if (na == 0 && nb == 0) { *out = NULL; *nout = 0; return; }
  Term *buf = (Term *)malloc((size_t)(na + nb) * sizeof(Term));
  uint32_t i = 0, j = 0, k = 0;
  while (i < na && j < nb) {
    int c = alphaorder(a[i], b[j]);
    if (c == 0) { buf[k++] = a[i]; i++; j++; }
    else if (c < 0) buf[k++] = a[i++];
    else buf[k++] = b[j++];
  }
  while (i < na) buf[k++] = a[i++];
  while (j < nb) buf[k++] = b[j++];
  *out = buf; *nout = k;
}

static void term_remove(const Term *a, uint32_t na, Term x,
                        Term **out, uint32_t *nout) {
  if (na == 0) { *out = NULL; *nout = 0; return; }
  Term *buf = (Term *)malloc((size_t)na * sizeof(Term));
  uint32_t k = 0;
  for (uint32_t i = 0; i < na; i++) {
    int c = alphaorder(a[i], x);
    if (c == 0) {
      for (uint32_t j = i + 1; j < na; j++) buf[k++] = a[j];
      break;
    }
    buf[k++] = a[i];
    if (c > 0) {
      for (uint32_t j = i + 1; j < na; j++) buf[k++] = a[j];
      break;
    }
  }
  if (k == 0) { free(buf); buf = NULL; }
  *out = buf; *nout = k;
}

static void deps_union(const uint32_t *a, uint32_t na, const uint32_t *b, uint32_t nb,
                       uint32_t **out, uint32_t *nout) {
  if (na == 0 && nb == 0) { *out = NULL; *nout = 0; return; }
  uint32_t *buf = (uint32_t *)malloc((size_t)(na + nb) * sizeof(uint32_t));
  uint32_t i = 0, j = 0, k = 0;
  while (i < na && j < nb) {
    if (a[i] == b[j]) { buf[k++] = a[i]; i++; j++; }
    else if (a[i] < b[j]) buf[k++] = a[i++];
    else buf[k++] = b[j++];
  }
  while (i < na) buf[k++] = a[i++];
  while (j < nb) buf[k++] = b[j++];
  *out = buf; *nout = k;
}

/* ---- Well-typed term certification in SPACE_WT via tcalc rules ---- */
static Occ certify_wt(Term tm) {
  ensure_tm(tm);
  if (TM[tm].wt_occ) return TM[tm].wt_occ;
  Term ty = tm_type(tm);
  uint32_t con; Term t0, l, r;
  tm_inspect(tm, &con, &t0, &l, &r);
  Occ out = 0;
  if ((int)con == C_VAR) {
    Term bind[2] = { ty, l };
    out = tc_fire(R_WT_VAR, NULL, NULL, bind);
  } else if ((int)con == C_CONST) {
    Term ca[2] = { ty, l };
    Occ co = tc_post(SPACE_REL, tc_app(C_CONST_INST, ca));
    Occ prem[1] = { co };
    out = tc_fire(R_WT_CONST, NULL, prem, NULL);
  } else if ((int)con == C_COMB) {
    Occ of = certify_wt(l);
    Occ ox = certify_wt(r);
    if (!of || !ox) return 0;
    Occ prem[2] = { of, ox };
    out = tc_fire(R_WT_COMB, NULL, prem, NULL);
  } else if ((int)con == C_ABS) {
    Occ ov = certify_wt(l);
    Occ ob = certify_wt(r);
    if (!ov || !ob) return 0;
    Occ prem[2] = { ov, ob };
    out = tc_fire(R_WT_ABS, NULL, prem, NULL);
  }
  if (out) TM[tm].wt_occ = out;
  return out;
}

/* ---- Theorem registration & 10 primitive HOL Light inference rules ---- */
static uint32_t thm_register(Occ occ, Term hyps_term, Term concl, Term deps_term,
                             Term *hyps, uint32_t nhyps, uint32_t *deps, uint32_t ndeps) {
  if (!occ) { free(hyps); free(deps); return 0; }
  Term thm_term = tc_term(occ);
  ensure_tm(thm_term);
  if (nthms + 1 >= capthms) {
    capthms = capthms ? capthms * 2 : 1024;
    thms = (ThmRec *)realloc(thms, (size_t)capthms * sizeof(ThmRec));
  }
  uint32_t anchor = TM[concl].anchor;
  for (uint32_t i = 0; i < nhyps; i++)
    if (TM[hyps[i]].anchor > anchor) anchor = TM[hyps[i]].anchor;
  for (uint32_t i = 0; i < ndeps; i++)
    if (deps[i] > anchor) anchor = deps[i];
  uint32_t id = ++nthms;
  thms[id] = (ThmRec){
    occ, thm_term, hyps_term, concl, deps_term, nhyps, ndeps, anchor, hyps, deps
  };
  return id;
}

static uint32_t rule_REFL(Term tm) {
  if (!tm) return 0;
  Term bind[2] = { tm_type(tm), tm };
  Occ occ = tc_fire(R_REFL, NULL, NULL, bind);
  if (!occ) return 0;
  return thm_register(occ, T_HNIL, tm_eq(tm, tm), T_DNIL, NULL, 0, NULL, 0);
}

static uint32_t rule_BETA(Term tm) {
  if (!tm) return 0;
  uint32_t c1, c2; Term ty1, l1, r1, ty2, v, bod;
  tm_inspect(tm, &c1, &ty1, &l1, &r1);
  if ((int)c1 != C_COMB) return 0;
  tm_inspect(l1, &c2, &ty2, &v, &bod);
  if ((int)c2 != C_ABS || r1 != v) return 0;
  Term dom, cod;
  if (!ty_is_fun(ty2, &dom, &cod)) return 0;
  uint32_t vc; Term vty, vn, vr;
  tm_inspect(v, &vc, &vty, &vn, &vr);
  Term bind[4] = { dom, cod, vn, bod };
  Occ occ = tc_fire(R_BETA, NULL, NULL, bind);
  if (!occ) return 0;
  return thm_register(occ, T_HNIL, tm_eq(tm, bod), T_DNIL, NULL, 0, NULL, 0);
}

static uint32_t rule_ASSUME(Term p) {
  if (!p || tm_type(p) != T_BOOL) return 0;
  Occ wt = certify_wt(p);
  if (!wt) return 0;
  Occ prem[1] = { wt };
  Occ occ = tc_fire(R_ASSUME, NULL, prem, NULL);
  if (!occ) return 0;
  Term *hyps = (Term *)malloc(sizeof(Term));
  hyps[0] = p;
  return thm_register(occ, hyps_build(hyps, 1), p, T_DNIL, hyps, 1, NULL, 0);
}

static uint32_t rule_TRANS(uint32_t t1, uint32_t t2) {
  const ThmRec *p1 = &thms[t1], *p2 = &thms[t2];
  Term l1, m1, m2, r2;
  if (!tm_is_eq(p1->concl, &l1, &m1) || !tm_is_eq(p2->concl, &m2, &r2)) return 0;
  if (m1 != m2 && alphaorder(m1, m2) != 0) return 0;
  Term concl = tm_eq(l1, r2);
  if (m1 == m2 && p1->nhyps == 0 && p2->nhyps == 0 && p1->ndeps == 0 && p2->ndeps == 0) {
    Occ prem[2] = { p1->occ, p2->occ };
    Occ occ = tc_fire(R_TRANS_FAST, NULL, prem, NULL);
    return thm_register(occ, T_HNIL, concl, T_DNIL, NULL, 0, NULL, 0);
  }
  Term *hyps = NULL; uint32_t nhyps = 0;
  uint32_t *deps = NULL; uint32_t ndeps = 0;
  term_union(p1->hyps, p1->nhyps, p2->hyps, p2->nhyps, &hyps, &nhyps);
  deps_union(p1->deps, p1->ndeps, p2->deps, p2->ndeps, &deps, &ndeps);
  Term ht = hyps_build(hyps, nhyps), dt = deps_build(deps, ndeps);
  Term aa[2] = { m1, m2 };
  Occ oa = tc_post(SPACE_REL, tc_app(C_ACONV, aa));
  Term ha[6] = { p1->hyps_term, p2->hyps_term, ht, p1->deps_term, p2->deps_term, dt };
  Occ oh = tc_post(SPACE_REL, tc_app(C_HDUNION, ha));
  Occ prem[4] = { p1->occ, p2->occ, oa, oh };
  Occ occ = tc_fire(R_TRANS, NULL, prem, NULL);
  return thm_register(occ, ht, concl, dt, hyps, nhyps, deps, ndeps);
}

static uint32_t rule_MK_COMB(uint32_t t1, uint32_t t2) {
  const ThmRec *p1 = &thms[t1], *p2 = &thms[t2];
  Term l1, r1, l2, r2, dom, cod;
  if (!tm_is_eq(p1->concl, &l1, &r1) || !tm_is_eq(p2->concl, &l2, &r2)) return 0;
  if (!ty_is_fun(tm_type(l1), &dom, &cod) || dom != tm_type(l2)) return 0;
  Term concl = tm_eq(tm_comb(l1, l2), tm_comb(r1, r2));
  if (p1->nhyps == 0 && p2->nhyps == 0 && p1->ndeps == 0 && p2->ndeps == 0) {
    Occ prem[2] = { p1->occ, p2->occ };
    Occ occ = tc_fire(R_MK_COMB_FAST, NULL, prem, NULL);
    return thm_register(occ, T_HNIL, concl, T_DNIL, NULL, 0, NULL, 0);
  }
  Term *hyps = NULL; uint32_t nhyps = 0;
  uint32_t *deps = NULL; uint32_t ndeps = 0;
  term_union(p1->hyps, p1->nhyps, p2->hyps, p2->nhyps, &hyps, &nhyps);
  deps_union(p1->deps, p1->ndeps, p2->deps, p2->ndeps, &deps, &ndeps);
  Term ht = hyps_build(hyps, nhyps), dt = deps_build(deps, ndeps);
  Term ha[6] = { p1->hyps_term, p2->hyps_term, ht, p1->deps_term, p2->deps_term, dt };
  Occ oh = tc_post(SPACE_REL, tc_app(C_HDUNION, ha));
  Occ prem[3] = { p1->occ, p2->occ, oh };
  Occ occ = tc_fire(R_MK_COMB, NULL, prem, NULL);
  return thm_register(occ, ht, concl, dt, hyps, nhyps, deps, ndeps);
}

static uint32_t rule_ABS(Term v, uint32_t t1) {
  if (!v || (int)tm_con(v) != C_VAR) return 0;
  const ThmRec *p1 = &thms[t1];
  Term l, r;
  if (!tm_is_eq(p1->concl, &l, &r)) return 0;
  for (uint32_t i = 0; i < p1->nhyps; i++)
    if (vfree_in(v, p1->hyps[i])) return 0;
  Term concl = tm_eq(tm_abs(v, l), tm_abs(v, r));
  if (p1->nhyps == 0 && p1->ndeps == 0) {
    uint32_t vc; Term vty, vn, vr;
    tm_inspect(v, &vc, &vty, &vn, &vr);
    Occ prem[1] = { p1->occ };
    Term bind[5] = { vty, vn, tm_type(l), l, r };
    Occ occ = tc_fire(R_ABS_FAST, NULL, prem, bind);
    return thm_register(occ, T_HNIL, concl, T_DNIL, NULL, 0, NULL, 0);
  }
  Term *hyps = NULL;
  if (p1->nhyps) {
    hyps = (Term *)malloc((size_t)p1->nhyps * sizeof(Term));
    memcpy(hyps, p1->hyps, (size_t)p1->nhyps * sizeof(Term));
  }
  uint32_t *deps = NULL;
  if (p1->ndeps) {
    deps = (uint32_t *)malloc((size_t)p1->ndeps * sizeof(uint32_t));
    memcpy(deps, p1->deps, (size_t)p1->ndeps * sizeof(uint32_t));
  }
  Term na[2] = { v, p1->hyps_term };
  Occ onf = tc_post(SPACE_REL, tc_app(C_NOT_FREE_HYPS, na));
  Occ prem[2] = { p1->occ, onf };
  Occ occ = tc_fire(R_ABS, NULL, prem, NULL);
  return thm_register(occ, p1->hyps_term, concl, p1->deps_term, hyps, p1->nhyps, deps, p1->ndeps);
}

static uint32_t rule_EQ_MP(uint32_t t1, uint32_t t2) {
  const ThmRec *p1 = &thms[t1], *p2 = &thms[t2];
  Term l, r;
  if (!tm_is_eq(p1->concl, &l, &r) || tm_type(l) != T_BOOL) return 0;
  if (l != p2->concl && alphaorder(l, p2->concl) != 0) return 0;
  if (l == p2->concl && p1->nhyps == 0 && p2->nhyps == 0 && p1->ndeps == 0 && p2->ndeps == 0) {
    Occ prem[2] = { p1->occ, p2->occ };
    Occ occ = tc_fire(R_EQ_MP_FAST, NULL, prem, NULL);
    return thm_register(occ, T_HNIL, r, T_DNIL, NULL, 0, NULL, 0);
  }
  Term *hyps = NULL; uint32_t nhyps = 0;
  uint32_t *deps = NULL; uint32_t ndeps = 0;
  term_union(p1->hyps, p1->nhyps, p2->hyps, p2->nhyps, &hyps, &nhyps);
  deps_union(p1->deps, p1->ndeps, p2->deps, p2->ndeps, &deps, &ndeps);
  Term ht = hyps_build(hyps, nhyps), dt = deps_build(deps, ndeps);
  Term aa[2] = { l, p2->concl };
  Occ oa = tc_post(SPACE_REL, tc_app(C_ACONV, aa));
  Term ha[6] = { p1->hyps_term, p2->hyps_term, ht, p1->deps_term, p2->deps_term, dt };
  Occ oh = tc_post(SPACE_REL, tc_app(C_HDUNION, ha));
  Occ prem[4] = { p1->occ, p2->occ, oa, oh };
  Occ occ = tc_fire(R_EQ_MP, NULL, prem, NULL);
  return thm_register(occ, ht, r, dt, hyps, nhyps, deps, ndeps);
}

static uint32_t rule_DEDUCT(uint32_t t1, uint32_t t2) {
  const ThmRec *p1 = &thms[t1], *p2 = &thms[t2];
  Term *h1 = NULL, *h2 = NULL, *hyps = NULL;
  uint32_t n1 = 0, n2 = 0, nhyps = 0;
  term_remove(p1->hyps, p1->nhyps, p2->concl, &h1, &n1);
  term_remove(p2->hyps, p2->nhyps, p1->concl, &h2, &n2);
  term_union(h1, n1, h2, n2, &hyps, &nhyps);
  free(h1); free(h2);
  uint32_t *deps = NULL; uint32_t ndeps = 0;
  deps_union(p1->deps, p1->ndeps, p2->deps, p2->ndeps, &deps, &ndeps);
  Term ht = hyps_build(hyps, nhyps), dt = deps_build(deps, ndeps);
  Term concl = tm_eq(p1->concl, p2->concl);
  Term da[8] = {
    p1->hyps_term, p1->concl, p2->hyps_term, p2->concl,
    ht, p1->deps_term, p2->deps_term, dt
  };
  Occ od = tc_post(SPACE_REL, tc_app(C_DEDUCT_CERT, da));
  Occ prem[3] = { p1->occ, p2->occ, od };
  Occ occ = tc_fire(R_DEDUCT, NULL, prem, NULL);
  return thm_register(occ, ht, concl, dt, hyps, nhyps, deps, ndeps);
}

static uint32_t rule_INST_TYPE(const TyPair *theta, size_t n, uint32_t t1) {
  for (size_t i = 0; i < n; i++) {
    if (!theta[i].repl || !theta[i].key) return 0;
    uint32_t con; int ar; const Term *a;
    ty_inspect(theta[i].key, &con, &ar, &a);
    if ((int)con != C_TYVAR) return 0;
  }
  const ThmRec *p1 = &thms[t1];
  Term concl = hol_inst(theta, n, p1->concl);
  if (!concl) return 0;
  Term *hyps = NULL; uint32_t nhyps = 0;
  for (uint32_t i = 0; i < p1->nhyps; i++) {
    Term h = hol_inst(theta, n, p1->hyps[i]);
    if (!h) { free(hyps); return 0; }
    Term *nh = NULL; uint32_t nnh = 0;
    term_union(hyps, nhyps, &h, 1, &nh, &nnh);
    free(hyps);
    hyps = nh; nhyps = nnh;
  }
  uint32_t *deps = NULL;
  if (p1->ndeps) {
    deps = (uint32_t *)malloc((size_t)p1->ndeps * sizeof(uint32_t));
    memcpy(deps, p1->deps, (size_t)p1->ndeps * sizeof(uint32_t));
  }
  Term ht = hyps_build(hyps, nhyps);
  Term sa[4] = { p1->hyps_term, p1->concl, ht, concl };
  Occ os = tc_post(SPACE_REL, tc_app(C_SUBST_CERT, sa));
  Occ prem[2] = { p1->occ, os };
  Occ occ = tc_fire(R_INST_TYPE, NULL, prem, NULL);
  return thm_register(occ, ht, concl, p1->deps_term, hyps, nhyps, deps, p1->ndeps);
}

static uint32_t rule_INST(const TmPair *theta, size_t n, uint32_t t1) {
  if (!vsubst_check(theta, n)) return 0;
  const ThmRec *p1 = &thms[t1];
  VsList il = { theta, n, vs_dom_sig(theta, n), next_memo_ctx() };
  Term concl = n ? vs_rec(&il, p1->concl) : p1->concl;
  if (!concl) return 0;
  Term *hyps = NULL; uint32_t nhyps = 0;
  for (uint32_t i = 0; i < p1->nhyps; i++) {
    il.ctx = next_memo_ctx();
    Term h = n ? vs_rec(&il, p1->hyps[i]) : p1->hyps[i];
    if (!h) { free(hyps); return 0; }
    Term *nh = NULL; uint32_t nnh = 0;
    term_union(hyps, nhyps, &h, 1, &nh, &nnh);
    free(hyps);
    hyps = nh; nhyps = nnh;
  }
  uint32_t *deps = NULL;
  if (p1->ndeps) {
    deps = (uint32_t *)malloc((size_t)p1->ndeps * sizeof(uint32_t));
    memcpy(deps, p1->deps, (size_t)p1->ndeps * sizeof(uint32_t));
  }
  Term ht = hyps_build(hyps, nhyps);
  Term sa[4] = { p1->hyps_term, p1->concl, ht, concl };
  Occ os = tc_post(SPACE_REL, tc_app(C_SUBST_CERT, sa));
  Occ prem[2] = { p1->occ, os };
  Occ occ = tc_fire(R_INST, NULL, prem, NULL);
  return thm_register(occ, ht, concl, p1->deps_term, hyps, nhyps, deps, p1->ndeps);
}

/* ---- Standard HOL Light axiom/definition recognition ---- */
#if __has_include("hol_std_data.inc")
#include "hol_std_data.inc"
#elif __has_include("../hyperon/CeTTa/native/hol_light/hol_std_data.inc")
#include "../hyperon/CeTTa/native/hol_light/hol_std_data.inc"
#elif __has_include("../../../hyperon/CeTTa/native/hol_light/hol_std_data.inc")
#include "../../../hyperon/CeTTa/native/hol_light/hol_std_data.inc"
#else
#include "../../hyperon/CeTTa/native/hol_light/hol_std_data.inc"
#endif

/* ---- Environment & Declarations ---- */
static uint32_t decl_new(uint32_t parent, uint8_t kind, uint8_t auth, HolName name) {
  if (ndecls + 1 >= capdecls) {
    capdecls = capdecls ? capdecls * 2 : 1024;
    decls = (Decl *)realloc(decls, (size_t)capdecls * sizeof(Decl));
  }
  uint32_t id = ++ndecls;
  uint8_t pol = parent ? decls[parent].policy : POL_OPEN;
  uint64_t nid = tc_fresh_name();
  Term dt = tc_name((uint16_t)S_NAME, nid);
  ensure_tm(dt);
  TM[dt].anchor = id;
  decls[id] = (Decl){
    id, parent, 0, 0, kind, auth, pol, 0, name, dt, 0, 0, -1, 0, 0, 0
  };
  if (kind == DECL_TYPE || kind == DECL_TYDEF) {
    decls[id].next_same = names[name].types;
    names[name].types = id;
  } else if (kind == DECL_CONST || kind == DECL_DEF ||
             kind == DECL_TYDEF_ABS || kind == DECL_TYDEF_REP) {
    decls[id].next_same = names[name].consts;
    names[name].consts = id;
  }
  return id;
}

static bool env_dominates(uint32_t sub, uint32_t anc) {
  if (!anc) return true;
  if (sub < anc) return false;
  for (uint32_t d = sub; d >= anc; d = decls[d].parent) {
    if (d == anc) return true;
    if (!decls[d].parent) break;
  }
  return false;
}

static uint32_t lookup_type(uint32_t env, HolName name) {
  for (uint32_t d = names[name].types; d; d = decls[d].next_same)
    if (d <= env && env_dominates(env, d)) return d;
  return 0;
}

static uint32_t lookup_const(uint32_t env, HolName name) {
  for (uint32_t d = names[name].consts; d; d = decls[d].next_same)
    if (d <= env && env_dominates(env, d)) return d;
  return 0;
}

static bool ty_visible_in(uint32_t env, Term ty) {
  return ty && env_dominates(env, TM[ty].anchor);
}

static bool tm_visible_in(uint32_t env, Term tm) {
  return tm && env_dominates(env, TM[tm].anchor);
}

static bool thm_visible_in(uint32_t env, uint32_t th) {
  return th && env_dominates(env, thms[th].anchor);
}

static Term mk_type_in(uint32_t env, HolName name, const Term *args, uint32_t n) {
  uint32_t d = lookup_type(env, name);
  if (!d || decls[d].arity != n) return 0;
  for (uint32_t i = 0; i < n; i++)
    if (!ty_visible_in(env, args[i])) return 0;
  return ty_app(d, args, n);
}

static bool type_match_rec(Term pat, Term tgt, TyPair *env, size_t *n, size_t cap) {
  uint32_t cp, ct; int ap, at; const Term *argp, *argt;
  ty_inspect(pat, &cp, &ap, &argp);
  ty_inspect(tgt, &ct, &at, &argt);
  if ((int)cp == C_TYVAR) {
    for (size_t i = 0; i < *n; i++)
      if (env[i].key == pat) return env[i].repl == tgt;
    if (*n >= cap) return false;
    env[(*n)++] = (TyPair){ tgt, pat };
    return true;
  }
  if (cp != ct || ap != at) return false;
  Term lp[TC_ARGS], lt[TC_ARGS];
  for (int i = 0; i < ap; i++) { lp[i] = argp[i]; lt[i] = argt[i]; }
  for (int i = 0; i < ap; i++)
    if (!type_match_rec(lp[i], lt[i], env, n, cap)) return false;
  return true;
}

static bool type_is_instance(Term pat, Term tgt) {
  TyPair env[64];
  size_t n = 0;
  return type_match_rec(pat, tgt, env, &n, 64);
}

static Term mk_const_at(uint32_t env, HolName name, Term ty) {
  if (!ty_visible_in(env, ty)) return 0;
  uint32_t d = lookup_const(env, name);
  if (!d || !type_is_instance(decls[d].gtype, ty)) return 0;
  return tm_const(d, ty);
}

static int hol_con(int sort, int arity, const int *asorts) {
  Binder b[TC_ARGS];
  for (int i = 0; i < arity; i++) b[i] = (Binder){ (uint16_t)asorts[i], 0, 0 };
  return tc_con((uint16_t)sort, 0, arity, arity ? b : NULL);
}

static uint32_t env_new_type(uint32_t env, HolName name, uint32_t arity) {
  if (!env || arity > TC_ARGS) return 0;
  if (lookup_type(env, name)) return 0;
  int sorts[TC_ARGS];
  for (uint32_t i = 0; i < arity; i++) sorts[i] = S_TYPE;
  int tcon = hol_con(S_TYPE, (int)arity, arity ? sorts : NULL);
  if (tcon < 0) return 0;
  uint32_t d = decl_new(env, DECL_TYPE, AUTH_DECL, name);
  decls[d].arity = arity;
  decls[d].tcon = tcon;
  tcon_to_decl[tcon] = d;
  return d;
}

static uint32_t env_new_constant(uint32_t env, HolName name, Term ty) {
  if (!env || !ty_visible_in(env, ty)) return 0;
  if (lookup_const(env, name)) return 0;
  uint32_t d = decl_new(env, DECL_CONST, AUTH_DECL, name);
  decls[d].gtype = ty;
  return d;
}

static uint8_t classify_std_axiom(uint32_t env, Term concl);

static uint32_t env_new_axiom(uint32_t env, HolName name, Term concl) {
  if (!env || decls[env].policy == POL_SEALED) return 0;
  if (!tm_visible_in(env, concl) || tm_type(concl) != T_BOOL) return 0;
  uint8_t auth = classify_std_axiom(env, concl);
  if (decls[env].policy == POL_STANDARD && auth == AUTH_USER_AX) return 0;
  uint32_t d = decl_new(env, DECL_AXIOM, auth, name);
  decls[d].gtype = T_BOOL;
  decls[d].body = concl;
  uint32_t *deps = (uint32_t *)malloc(sizeof(uint32_t));
  deps[0] = d;
  Term dt = deps_build(deps, 1);
  Term aa[2] = { concl, decls[d].dterm };
  Occ oa = tc_post(SPACE_REL, tc_app(C_AXIOM_CERT, aa));
  Occ prem[1] = { oa };
  Occ occ = tc_fire(R_NEW_AXIOM, NULL, prem, NULL);
  uint32_t th = thm_register(occ, T_HNIL, concl, dt, NULL, 0, deps, 1);
  decls[d].thm1 = th;
  return d;
}

static bool subset_tyvars(const TermVec *sub, const TermVec *sup) {
  for (size_t i = 0; i < sub->n; i++)
    if (!tvec_mem(sup, sub->v[i])) return false;
  return true;
}

static uint32_t env_new_definition(uint32_t env, Term eq) {
  if (!env || !tm_visible_in(env, eq)) return 0;
  Term lhs, rhs;
  if (!tm_is_eq(eq, &lhs, &rhs)) return 0;
  if ((int)tm_con(lhs) != C_VAR) return 0;
  HolName cname = tm_leaf_name(lhs);
  Term cty = tm_type(lhs);
  if (lookup_const(env, cname)) return 0;
  if (!freesin_closed(rhs)) return 0;
  TermVec rtv = {0}, ctv = {0};
  type_vars_in_term_exact(rhs, &rtv);
  tyvars_exact(cty, &ctv);
  bool ok = subset_tyvars(&rtv, &ctv);
  free(rtv.v); free(ctv.v);
  if (!ok) return 0;
  uint32_t d = decl_new(env, DECL_DEF, AUTH_DEF, cname);
  decls[d].gtype = cty;
  decls[d].body = rhs;
  Term ctm = tm_const(d, cty);
  Term concl = tm_eq(ctm, rhs);
  Term da[2] = { ctm, rhs };
  Occ od = tc_post(SPACE_REL, tc_app(C_DEF_CERT, da));
  Occ prem[1] = { od };
  Occ occ = tc_fire(R_NEW_DEF, NULL, prem, NULL);
  decls[d].thm1 = thm_register(occ, T_HNIL, concl, T_DNIL, NULL, 0, NULL, 0);
  return d;
}

static int cmp_tyvar_Asc(const void *a, const void *b) {
  return ty_compare(*(const Term *)a, *(const Term *)b);
}

static uint32_t env_new_typedef(uint32_t env, HolName tyname, HolName absname,
                                HolName repname, uint32_t witness_thm) {
  if (!env || !thm_visible_in(env, witness_thm))
    return 0;
  if (lookup_type(env, tyname) || lookup_const(env, absname) ||
      lookup_const(env, repname) || absname == repname)
    return 0;
  const ThmRec *w = &thms[witness_thm];
  if (w->nhyps != 0) return 0;
  uint32_t wc; Term wty, P, x;
  tm_inspect(w->concl, &wc, &wty, &P, &x);
  if ((int)wc != C_COMB || !freesin_closed(P)) return 0;
  Term rty, cod;
  if (!ty_is_fun(tm_type(P), &rty, &cod) || cod != T_BOOL) return 0;
  TermVec tv = {0};
  type_vars_in_term_exact(P, &tv);
  if (tv.n > TC_ARGS) { free(tv.v); return 0; }
  if (tv.n > 1) qsort(tv.v, tv.n, sizeof(Term), cmp_tyvar_Asc);

  int sorts[TC_ARGS];
  for (size_t i = 0; i < tv.n; i++) sorts[i] = S_TYPE;
  int tcon = hol_con(S_TYPE, (int)tv.n, tv.n ? sorts : NULL);
  if (tcon < 0) { free(tv.v); return 0; }
  uint32_t dt = decl_new(env, DECL_TYDEF, AUTH_DEF, tyname);
  decls[dt].arity = (uint32_t)tv.n;
  decls[dt].tcon = tcon;
  decls[dt].body = P;
  decls[dt].witness_thm = witness_thm;
  tcon_to_decl[tcon] = dt;

  Term aty = ty_app(dt, tv.v, (uint32_t)tv.n);
  free(tv.v);
  Term abs_ty = ty_fun(rty, aty), rep_ty = ty_fun(aty, rty);
  uint32_t dabs = decl_new(dt, DECL_TYDEF_ABS, AUTH_DEF, absname);
  decls[dabs].gtype = abs_ty;
  uint32_t drep = decl_new(dabs, DECL_TYDEF_REP, AUTH_DEF, repname);
  decls[drep].gtype = rep_ty;

  Term abs_c = tm_const(dabs, abs_ty), rep_c = tm_const(drep, rep_ty);
  Term va = tm_var(N_a, aty), vr = tm_var(N_r, rty);
  Term c1 = tm_eq(tm_comb(abs_c, tm_comb(rep_c, va)), va);
  Term c2 = tm_eq(tm_comb(P, vr), tm_eq(tm_comb(rep_c, tm_comb(abs_c, vr)), vr));

  uint32_t *d1 = NULL, *d2 = NULL;
  if (w->ndeps) {
    d1 = (uint32_t *)malloc((size_t)w->ndeps * sizeof(uint32_t));
    d2 = (uint32_t *)malloc((size_t)w->ndeps * sizeof(uint32_t));
    memcpy(d1, w->deps, (size_t)w->ndeps * sizeof(uint32_t));
    memcpy(d2, w->deps, (size_t)w->ndeps * sizeof(uint32_t));
  }
  Term ta[4] = { P, x, c1, c2 };
  Occ ot = tc_post(SPACE_REL, tc_app(C_TYDEF_CERT, ta));
  Occ prem[2] = { w->occ, ot };
  Occ o1 = tc_fire(R_NEW_TYDEF1, NULL, prem, NULL);
  Occ o2 = tc_fire(R_NEW_TYDEF2, NULL, prem, NULL);
  uint32_t th1 = thm_register(o1, T_HNIL, c1, w->deps_term, NULL, 0, d1, w->ndeps);
  uint32_t th2 = thm_register(o2, T_HNIL, c2, w->deps_term, NULL, 0, d2, w->ndeps);
  decls[dt].thm1 = th1; decls[dt].thm2 = th2;
  decls[dabs].thm1 = th1; decls[dabs].thm2 = th2;
  decls[drep].thm1 = th1; decls[drep].thm2 = th2;
  return drep;
}

static uint32_t env_set_policy(uint32_t env, uint8_t policy) {
  if (!env || policy > POL_SEALED || policy < decls[env].policy) return 0;
  uint32_t d = decl_new(env, DECL_POLICY, AUTH_POLICY, N_BOOL);
  decls[d].policy = policy;
  return d;
}

/* ---- Canonical Printer & Parser ---- */
typedef struct { char *s; size_t len, cap; } StrBuf;
static void sb_reserve(StrBuf *b, size_t add) {
  if (b->len + add + 1 <= b->cap) return;
  size_t c = b->cap ? b->cap : 128;
  while (c < b->len + add + 1) c *= 2;
  b->s = (char *)realloc(b->s, c);
  b->cap = c;
}
static void sb_bytes(StrBuf *b, const char *s, size_t n) {
  sb_reserve(b, n);
  memcpy(b->s + b->len, s, n);
  b->len += n;
  b->s[b->len] = 0;
}
static void sb_cstr(StrBuf *b, const char *s) { sb_bytes(b, s, strlen(s)); }
static void sb_ch(StrBuf *b, char c) { sb_bytes(b, &c, 1); }
static void sb_quoted(StrBuf *b, HolName n) {
  const NameRec *r = &names[n];
  sb_ch(b, '"');
  for (uint32_t i = 0; i < r->len; i++) {
    unsigned char c = (unsigned char)r->bytes[i];
    if (c == '\\' || c == '"') { sb_ch(b, '\\'); sb_ch(b, (char)c); }
    else if (c < 0x20 || c > 0x7e) {
      char hex[5]; snprintf(hex, sizeof(hex), "\\x%02x", (unsigned)c);
      sb_cstr(b, hex);
    } else sb_ch(b, (char)c);
  }
  sb_ch(b, '"');
}

static void sb_type(StrBuf *b, Term ty) {
  uint32_t con; int ar; const Term *a;
  ty_inspect(ty, &con, &ar, &a);
  if ((int)con == C_TYVAR) {
    sb_cstr(b, "(V ");
    sb_quoted(b, (HolName)TM[a[0]].anchor);
    sb_ch(b, ')');
    return;
  }
  uint32_t d = tcon_to_decl[con];
  sb_cstr(b, "(T ");
  sb_quoted(b, decls[d].name);
  Term args[TC_ARGS];
  for (int i = 0; i < ar; i++) args[i] = a[i];
  for (int i = 0; i < ar; i++) { sb_ch(b, ' '); sb_type(b, args[i]); }
  sb_ch(b, ')');
}

static void sb_term(StrBuf *b, Term tm) {
  uint32_t con; Term ty, l, r;
  tm_inspect(tm, &con, &ty, &l, &r);
  if ((int)con == C_VAR || (int)con == C_CONST) {
    sb_cstr(b, (int)con == C_VAR ? "(v " : "(c ");
    sb_quoted(b, tm_leaf_name(tm));
    sb_ch(b, ' ');
    sb_type(b, ty);
    sb_ch(b, ')');
  } else {
    sb_cstr(b, (int)con == C_COMB ? "(A " : "(L ");
    sb_term(b, l);
    sb_ch(b, ' ');
    sb_term(b, r);
    sb_ch(b, ')');
  }
}

static char *print_thm(uint32_t th) {
  const ThmRec *p = &thms[th];
  StrBuf b = {0};
  sb_cstr(&b, "(thm (");
  for (uint32_t i = 0; i < p->nhyps; i++) {
    if (i) sb_ch(&b, ' ');
    sb_term(&b, p->hyps[i]);
  }
  sb_cstr(&b, ") ");
  sb_term(&b, p->concl);
  sb_ch(&b, ')');
  return b.s;
}

typedef struct { const char *s; size_t len, pos; uint32_t env; } PCur;
static void p_ws(PCur *c) {
  while (c->pos < c->len) {
    unsigned char ch = (unsigned char)c->s[c->pos];
    if (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r') c->pos++;
    else break;
  }
}
static bool p_ch(PCur *c, char ch) {
  p_ws(c);
  if (c->pos >= c->len || c->s[c->pos] != ch) return false;
  c->pos++;
  return true;
}
static int hex_v(char ch) {
  if (ch >= '0' && ch <= '9') return ch - '0';
  if (ch >= 'a' && ch <= 'f') return 10 + (ch - 'a');
  if (ch >= 'A' && ch <= 'F') return 10 + (ch - 'A');
  return -1;
}
static HolName p_qname(PCur *c) {
  if (!p_ch(c, '"')) return 0;
  StrBuf b = {0};
  sb_reserve(&b, 16);
  while (c->pos < c->len) {
    char ch = c->s[c->pos++];
    if (ch == '"') {
      HolName nm = name_intern(b.s ? b.s : "", b.len);
      free(b.s);
      return nm;
    }
    if (ch == '\\') {
      if (c->pos >= c->len) { free(b.s); return 0; }
      char e = c->s[c->pos++];
      if (e == '\\' || e == '"') sb_ch(&b, e);
      else if (e == 'x' && c->len - c->pos >= 2) {
        int hi = hex_v(c->s[c->pos++]), lo = hex_v(c->s[c->pos++]);
        if (hi < 0 || lo < 0) { free(b.s); return 0; }
        sb_ch(&b, (char)((hi << 4) | lo));
      } else { free(b.s); return 0; }
    } else sb_ch(&b, ch);
  }
  free(b.s);
  return 0;
}

static Term p_type(PCur *c) {
  if (!p_ch(c, '(')) return 0;
  p_ws(c);
  if (c->pos >= c->len) return 0;
  char tag = c->s[c->pos++];
  HolName nm = p_qname(c);
  if (!nm) return 0;
  if (tag == 'V') {
    if (!p_ch(c, ')')) return 0;
    return ty_var(nm);
  }
  if (tag == 'T') {
    TermVec a = {0};
    for (;;) {
      p_ws(c);
      if (c->pos >= c->len) { free(a.v); return 0; }
      if (c->s[c->pos] == ')') { c->pos++; break; }
      Term sub = p_type(c);
      if (!sub) { free(a.v); return 0; }
      tvec_push(&a, sub);
    }
    Term out = mk_type_in(c->env, nm, a.v, (uint32_t)a.n);
    free(a.v);
    return out;
  }
  return 0;
}

static Term p_term(PCur *c) {
  if (!p_ch(c, '(')) return 0;
  p_ws(c);
  if (c->pos >= c->len) return 0;
  char tag = c->s[c->pos++];
  if (tag == 'v' || tag == 'c') {
    HolName nm = p_qname(c);
    if (!nm) return 0;
    Term ty = p_type(c);
    if (!ty || !p_ch(c, ')')) return 0;
    return tag == 'v' ? tm_var(nm, ty) : mk_const_at(c->env, nm, ty);
  }
  if (tag == 'A' || tag == 'L') {
    Term l = p_term(c);
    if (!l) return 0;
    Term r = p_term(c);
    if (!r || !p_ch(c, ')')) return 0;
    return tag == 'A' ? tm_comb(l, r) : tm_abs(l, r);
  }
  return 0;
}

static Term parse_type_cstr(uint32_t env, const char *s) {
  PCur c = { s, strlen(s), 0, env };
  Term t = p_type(&c);
  p_ws(&c);
  return c.pos == c.len ? t : 0;
}

static Term parse_term_cstr(uint32_t env, const char *s) {
  PCur c = { s, strlen(s), 0, env };
  Term t = p_term(&c);
  p_ws(&c);
  return c.pos == c.len ? t : 0;
}

static bool name_is_cstr(HolName nm, const char *s) {
  size_t n = strlen(s);
  return names[nm].len == n && memcmp(names[nm].bytes, s, n) == 0;
}

static int std_def_index_by_name(HolName nm) {
  size_t n = sizeof(hol_std_defs) / sizeof(hol_std_defs[0]);
  for (size_t i = 0; i < n; i++)
    if (name_is_cstr(nm, hol_std_defs[i].name)) return (int)i;
  return -1;
}

static bool all_standard(Term tm);

static bool decl_standard(uint32_t did) {
  if (!did) return false;
  Decl *d = &decls[did];
  if (d->std_cert == 1) return true;
  if (d->std_cert == 2) return false;
  bool ok = false;
  switch (d->kind) {
    case DECL_TYPE:
      ok = d->auth == AUTH_PRIM || (name_is_cstr(d->name, "ind") && d->arity == 0);
      break;
    case DECL_CONST:
      if (d->auth == AUTH_PRIM) ok = true;
      else if (name_is_cstr(d->name, "@")) {
        Term ty = parse_type_cstr(d->parent, hol_std_choice_type);
        ok = (ty != 0 && ty == d->gtype);
      }
      break;
    case DECL_DEF: {
      int idx = std_def_index_by_name(d->name);
      if (idx >= 0) {
        Term ty = parse_type_cstr(d->parent, hol_std_defs[idx].type);
        if (ty && ty == d->gtype) {
          Term body = parse_term_cstr(d->parent, hol_std_defs[idx].body);
          if (body && alphaorder(body, d->body) == 0 && all_standard(d->body))
            ok = true;
        }
      }
      break;
    }
    case DECL_AXIOM:
      ok = (d->auth >= AUTH_STD_ETA && d->auth <= AUTH_STD_INFINITY);
      break;
    default:
      ok = false;
      break;
  }
  d->std_cert = ok ? 1 : 2;
  return ok;
}

static bool type_standard(Term ty) {
  uint32_t con; int ar; const Term *a;
  ty_inspect(ty, &con, &ar, &a);
  if ((int)con == C_TYVAR) return true;
  uint32_t d = tcon_to_decl[con];
  if (!decl_standard(d)) return false;
  Term args[TC_ARGS];
  for (int i = 0; i < ar; i++) args[i] = a[i];
  for (int i = 0; i < ar; i++)
    if (!type_standard(args[i])) return false;
  return true;
}

static bool all_standard(Term tm) {
  uint32_t con; Term ty, l, r;
  tm_inspect(tm, &con, &ty, &l, &r);
  if (!type_standard(ty)) return false;
  if ((int)con == C_VAR) return true;
  if ((int)con == C_CONST) return decl_standard(TM[l].anchor);
  return all_standard(l) && all_standard(r);
}

static uint8_t classify_std_axiom(uint32_t env, Term concl) {
  static const uint8_t auths[3] = { AUTH_STD_ETA, AUTH_STD_SELECT, AUTH_STD_INFINITY };
  for (int i = 0; i < 3; i++) {
    Term std = parse_term_cstr(env, hol_std_axioms[i]);
    if (!std) continue;
    if (alphaorder(std, concl) == 0 && all_standard(concl))
      return auths[i];
  }
  return AUTH_USER_AX;
}

/* ---- tcalc HOL Light Kernel Bootstrap ---- */
static Term mk_eq_pat(Term ty, Term l, Term r) {
  Term fa[2] = { ty, T_BOOL };
  Term f1 = tc_app(C_FUN, fa);
  Term fa2[2] = { ty, f1 };
  Term f2 = tc_app(C_FUN, fa2);
  Term ca[2] = { f2, decls[D_EQ].dterm };
  Term eqc = tc_app(C_CONST, ca);
  Term a1[3] = { f1, eqc, l };
  Term c1 = tc_app(C_COMB, a1);
  Term a2[3] = { T_BOOL, c1, r };
  return tc_app(C_COMB, a2);
}

static Term mk_thm_pat(Term h, Term c, Term d) {
  Term a[3] = { h, c, d };
  return tc_app(C_THM, a);
}

static Term mk_wt_pat(Term ty, Term tm) {
  Term a[2] = { ty, tm };
  return tc_app(C_WT, a);
}

static void hol_ctx(int nvars, const int *vsorts) {
  Binder b[TC_VARS];
  for (int i = 0; i < nvars; i++) b[i] = (Binder){ (uint16_t)vsorts[i], 0, 0 };
  tc_ctx(nvars, nvars ? b : NULL);
}

static int hol_rule(int nkeep, const Pat *keep, Term make_t, uint8_t make_sp) {
  Rule r;
  memset(&r, 0, sizeof(r));
  r.fresh = -1;
  r.nkeep = (uint8_t)nkeep;
  for (int i = 0; i < nkeep; i++) r.keep[i] = keep[i];
  r.make = (Pat){ make_t, make_sp };
  return tc_rule(&r);
}

static void hol_tc_init(void) {
  tc_init(1u << 22, 1u << 21);
  S_NAME = tc_sort(SORT_PURE | SORT_FREE);
  S_TYPE = tc_sort(0);
  S_TERM = tc_sort(0);
  S_HYPS = tc_sort(0);
  S_DEPS = tc_sort(0);
  S_CERT = tc_sort(SORT_PROVABLE);
  S_WT   = tc_sort(SORT_PROVABLE);
  S_THM  = tc_sort(SORT_PROVABLE);

  int s_name1[1] = { S_NAME };
  int s_type2[2] = { S_TYPE, S_TYPE };
  int s_ty_nm[2] = { S_TYPE, S_NAME };
  int s_tm3[3]   = { S_TYPE, S_TERM, S_TERM };
  int s_hcons[2] = { S_TERM, S_HYPS };
  int s_dcons[2] = { S_NAME, S_DEPS };
  int s_wt[2]    = { S_TYPE, S_TERM };
  int s_thm[3]   = { S_HYPS, S_TERM, S_DEPS };
  int s_tm2[2]   = { S_TERM, S_TERM };
  int s_hdu[6]   = { S_HYPS, S_HYPS, S_HYPS, S_DEPS, S_DEPS, S_DEPS };
  int s_nfh[2]   = { S_TERM, S_HYPS };
  int s_ded[8]   = { S_HYPS, S_TERM, S_HYPS, S_TERM, S_HYPS, S_DEPS, S_DEPS, S_DEPS };
  int s_sub[4]   = { S_HYPS, S_TERM, S_HYPS, S_TERM };
  int s_ax[2]    = { S_TERM, S_NAME };
  int s_tyd[4]   = { S_TERM, S_TERM, S_TERM, S_TERM };

  C_TYVAR = hol_con(S_TYPE, 1, s_name1);
  C_FUN   = hol_con(S_TYPE, 2, s_type2);
  C_BOOL  = hol_con(S_TYPE, 0, NULL);

  C_VAR   = hol_con(S_TERM, 2, s_ty_nm);
  C_CONST = hol_con(S_TERM, 2, s_ty_nm);
  C_COMB  = hol_con(S_TERM, 3, s_tm3);
  C_ABS   = hol_con(S_TERM, 3, s_tm3);

  C_HNIL  = hol_con(S_HYPS, 0, NULL);
  C_HCONS = hol_con(S_HYPS, 2, s_hcons);
  C_DNIL  = hol_con(S_DEPS, 0, NULL);
  C_DCONS = hol_con(S_DEPS, 2, s_dcons);

  C_WT    = hol_con(S_WT,  2, s_wt);
  C_THM   = hol_con(S_THM, 3, s_thm);

  C_CONST_INST    = hol_con(S_CERT, 2, s_ty_nm);
  C_ACONV         = hol_con(S_CERT, 2, s_tm2);
  C_HDUNION       = hol_con(S_CERT, 6, s_hdu);
  C_NOT_FREE_HYPS = hol_con(S_CERT, 2, s_nfh);
  C_DEDUCT_CERT   = hol_con(S_CERT, 8, s_ded);
  C_SUBST_CERT    = hol_con(S_CERT, 4, s_sub);
  C_AXIOM_CERT    = hol_con(S_CERT, 2, s_ax);
  C_DEF_CERT      = hol_con(S_CERT, 2, s_tm2);
  C_TYDEF_CERT    = hol_con(S_CERT, 4, s_tyd);

  T_BOOL = tc_app(C_BOOL, NULL); ensure_tm(T_BOOL);
  T_HNIL = tc_app(C_HNIL, NULL); ensure_tm(T_HNIL);
  T_DNIL = tc_app(C_DNIL, NULL); ensure_tm(T_DNIL);

  N_FUN  = name_intern("fun", 3);
  N_BOOL = name_intern("bool", 4);
  N_EQ   = name_intern("=", 1);
  N_A    = name_intern("A", 1);
  N_a    = name_intern("a", 1);
  N_r    = name_intern("r", 1);

  D_FUN = decl_new(0, DECL_TYPE, AUTH_PRIM, N_FUN);
  decls[D_FUN].arity = 2; decls[D_FUN].tcon = C_FUN; tcon_to_decl[C_FUN] = D_FUN;
  D_BOOL = decl_new(D_FUN, DECL_TYPE, AUTH_PRIM, N_BOOL);
  decls[D_BOOL].arity = 0; decls[D_BOOL].tcon = C_BOOL; tcon_to_decl[C_BOOL] = D_BOOL;

  TM[T_BOOL].init = 1; TM[T_BOOL].anchor = D_BOOL;
  T_ATY = ty_var(N_A);
  D_EQ = decl_new(D_BOOL, DECL_CONST, AUTH_PRIM, N_EQ);
  decls[D_EQ].gtype = ty_fun(T_ATY, ty_fun(T_ATY, T_BOOL));

  /* Well-typed term formation rules in SPACE_WT */
  {
    int vs[2] = { S_TYPE, S_NAME }; hol_ctx(2, vs);
    Term A = tc_v(0), n = tc_v(1);
    Term va[2] = { A, n };
    R_WT_VAR = hol_rule(0, NULL, mk_wt_pat(A, tc_app(C_VAR, va)), SPACE_WT);
    Term ca[2] = { A, n };
    Pat p[1] = { { tc_app(C_CONST_INST, ca), SPACE_REL } };
    R_WT_CONST = hol_rule(1, p, mk_wt_pat(A, tc_app(C_CONST, ca)), SPACE_WT);
  }
  {
    int vs[4] = { S_TYPE, S_TYPE, S_TERM, S_TERM }; hol_ctx(4, vs);
    Term A = tc_v(0), B = tc_v(1), f = tc_v(2), x = tc_v(3);
    Term fa[2] = { A, B }, ca[3] = { B, f, x };
    Pat p[2] = { { mk_wt_pat(tc_app(C_FUN, fa), f), SPACE_WT }, { mk_wt_pat(A, x), SPACE_WT } };
    R_WT_COMB = hol_rule(2, p, mk_wt_pat(B, tc_app(C_COMB, ca)), SPACE_WT);
  }
  {
    int vs[4] = { S_TYPE, S_TYPE, S_NAME, S_TERM }; hol_ctx(4, vs);
    Term A = tc_v(0), B = tc_v(1), n = tc_v(2), bod = tc_v(3);
    Term va[2] = { A, n }, v = tc_app(C_VAR, va);
    Term fa[2] = { A, B }, fab = tc_app(C_FUN, fa);
    Term aa[3] = { fab, v, bod };
    Pat p[2] = { { mk_wt_pat(A, v), SPACE_WT }, { mk_wt_pat(B, bod), SPACE_WT } };
    R_WT_ABS = hol_rule(2, p, mk_wt_pat(fab, tc_app(C_ABS, aa)), SPACE_WT);
  }

  /* 10 Primitive HOL Light Inference Rules in SPACE_THM */
  {
    int vs[2] = { S_TYPE, S_TERM }; hol_ctx(2, vs);
    Term A = tc_v(0), t = tc_v(1);
    R_REFL = hol_rule(0, NULL, mk_thm_pat(T_HNIL, mk_eq_pat(A, t, t), T_DNIL), SPACE_THM);
  }
  {
    int vs[4] = { S_TYPE, S_TYPE, S_NAME, S_TERM }; hol_ctx(4, vs);
    Term A = tc_v(0), B = tc_v(1), n = tc_v(2), bod = tc_v(3);
    Term va[2] = { A, n }, v = tc_app(C_VAR, va);
    Term fa[2] = { A, B }, fab = tc_app(C_FUN, fa);
    Term aa[3] = { fab, v, bod }, lam = tc_app(C_ABS, aa);
    Term ca[3] = { B, lam, v }, red = tc_app(C_COMB, ca);
    R_BETA = hol_rule(0, NULL, mk_thm_pat(T_HNIL, mk_eq_pat(B, red, bod), T_DNIL), SPACE_THM);
  }
  {
    int vs[1] = { S_TERM }; hol_ctx(1, vs);
    Term p = tc_v(0);
    Pat pr[1] = { { mk_wt_pat(T_BOOL, p), SPACE_WT } };
    Term ha[2] = { p, T_HNIL };
    R_ASSUME = hol_rule(1, pr, mk_thm_pat(tc_app(C_HCONS, ha), p, T_DNIL), SPACE_THM);
  }
  {
    int vs[4] = { S_TYPE, S_TERM, S_TERM, S_TERM }; hol_ctx(4, vs);
    Term A = tc_v(0), l = tc_v(1), m = tc_v(2), r = tc_v(3);
    Pat pr[2] = { { mk_thm_pat(T_HNIL, mk_eq_pat(A, l, m), T_DNIL), SPACE_THM },
                  { mk_thm_pat(T_HNIL, mk_eq_pat(A, m, r), T_DNIL), SPACE_THM } };
    R_TRANS_FAST = hol_rule(2, pr, mk_thm_pat(T_HNIL, mk_eq_pat(A, l, r), T_DNIL), SPACE_THM);
  }
  {
    int vs[11] = { S_TYPE, S_TERM, S_TERM, S_TERM, S_TERM, S_HYPS, S_HYPS, S_HYPS, S_DEPS, S_DEPS, S_DEPS };
    hol_ctx(11, vs);
    Term A = tc_v(0), l = tc_v(1), m1 = tc_v(2), m2 = tc_v(3), r = tc_v(4);
    Term H1 = tc_v(5), H2 = tc_v(6), H3 = tc_v(7);
    Term D1 = tc_v(8), D2 = tc_v(9), D3 = tc_v(10);
    Term aa[2] = { m1, m2 }, ha[6] = { H1, H2, H3, D1, D2, D3 };
    Pat pr[4] = {
      { mk_thm_pat(H1, mk_eq_pat(A, l, m1), D1), SPACE_THM },
      { mk_thm_pat(H2, mk_eq_pat(A, m2, r), D2), SPACE_THM },
      { tc_app(C_ACONV, aa), SPACE_REL },
      { tc_app(C_HDUNION, ha), SPACE_REL }
    };
    R_TRANS = hol_rule(4, pr, mk_thm_pat(H3, mk_eq_pat(A, l, r), D3), SPACE_THM);
  }
  {
    int vs[6] = { S_TYPE, S_TYPE, S_TERM, S_TERM, S_TERM, S_TERM }; hol_ctx(6, vs);
    Term A = tc_v(0), B = tc_v(1), f = tc_v(2), g = tc_v(3), x = tc_v(4), y = tc_v(5);
    Term fa[2] = { A, B }, fab = tc_app(C_FUN, fa);
    Term fx[3] = { B, f, x }, gy[3] = { B, g, y };
    Pat pr[2] = {
      { mk_thm_pat(T_HNIL, mk_eq_pat(fab, f, g), T_DNIL), SPACE_THM },
      { mk_thm_pat(T_HNIL, mk_eq_pat(A, x, y), T_DNIL), SPACE_THM }
    };
    R_MK_COMB_FAST = hol_rule(2, pr,
      mk_thm_pat(T_HNIL, mk_eq_pat(B, tc_app(C_COMB, fx), tc_app(C_COMB, gy)), T_DNIL), SPACE_THM);
  }
  {
    int vs[12] = { S_TYPE, S_TYPE, S_TERM, S_TERM, S_TERM, S_TERM, S_HYPS, S_HYPS, S_HYPS, S_DEPS, S_DEPS, S_DEPS };
    hol_ctx(12, vs);
    Term A = tc_v(0), B = tc_v(1), f = tc_v(2), g = tc_v(3), x = tc_v(4), y = tc_v(5);
    Term H1 = tc_v(6), H2 = tc_v(7), H3 = tc_v(8);
    Term D1 = tc_v(9), D2 = tc_v(10), D3 = tc_v(11);
    Term fa[2] = { A, B }, fab = tc_app(C_FUN, fa);
    Term fx[3] = { B, f, x }, gy[3] = { B, g, y };
    Term ha[6] = { H1, H2, H3, D1, D2, D3 };
    Pat pr[3] = {
      { mk_thm_pat(H1, mk_eq_pat(fab, f, g), D1), SPACE_THM },
      { mk_thm_pat(H2, mk_eq_pat(A, x, y), D2), SPACE_THM },
      { tc_app(C_HDUNION, ha), SPACE_REL }
    };
    R_MK_COMB = hol_rule(3, pr,
      mk_thm_pat(H3, mk_eq_pat(B, tc_app(C_COMB, fx), tc_app(C_COMB, gy)), D3), SPACE_THM);
  }
  {
    int vs[5] = { S_TYPE, S_NAME, S_TYPE, S_TERM, S_TERM }; hol_ctx(5, vs);
    Term A = tc_v(0), n = tc_v(1), B = tc_v(2), l = tc_v(3), r = tc_v(4);
    Term va[2] = { A, n }, v = tc_app(C_VAR, va);
    Term fa[2] = { A, B }, fab = tc_app(C_FUN, fa);
    Term al[3] = { fab, v, l }, ar[3] = { fab, v, r };
    Pat pr[1] = { { mk_thm_pat(T_HNIL, mk_eq_pat(B, l, r), T_DNIL), SPACE_THM } };
    R_ABS_FAST = hol_rule(1, pr,
      mk_thm_pat(T_HNIL, mk_eq_pat(fab, tc_app(C_ABS, al), tc_app(C_ABS, ar)), T_DNIL), SPACE_THM);
  }
  {
    int vs[7] = { S_TYPE, S_NAME, S_TYPE, S_TERM, S_TERM, S_HYPS, S_DEPS }; hol_ctx(7, vs);
    Term A = tc_v(0), n = tc_v(1), B = tc_v(2), l = tc_v(3), r = tc_v(4);
    Term H = tc_v(5), D = tc_v(6);
    Term va[2] = { A, n }, v = tc_app(C_VAR, va);
    Term fa[2] = { A, B }, fab = tc_app(C_FUN, fa);
    Term al[3] = { fab, v, l }, ar[3] = { fab, v, r };
    Term na[2] = { v, H };
    Pat pr[2] = {
      { mk_thm_pat(H, mk_eq_pat(B, l, r), D), SPACE_THM },
      { tc_app(C_NOT_FREE_HYPS, na), SPACE_REL }
    };
    R_ABS = hol_rule(2, pr,
      mk_thm_pat(H, mk_eq_pat(fab, tc_app(C_ABS, al), tc_app(C_ABS, ar)), D), SPACE_THM);
  }
  {
    int vs[2] = { S_TERM, S_TERM }; hol_ctx(2, vs);
    Term p = tc_v(0), q = tc_v(1);
    Pat pr[2] = {
      { mk_thm_pat(T_HNIL, mk_eq_pat(T_BOOL, p, q), T_DNIL), SPACE_THM },
      { mk_thm_pat(T_HNIL, p, T_DNIL), SPACE_THM }
    };
    R_EQ_MP_FAST = hol_rule(2, pr, mk_thm_pat(T_HNIL, q, T_DNIL), SPACE_THM);
  }
  {
    int vs[9] = { S_TERM, S_TERM, S_TERM, S_HYPS, S_HYPS, S_HYPS, S_DEPS, S_DEPS, S_DEPS };
    hol_ctx(9, vs);
    Term p1 = tc_v(0), q = tc_v(1), p2 = tc_v(2);
    Term H1 = tc_v(3), H2 = tc_v(4), H3 = tc_v(5);
    Term D1 = tc_v(6), D2 = tc_v(7), D3 = tc_v(8);
    Term aa[2] = { p1, p2 }, ha[6] = { H1, H2, H3, D1, D2, D3 };
    Pat pr[4] = {
      { mk_thm_pat(H1, mk_eq_pat(T_BOOL, p1, q), D1), SPACE_THM },
      { mk_thm_pat(H2, p2, D2), SPACE_THM },
      { tc_app(C_ACONV, aa), SPACE_REL },
      { tc_app(C_HDUNION, ha), SPACE_REL }
    };
    R_EQ_MP = hol_rule(4, pr, mk_thm_pat(H3, q, D3), SPACE_THM);
  }
  {
    int vs[8] = { S_HYPS, S_TERM, S_HYPS, S_TERM, S_HYPS, S_DEPS, S_DEPS, S_DEPS };
    hol_ctx(8, vs);
    Term H1 = tc_v(0), p = tc_v(1), H2 = tc_v(2), q = tc_v(3);
    Term H3 = tc_v(4), D1 = tc_v(5), D2 = tc_v(6), D3 = tc_v(7);
    Term da[8] = { H1, p, H2, q, H3, D1, D2, D3 };
    Pat pr[3] = {
      { mk_thm_pat(H1, p, D1), SPACE_THM },
      { mk_thm_pat(H2, q, D2), SPACE_THM },
      { tc_app(C_DEDUCT_CERT, da), SPACE_REL }
    };
    R_DEDUCT = hol_rule(3, pr, mk_thm_pat(H3, mk_eq_pat(T_BOOL, p, q), D3), SPACE_THM);
  }
  {
    int vs[5] = { S_HYPS, S_TERM, S_DEPS, S_HYPS, S_TERM }; hol_ctx(5, vs);
    Term H = tc_v(0), c = tc_v(1), D = tc_v(2), Hp = tc_v(3), cp = tc_v(4);
    Term sa[4] = { H, c, Hp, cp };
    Pat pr[2] = {
      { mk_thm_pat(H, c, D), SPACE_THM },
      { tc_app(C_SUBST_CERT, sa), SPACE_REL }
    };
    R_INST_TYPE = hol_rule(2, pr, mk_thm_pat(Hp, cp, D), SPACE_THM);
    R_INST      = hol_rule(2, pr, mk_thm_pat(Hp, cp, D), SPACE_THM);
  }
  {
    int vs[2] = { S_TERM, S_NAME }; hol_ctx(2, vs);
    Term c = tc_v(0), d = tc_v(1);
    Term aa[2] = { c, d }, da[2] = { d, T_DNIL };
    Pat pr[1] = { { tc_app(C_AXIOM_CERT, aa), SPACE_REL } };
    R_NEW_AXIOM = hol_rule(1, pr, mk_thm_pat(T_HNIL, c, tc_app(C_DCONS, da)), SPACE_THM);
  }
  {
    int vs[3] = { S_TYPE, S_NAME, S_TERM }; hol_ctx(3, vs);
    Term A = tc_v(0), d = tc_v(1), rhs = tc_v(2);
    Term ca[2] = { A, d }, ctm = tc_app(C_CONST, ca);
    Term da[2] = { ctm, rhs };
    Pat pr[1] = { { tc_app(C_DEF_CERT, da), SPACE_REL } };
    R_NEW_DEF = hol_rule(1, pr, mk_thm_pat(T_HNIL, mk_eq_pat(A, ctm, rhs), T_DNIL), SPACE_THM);
  }
  {
    int vs[5] = { S_TERM, S_TERM, S_TERM, S_TERM, S_DEPS }; hol_ctx(5, vs);
    Term P = tc_v(0), x = tc_v(1), c1 = tc_v(2), c2 = tc_v(3), D = tc_v(4);
    Term wa[3] = { T_BOOL, P, x }, ta[4] = { P, x, c1, c2 };
    Pat pr[2] = {
      { mk_thm_pat(T_HNIL, tc_app(C_COMB, wa), D), SPACE_THM },
      { tc_app(C_TYDEF_CERT, ta), SPACE_REL }
    };
    R_NEW_TYDEF1 = hol_rule(2, pr, mk_thm_pat(T_HNIL, c1, D), SPACE_THM);
    R_NEW_TYDEF2 = hol_rule(2, pr, mk_thm_pat(T_HNIL, c2, D), SPACE_THM);
  }

  tc_protect(SPACE_WT);
  tc_protect(SPACE_THM);
  tc_seal();
}

/* ---- HOLRPLY1 Binary Stream Replay & Spec Verification ---- */
static const uint8_t holr_kernel_sha[32] = {
  0x29, 0x54, 0x4b, 0xe9, 0x2d, 0x9c, 0xc1, 0xe6,
  0xb3, 0xb5, 0x9b, 0xa5, 0xb2, 0x10, 0x60, 0x4b,
  0x9a, 0x74, 0x83, 0x66, 0xa6, 0x8b, 0x3b, 0xcd,
  0xc2, 0x61, 0x97, 0x17, 0xd6, 0x8f, 0xd9, 0x8a
};

enum {
  HOLR_NAME           = 0x01,
  HOLR_TYVAR          = 0x02,
  HOLR_TYAPP          = 0x03,
  HOLR_VAR            = 0x04,
  HOLR_CONST          = 0x05,
  HOLR_COMB           = 0x06,
  HOLR_ABS            = 0x07,
  HOLR_REFL           = 0x10,
  HOLR_TRANS          = 0x11,
  HOLR_MK_COMB        = 0x12,
  HOLR_ABS_RULE       = 0x13,
  HOLR_BETA           = 0x14,
  HOLR_ASSUME         = 0x15,
  HOLR_EQ_MP          = 0x16,
  HOLR_DEDUCT         = 0x17,
  HOLR_INST_TYPE      = 0x18,
  HOLR_INST           = 0x19,
  HOLR_NEW_TYPE       = 0x20,
  HOLR_NEW_CONSTANT   = 0x21,
  HOLR_NEW_AXIOM      = 0x22,
  HOLR_NEW_DEFINITION = 0x23,
  HOLR_NEW_TYPEDEF    = 0x24,
  HOLR_POLICY         = 0x25,
  HOLR_EXPECT         = 0x30,
  HOLR_LABEL          = 0x31,
  HOLR_EMIT           = 0x32,
  HOLR_EXPECT_REFUSED = 0x33,
  HOLR_EXPECT_AXIOMS  = 0x34,
  HOLR_EXPECT_ALPHA   = 0x35,
  HOLR_DROP_TYPE      = 0x40,
  HOLR_DROP_TERM      = 0x41,
  HOLR_DROP_THM       = 0x42,
  HOLR_END            = 0x7f
};

enum { ST_NONE = 0, ST_OK = 1, ST_FAILED = 2, ST_DROPPED = 3 };

typedef struct { uint8_t op, nout; char out; const char *layout; } OpInfo;
static const OpInfo op_table[] = {
  { HOLR_NAME,           1, 'N', "b"     },
  { HOLR_TYVAR,          1, 'Y', "N"     },
  { HOLR_TYAPP,          1, 'Y', "N*Y"   },
  { HOLR_VAR,            1, 'T', "NY"    },
  { HOLR_CONST,          1, 'T', "NY"    },
  { HOLR_COMB,           1, 'T', "TT"    },
  { HOLR_ABS,            1, 'T', "TT"    },
  { HOLR_REFL,           1, 'H', "T"     },
  { HOLR_TRANS,          1, 'H', "HH"    },
  { HOLR_MK_COMB,        1, 'H', "HH"    },
  { HOLR_ABS_RULE,       1, 'H', "TH"    },
  { HOLR_BETA,           1, 'H', "T"     },
  { HOLR_ASSUME,         1, 'H', "T"     },
  { HOLR_EQ_MP,          1, 'H', "HH"    },
  { HOLR_DEDUCT,         1, 'H', "HH"    },
  { HOLR_INST_TYPE,      1, 'H', "%YYH"  },
  { HOLR_INST,           1, 'H', "%TTH"  },
  { HOLR_NEW_TYPE,       0, 0,   "Nu"    },
  { HOLR_NEW_CONSTANT,   0, 0,   "NY"    },
  { HOLR_NEW_AXIOM,      1, 'H', "T"     },
  { HOLR_NEW_DEFINITION, 1, 'H', "T"     },
  { HOLR_NEW_TYPEDEF,    2, 'H', "NNNH"  },
  { HOLR_POLICY,         0, 0,   "u"     },
  { HOLR_EXPECT,         0, 0,   "H*TT"  },
  { HOLR_LABEL,          0, 0,   "HN"    },
  { HOLR_EMIT,           0, 0,   "H"     },
  { HOLR_EXPECT_REFUSED, 0, 0,   ""      },
  { HOLR_EXPECT_AXIOMS,  0, 0,   "H*H"   },
  { HOLR_EXPECT_ALPHA,   0, 0,   "H*TT"  },
  { HOLR_DROP_TYPE,      0, 0,   "y"     },
  { HOLR_DROP_TERM,      0, 0,   "t"     },
  { HOLR_DROP_THM,       0, 0,   "h"     },
  { HOLR_END,            0, 0,   "uc"    }
};

static const OpInfo *find_op(uint8_t op) {
  for (size_t i = 0; i < sizeof(op_table) / sizeof(op_table[0]); i++)
    if (op_table[i].op == op) return &op_table[i];
  return NULL;
}

typedef struct {
  uint32_t *obj;
  uint8_t *st;
  uint64_t n, cap;
} IdSpace;

static void idspace_put(IdSpace *s, uint32_t v, uint8_t st) {
  if (s->n == s->cap) {
    s->cap = s->cap ? s->cap * 2 : 512;
    s->obj = (uint32_t *)realloc(s->obj, (size_t)s->cap * sizeof(uint32_t));
    s->st  = (uint8_t *)realloc(s->st, (size_t)s->cap);
  }
  s->obj[s->n] = v;
  s->st[s->n] = st;
  s->n++;
}

typedef struct {
  uint32_t env, records, n_emits, cap_emits;
  uint32_t *emits;
  HolName *emit_labels;
} ReplayOut;

typedef struct { const uint8_t *p, *end; bool err; } BCur;

static const uint8_t *cur_bytes(BCur *c, size_t n) {
  if (c->err || (size_t)(c->end - c->p) < n) { c->err = true; return NULL; }
  const uint8_t *r = c->p;
  c->p += n;
  return r;
}

static uint64_t cur_uv(BCur *c) {
  if (c->err) return 0;
  uint64_t v = 0;
  for (unsigned i = 0; i < 9; i++) {
    if (c->p == c->end) { c->err = true; return 0; }
    uint8_t b = *c->p++;
    v |= (uint64_t)(b & 0x7f) << (7 * i);
    if ((b & 0x80) == 0) {
      if (i > 0 && b == 0) { c->err = true; return 0; }
      if (v >= (1ULL << 62)) { c->err = true; return 0; }
      return v;
    }
  }
  c->err = true;
  return 0;
}

static uint64_t cur_u64le(BCur *c) {
  const uint8_t *p = cur_bytes(c, 8);
  if (!p) return 0;
  uint64_t v = 0;
  for (int i = 0; i < 8; i++) v |= (uint64_t)p[i] << (8 * i);
  return v;
}

typedef struct {
  uint8_t op;
  const OpInfo *info;
  uint64_t a[4];
  size_t na;
  uint64_t *v;
  uint64_t nv, capv;
  const uint8_t *bytes;
  uint64_t nbytes;
} Rec;

static bool decode_rec(BCur *c, Rec *rc) {
  const uint8_t *opb = cur_bytes(c, 1);
  if (!opb) return false;
  rc->op = *opb;
  rc->info = find_op(rc->op);
  if (!rc->info) { c->err = true; return false; }
  rc->na = 0; rc->nv = 0; rc->bytes = NULL; rc->nbytes = 0;
  for (const char *f = rc->info->layout; *f; f++) {
    if (*f == 'b') {
      uint64_t n = cur_uv(c);
      if (c->err || n > (1u << 20)) return false;
      rc->bytes = cur_bytes(c, (size_t)n);
      rc->nbytes = n;
    } else if (*f == '*' || *f == '%') {
      bool pairs = (*f == '%');
      f += pairs ? 2 : 1;
      uint64_t n = cur_uv(c);
      if (c->err || n > (1u << 22)) return false;
      uint64_t items = pairs ? 2 * n : n;
      if (items > rc->capv) {
        rc->capv = items;
        rc->v = (uint64_t *)realloc(rc->v, (size_t)items * sizeof(uint64_t));
      }
      rc->nv = items;
      for (uint64_t i = 0; i < items; i++) {
        rc->v[i] = cur_uv(c);
        if (c->err) return false;
      }
    } else if (*f == 'c') {
      rc->a[rc->na++] = cur_u64le(c);
    } else {
      rc->a[rc->na++] = cur_uv(c);
    }
    if (c->err) return false;
  }
  return true;
}

static bool sequent_matches(uint32_t thid, const Term *hyps, uint64_t nh, Term concl, bool alpha) {
  const ThmRec *th = &thms[thid];
  if (!alpha) {
    if (th->concl != concl || th->nhyps != nh) return false;
    for (uint64_t i = 0; i < nh; i++)
      if (th->hyps[i] != hyps[i]) return false;
    return true;
  }
  if (alphaorder(th->concl, concl) != 0) return false;
  for (int dir = 0; dir < 2; dir++) {
    uint64_t na = dir ? nh : th->nhyps, nb = dir ? th->nhyps : nh;
    for (uint64_t i = 0; i < na; i++) {
      Term x = dir ? hyps[i] : th->hyps[i];
      bool found = false;
      for (uint64_t j = 0; j < nb && !found; j++) {
        Term y = dir ? th->hyps[j] : hyps[j];
        found = (alphaorder(x, y) == 0);
      }
      if (!found) return false;
    }
  }
  return true;
}

static int cmp_u64_asc(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : (x > y ? 1 : 0);
}

static bool axioms_match(const IdSpace *th_sp, const uint64_t *ax_slots, uint64_t nax_slots,
                         uint32_t thid, const uint64_t *ids, uint64_t n) {
  const ThmRec *th = &thms[thid];
  if (n != th->ndeps) return false;
  uint64_t *s = (uint64_t *)malloc((size_t)(n ? n : 1) * sizeof(uint64_t));
  if (n) memcpy(s, ids, (size_t)n * sizeof(uint64_t));
  qsort(s, (size_t)n, sizeof(uint64_t), cmp_u64_asc);
  bool ok = true;
  for (uint64_t i = 0; ok && i < n; i++) {
    if (i > 0 && s[i] == s[i - 1]) { ok = false; break; }
    uint64_t lo = 0, hi = nax_slots;
    while (lo < hi) {
      uint64_t mid = lo + (hi - lo) / 2;
      if (ax_slots[mid] < s[i]) lo = mid + 1; else hi = mid;
    }
    if (lo == nax_slots || ax_slots[lo] != s[i]) { ok = false; break; }
    uint32_t ax_th = th_sp->obj[s[i]];
    if (!ax_th || thms[ax_th].ndeps != 1) { ok = false; break; }
    uint32_t ax_decl = thms[ax_th].deps[0];
    bool found = false;
    for (uint32_t j = 0; j < th->ndeps && !found; j++)
      found = (th->deps[j] == ax_decl);
    ok = found;
  }
  free(s);
  return ok;
}

static int check_ref_space(const IdSpace *sp, char kind, uint64_t id) {
  if (id >= sp->n) return 3;
  uint8_t st = sp->st[id];
  if (kind >= 'a' && kind <= 'z') return st == ST_OK ? 0 : 3;
  if (st == ST_OK) return 0;
  if (st == ST_FAILED) return 2;
  return 3;
}

static bool hol_replay_bytes(const unsigned char *bytes, size_t len, ReplayOut *out) {
  memset(out, 0, sizeof(*out));
  BCur hdr = { bytes, bytes + len, false };
  const uint8_t *m = cur_bytes(&hdr, 8);
  if (!m || memcmp(m, "HOLRPLY1", 8) != 0) return false;
  const uint8_t *sha = cur_bytes(&hdr, 32);
  if (!sha || memcmp(sha, holr_kernel_sha, 32) != 0) return false;
  uint64_t version = cur_uv(&hdr);
  uint64_t profile = cur_uv(&hdr);
  uint64_t policy  = cur_uv(&hdr);
  uint64_t flags   = cur_uv(&hdr);
  if (hdr.err || version != 1 || profile != 0 || policy > POL_SEALED || (flags & ~1ULL) != 0)
    return false;
  bool probe = (flags & 1ULL) != 0;
  uint32_t env = D_EQ;
  if (policy > POL_OPEN) {
    env = env_set_policy(env, (uint8_t)policy);
    if (!env) return false;
  }
  size_t pos = (size_t)(hdr.p - bytes);
  uint64_t fnv = fnv1a(bytes, pos, FNV_OFFSET);

  HolName *nm_tab = NULL;
  uint64_t nnm = 0, capnm = 0;
  IdSpace ty_sp = {0}, tm_sp = {0}, th_sp = {0};
  uint64_t *ax_slots = NULL;
  uint64_t nax_slots = 0, capax = 0;
  uint64_t *lbl_thm = NULL;
  HolName  *lbl_nm  = NULL;
  uint64_t nlbl = 0, caplbl = 0;
  uint64_t *emit_slots = NULL;
  uint64_t nemit_slots = 0, capemit = 0;
  bool last_refused = false, accepted = false;
  Rec rc = {0};

  while (pos < len) {
    BCur c = { bytes + pos, bytes + len, false };
    if (!decode_rec(&c, &rc)) goto done;
    size_t rec_len = (size_t)(c.p - (bytes + pos));
    if (rc.op == HOLR_END) {
      if (rc.a[0] != out->records || rc.a[1] != fnv) goto done;
      pos += rec_len;
      if (pos != len) goto done;
      accepted = true;
      break;
    }

    /* Validate references */
    int vstat = 0;
    size_t ai = 0;
    for (const char *f = rc.info->layout; *f && vstat == 0; f++) {
      if (*f == 'b' || *f == 'u' || *f == 'c') {
        if (*f != 'b') ai++;
        continue;
      }
      if (*f == '*' || *f == '%') {
        bool pairs = (*f == '%');
        char k1 = f[1], k2 = pairs ? f[2] : f[1];
        f += pairs ? 2 : 1;
        for (uint64_t i = 0; i < rc.nv; i++) {
          char k = (pairs && (i & 1)) ? k2 : k1;
          if (k == 'N') { if (rc.v[i] >= nnm) { vstat = 3; break; } }
          else {
            const IdSpace *sp = k == 'Y' ? &ty_sp : k == 'T' ? &tm_sp : &th_sp;
            int r = check_ref_space(sp, k, rc.v[i]);
            if (r == 3) { vstat = 3; break; }
            if (r == 2) vstat = 2;
          }
        }
        continue;
      }
      char k = *f;
      uint64_t id = rc.a[ai++];
      if (k == 'N') { if (id >= nnm) { vstat = 3; break; } }
      else {
        const IdSpace *sp = (k == 'Y' || k == 'y') ? &ty_sp
                          : (k == 'T' || k == 't') ? &tm_sp : &th_sp;
        int r = check_ref_space(sp, k, id);
        if (r == 3) { vstat = 3; break; }
        if (r == 2) vstat = 2;
      }
    }
    if (vstat == 3) goto done;

    uint32_t out_val[2] = {0, 0};
    uint32_t new_env = 0;
    HolName out_nm = 0;
    int estat = vstat; /* 0=ok, 1=refused, 2=depfail, 3=malformed, 5=checkfail */

    if (estat == 0) {
      const uint64_t *a = rc.a;
      #define RNM(i) (nm_tab[a[i]])
      #define RTY(i) ((Term)ty_sp.obj[a[i]])
      #define RTM(i) ((Term)tm_sp.obj[a[i]])
      #define RTH(i) (th_sp.obj[a[i]])
      switch (rc.op) {
        case HOLR_NAME:
          out_nm = name_intern((const char *)rc.bytes, (size_t)rc.nbytes);
          if (!out_nm) goto done;
          break;
        case HOLR_TYVAR:
          out_val[0] = ty_var(RNM(0));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_TYAPP: {
          if (rc.nv > TC_ARGS) { estat = 1; break; }
          Term args[TC_ARGS];
          for (uint64_t i = 0; i < rc.nv; i++) args[i] = (Term)ty_sp.obj[rc.v[i]];
          out_val[0] = mk_type_in(env, RNM(0), args, (uint32_t)rc.nv);
          if (!out_val[0]) estat = 1;
          break;
        }
        case HOLR_VAR:
          out_val[0] = tm_var(RNM(0), RTY(1));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_CONST:
          out_val[0] = mk_const_at(env, RNM(0), RTY(1));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_COMB:
          out_val[0] = tm_comb(RTM(0), RTM(1));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_ABS:
          out_val[0] = tm_abs(RTM(0), RTM(1));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_REFL:
          out_val[0] = rule_REFL(RTM(0));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_BETA:
          out_val[0] = rule_BETA(RTM(0));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_ASSUME:
          out_val[0] = rule_ASSUME(RTM(0));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_TRANS:
          out_val[0] = rule_TRANS(RTH(0), RTH(1));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_MK_COMB:
          out_val[0] = rule_MK_COMB(RTH(0), RTH(1));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_EQ_MP:
          out_val[0] = rule_EQ_MP(RTH(0), RTH(1));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_DEDUCT:
          out_val[0] = rule_DEDUCT(RTH(0), RTH(1));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_ABS_RULE:
          out_val[0] = rule_ABS(RTM(0), RTH(1));
          if (!out_val[0]) estat = 1;
          break;
        case HOLR_INST_TYPE: {
          uint64_t np = rc.nv / 2;
          TyPair *p = np ? (TyPair *)malloc((size_t)np * sizeof(TyPair)) : NULL;
          for (uint64_t i = 0; i < np; i++)
            p[i] = (TyPair){ (Term)ty_sp.obj[rc.v[2 * i]], (Term)ty_sp.obj[rc.v[2 * i + 1]] };
          out_val[0] = rule_INST_TYPE(p, (size_t)np, RTH(0));
          free(p);
          if (!out_val[0]) estat = 1;
          break;
        }
        case HOLR_INST: {
          uint64_t np = rc.nv / 2;
          TmPair *p = np ? (TmPair *)malloc((size_t)np * sizeof(TmPair)) : NULL;
          for (uint64_t i = 0; i < np; i++)
            p[i] = (TmPair){ (Term)tm_sp.obj[rc.v[2 * i]], (Term)tm_sp.obj[rc.v[2 * i + 1]] };
          out_val[0] = rule_INST(p, (size_t)np, RTH(0));
          free(p);
          if (!out_val[0]) estat = 1;
          break;
        }
        case HOLR_NEW_TYPE:
          if (a[1] > TC_ARGS) { estat = 3; break; }
          new_env = env_new_type(env, RNM(0), (uint32_t)a[1]);
          if (!new_env) estat = 1;
          break;
        case HOLR_NEW_CONSTANT:
          new_env = env_new_constant(env, RNM(0), RTY(1));
          if (!new_env) estat = 1;
          break;
        case HOLR_NEW_AXIOM:
          new_env = env_new_axiom(env, 0, RTM(0));
          if (!new_env) estat = 1;
          else out_val[0] = decls[new_env].thm1;
          break;
        case HOLR_NEW_DEFINITION:
          new_env = env_new_definition(env, RTM(0));
          if (!new_env) estat = 1;
          else out_val[0] = decls[new_env].thm1;
          break;
        case HOLR_NEW_TYPEDEF:
          new_env = env_new_typedef(env, RNM(0), RNM(1), RNM(2), RTH(3));
          if (!new_env) estat = 1;
          else { out_val[0] = decls[new_env].thm1; out_val[1] = decls[new_env].thm2; }
          break;
        case HOLR_POLICY:
          if (a[0] > POL_SEALED) { estat = 3; break; }
          if (a[0] > decls[env].policy) {
            new_env = env_set_policy(env, (uint8_t)a[0]);
            if (!new_env) estat = 1;
          }
          break;
        case HOLR_EXPECT:
        case HOLR_EXPECT_ALPHA: {
          Term *hyps = rc.nv ? (Term *)malloc((size_t)rc.nv * sizeof(Term)) : NULL;
          for (uint64_t i = 0; i < rc.nv; i++) hyps[i] = (Term)tm_sp.obj[rc.v[i]];
          bool m = sequent_matches(RTH(0), hyps, rc.nv, RTM(1), rc.op == HOLR_EXPECT_ALPHA);
          free(hyps);
          if (!m) estat = 5;
          break;
        }
        case HOLR_EXPECT_AXIOMS:
          if (!axioms_match(&th_sp, ax_slots, nax_slots, RTH(0), rc.v, rc.nv)) estat = 5;
          break;
        case HOLR_EXPECT_REFUSED:
          if (!last_refused) estat = 5;
          break;
        case HOLR_LABEL:
          out_nm = RNM(1);
          break;
        case HOLR_EMIT:
        case HOLR_DROP_TYPE:
        case HOLR_DROP_TERM:
        case HOLR_DROP_THM:
          break;
        default:
          estat = 3;
          break;
      }
      #undef RNM
      #undef RTY
      #undef RTM
      #undef RTH
    }

    if (estat == 3) goto done;
    if ((estat == 1 || estat == 5) && !probe) goto done;

    IdSpace *outsp = rc.info->out == 'Y' ? &ty_sp
                   : rc.info->out == 'T' ? &tm_sp
                   : rc.info->out == 'H' ? &th_sp : NULL;
    uint64_t first = outsp ? outsp->n : 0;

    if (rc.op == HOLR_NAME) {
      if (nnm == capnm) {
        capnm = capnm ? capnm * 2 : 512;
        nm_tab = (HolName *)realloc(nm_tab, (size_t)capnm * sizeof(HolName));
      }
      nm_tab[nnm++] = out_nm;
    } else if (estat == 0) {
      if (outsp) {
        for (uint8_t i = 0; i < rc.info->nout; i++)
          idspace_put(outsp, out_val[i], ST_OK);
      }
      if (new_env) env = new_env;
      if (rc.op == HOLR_NEW_AXIOM) {
        if (nax_slots == capax) {
          capax = capax ? capax * 2 : 32;
          ax_slots = (uint64_t *)realloc(ax_slots, (size_t)capax * sizeof(uint64_t));
        }
        ax_slots[nax_slots++] = first;
      }
      if (rc.op == HOLR_LABEL) {
        if (nlbl == caplbl) {
          caplbl = caplbl ? caplbl * 2 : 64;
          lbl_thm = (uint64_t *)realloc(lbl_thm, (size_t)caplbl * sizeof(uint64_t));
          lbl_nm  = (HolName *)realloc(lbl_nm, (size_t)caplbl * sizeof(HolName));
        }
        lbl_thm[nlbl] = rc.a[0];
        lbl_nm[nlbl]  = out_nm;
        nlbl++;
      }
      if (rc.op == HOLR_EMIT) {
        if (nemit_slots == capemit) {
          capemit = capemit ? capemit * 2 : 64;
          emit_slots = (uint64_t *)realloc(emit_slots, (size_t)capemit * sizeof(uint64_t));
        }
        emit_slots[nemit_slots++] = rc.a[0];
      }
      if (rc.op == HOLR_DROP_TYPE) ty_sp.st[rc.a[0]] = ST_DROPPED;
      if (rc.op == HOLR_DROP_TERM) tm_sp.st[rc.a[0]] = ST_DROPPED;
      if (rc.op == HOLR_DROP_THM)  th_sp.st[rc.a[0]] = ST_DROPPED;
    } else {
      if (outsp) {
        for (uint8_t i = 0; i < rc.info->nout; i++)
          idspace_put(outsp, 0, ST_FAILED);
      }
    }

    last_refused = (estat == 1 || estat == 2);
    fnv = fnv1a(bytes + pos, rec_len, fnv);
    pos += rec_len;
    out->records++;
  }

  if (accepted) {
    out->env = env;
    out->n_emits = (uint32_t)nemit_slots;
    out->emits = (uint32_t *)calloc(nemit_slots ? (size_t)nemit_slots : 1, sizeof(uint32_t));
    out->emit_labels = (HolName *)calloc(nemit_slots ? (size_t)nemit_slots : 1, sizeof(HolName));
    for (uint64_t i = 0; i < nemit_slots; i++) {
      uint64_t slot = emit_slots[i];
      if (slot >= th_sp.n || th_sp.st[slot] != ST_OK) { accepted = false; break; }
      out->emits[i] = th_sp.obj[slot];
      for (uint64_t j = 0; j < nlbl; j++)
        if (lbl_thm[j] == slot) out->emit_labels[i] = lbl_nm[j];
    }
  }

done:
  free(rc.v);
  free(nm_tab);
  free(ty_sp.obj); free(ty_sp.st);
  free(tm_sp.obj); free(tm_sp.st);
  free(th_sp.obj); free(th_sp.st);
  free(ax_slots);
  free(lbl_thm); free(lbl_nm);
  free(emit_slots);
  return accepted;
}

static unsigned char *slurp_file(const char *path, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (!f) return NULL;
  if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return NULL; }
  long sz = ftell(f);
  if (sz < 0 || fseek(f, 0, SEEK_SET) != 0) { fclose(f); return NULL; }
  unsigned char *buf = (unsigned char *)malloc((size_t)sz + 1);
  if (sz > 0 && fread(buf, 1, (size_t)sz, f) != (size_t)sz) { free(buf); fclose(f); return NULL; }
  buf[sz] = 0;
  fclose(f);
  *out_len = (size_t)sz;
  return buf;
}

static bool parse_thm_line(uint32_t env, const char *s, size_t len,
                           TermVec *hyps, Term *concl_out) {
  PCur c = { s, len, 0, env };
  if (!p_ch(&c, '(')) return false;
  p_ws(&c);
  if (c.len - c.pos < 3 || memcmp(c.s + c.pos, "thm", 3) != 0) return false;
  c.pos += 3;
  if (!p_ch(&c, '(')) return false;
  for (;;) {
    p_ws(&c);
    if (c.pos >= c.len) return false;
    if (c.s[c.pos] == ')') { c.pos++; break; }
    Term h = p_term(&c);
    if (!h) return false;
    tvec_push(hyps, h);
  }
  Term concl = p_term(&c);
  if (!concl || !p_ch(&c, ')')) return false;
  p_ws(&c);
  if (c.pos != c.len) return false;
  *concl_out = concl;
  return true;
}

static bool verify_spec_file(const ReplayOut *r, const char *spec_path) {
  size_t len = 0;
  unsigned char *buf = slurp_file(spec_path, &len);
  if (!buf) return false;
  char *p = (char *)buf, *end = (char *)buf + len;
  uint32_t idx = 0;
  while (p < end) {
    char *nl = (char *)memchr(p, '\n', (size_t)(end - p));
    size_t l = nl ? (size_t)(nl - p) : (size_t)(end - p);
    if (l > 0 && p[l - 1] == '\r') l--;
    if (l > 0) {
      if (l >= 14 && memcmp(p, "(hol:accepted ", 14) == 0) {
        char expected[64];
        int n = snprintf(expected, sizeof(expected), "(hol:accepted %" PRIu32 " %" PRIu32 ")",
                         r->records, r->n_emits);
        if (n < 0 || (size_t)n != l || memcmp(p, expected, l) != 0) {
          free(buf);
          return false;
        }
        p = nl ? nl + 1 : end;
        continue;
      }
      if (idx >= r->n_emits) { free(buf); return false; }
      const char *seq = p;
      size_t seq_len = l;
      char *tab = (char *)memchr(p, '\t', l);
      if (tab) {
        size_t lbl_len = (size_t)(tab - p);
        seq = tab + 1;
        seq_len = l - lbl_len - 1;
        if (r->emit_labels[idx]) {
          const NameRec *nm = &names[r->emit_labels[idx]];
          if (nm->len != lbl_len || memcmp(nm->bytes, p, lbl_len) != 0) {
            free(buf);
            return false;
          }
        }
      }
      TermVec hyps = {0};
      Term concl = 0;
      bool ok = parse_thm_line(r->env, seq, seq_len, &hyps, &concl) &&
                sequent_matches(r->emits[idx], hyps.v, hyps.n, concl, true);
      free(hyps.v);
      if (!ok) { free(buf); return false; }
      idx++;
    }
    p = nl ? nl + 1 : end;
  }
  free(buf);
  return idx == r->n_emits;
}

static int run_self_tests(void) {
  hol_tc_init();
  uint32_t pass = 0, fail = 0;
  #define CHECK(cond, msg) do { \
    if (cond) pass++; \
    else { fail++; fprintf(stderr, "FAIL: %s (line %d)\n", msg, __LINE__); } \
  } while (0)

  uint32_t env = D_EQ;
  HolName nx = name_intern("x", 1), ny = name_intern("y", 1), np = name_intern("p", 1);
  Term vx = tm_var(nx, T_ATY), vy = tm_var(ny, T_ATY);
  Term vp = tm_var(np, T_BOOL);
  Term id_x = tm_abs(vx, vx), id_y = tm_abs(vy, vy);

  /* 1. Protected space enforcement: direct tc_post into SPACE_WT or SPACE_THM is refused */
  Term fake_wt_args[2] = { T_BOOL, vp };
  Term fake_thm_args[3] = { T_HNIL, vp, T_DNIL };
  CHECK(tc_post(SPACE_WT, tc_app(C_WT, fake_wt_args)) == 0, "SPACE_WT protected after seal");
  CHECK(tc_post(SPACE_THM, tc_app(C_THM, fake_thm_args)) == 0, "SPACE_THM protected after seal");

  /* 2. Term formation positive & negative */
  CHECK(tm_comb(id_x, vx) != 0, "well-typed comb accepted");
  CHECK(tm_comb(id_x, vp) == 0, "ill-typed comb refused");
  Term eq_bool = mk_const_at(env, N_EQ, ty_fun(T_BOOL, ty_fun(T_BOOL, T_BOOL)));
  CHECK(eq_bool != 0, "valid const instance accepted");
  CHECK(mk_const_at(env, N_EQ, T_BOOL) == 0, "invalid const instance refused");
  CHECK(tm_abs(eq_bool, vp) == 0, "abs over non-var refused");

  /* 3. REFL, BETA, ASSUME, TRANS, MK_COMB, ABS, EQ_MP, DEDUCT */
  uint32_t th_refl_x = rule_REFL(vx);
  CHECK(th_refl_x != 0 && thms[th_refl_x].occ != 0, "REFL(x) accepted");
  uint32_t th_beta = rule_BETA(tm_comb(id_x, vx));
  CHECK(th_beta != 0 && thms[th_beta].concl == tm_eq(tm_comb(id_x, vx), vx), "BETA((\\x.x) x) accepted");
  CHECK(rule_BETA(tm_comb(id_x, vy)) == 0, "BETA((\\x.x) y) refused (primitive BETA requires arg == bv)");
  CHECK(rule_ASSUME(vx) == 0, "ASSUME(x:A) non-bool refused");
  uint32_t th_ass_p = rule_ASSUME(vp);
  CHECK(th_ass_p != 0 && thms[th_ass_p].nhyps == 1 && thms[th_ass_p].hyps[0] == vp, "ASSUME(p:bool) accepted");

  /* Alpha-equivalent TRANS & EQ_MP */
  uint32_t th_id_x = rule_REFL(id_x), th_id_y = rule_REFL(id_y);
  uint32_t th_id_xy = rule_TRANS(th_id_x, th_id_y);
  CHECK(th_id_xy != 0 && thms[th_id_xy].concl == tm_eq(id_x, id_y), "TRANS across alpha-equiv accepted");
  CHECK(rule_TRANS(th_refl_x, th_id_x) == 0, "TRANS with non-alpha middle refused");

  /* ABS free-in-hyps guard */
  uint32_t th_ass_xx = rule_ASSUME(tm_eq(vx, vx));
  CHECK(rule_ABS(vx, th_ass_xx) == 0, "ABS(x) refused when x free in hyps");
  CHECK(rule_ABS(vy, th_ass_xx) != 0, "ABS(y) accepted when y not free in hyps");

  /* DEDUCT_ANTISYM_RULE */
  uint32_t th_ded = rule_DEDUCT(th_ass_p, th_ass_p);
  CHECK(th_ded != 0 && thms[th_ded].nhyps == 0 && thms[th_ded].concl == tm_eq(vp, vp), "DEDUCT discharges mutual hyp");

  /* INST_TYPE & capture-avoiding INST */
  TyPair typ[1] = { { T_BOOL, T_ATY } };
  uint32_t th_inst_ty = rule_INST_TYPE(typ, 1, th_refl_x);
  CHECK(th_inst_ty != 0 && thms[th_inst_ty].concl == tm_eq(tm_var(nx, T_BOOL), tm_var(nx, T_BOOL)), "INST_TYPE accepted");

  /* (\y. x) under [y/x] must rename bound y to y' so free y is not captured */
  Term lam_yx = tm_abs(vy, vx);
  uint32_t th_lam_yx = rule_REFL(lam_yx);
  TmPair tmp[1] = { { vy, vx } };
  uint32_t th_inst_tm = rule_INST(tmp, 1, th_lam_yx);
  CHECK(th_inst_tm != 0, "capture-avoiding INST accepted");
  Term lhs_i = 0, rhs_i = 0;
  CHECK(tm_is_eq(thms[th_inst_tm].concl, &lhs_i, &rhs_i), "INST conclusion is eq");
  uint32_t lc; Term lty, lbv, lbod;
  tm_inspect(lhs_i, &lc, &lty, &lbv, &lbod);
  CHECK(lbv != vy && lbod == vy, "bound variable renamed to avoid capturing free y");

  /* 4. Conservative definition & typedef guards */
  HolName nid = name_intern("my_id", 5), nbad = name_intern("bad_c", 5);
  Term vid = tm_var(nid, ty_fun(T_ATY, T_ATY));
  CHECK(env_new_definition(env, tm_eq(tm_var(nbad, T_ATY), vx)) == 0, "DEF with free var on RHS refused");
  CHECK(env_new_definition(env, tm_eq(tm_var(nbad, T_BOOL), tm_eq(vx, vx))) == 0, "DEF with unreflected tyvar refused");
  uint32_t env2 = env_new_definition(env, tm_eq(vid, id_x));
  CHECK(env2 != 0 && decls[env2].thm1 != 0, "valid conservative definition accepted");
  CHECK(env_new_definition(env2, tm_eq(vid, id_x)) == 0, "redefining constant refused");

  /* Policy enforcement on axioms */
  uint32_t env_std = env_set_policy(env2, POL_STANDARD);
  CHECK(env_std != 0, "set policy POL_STANDARD accepted");
  CHECK(env_new_axiom(env_std, 0, vp) == 0, "non-standard axiom refused under POL_STANDARD");
  CHECK(env_set_policy(env_std, POL_OPEN) == 0, "loosening policy refused");

  #undef CHECK
  printf("hol_tcalc self-tests: %" PRIu32 " passed, %" PRIu32 " failed (tcalc_steps=%" PRIu64 ")\n",
         pass, fail, tc_steps());
  return fail == 0 ? 0 : 1;
}

int main(int argc, char **argv) {
  const char *stream_path = NULL, *spec_path = NULL;
  bool print_emits = false, self_test = false;
  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--spec") == 0 && i + 1 < argc) spec_path = argv[++i];
    else if (strcmp(argv[i], "--print-emits") == 0) print_emits = true;
    else if (strcmp(argv[i], "--test") == 0) self_test = true;
    else if (!stream_path) stream_path = argv[i];
    else { fprintf(stderr, "usage: hol_tcalc [--test] [--spec FILE] [--print-emits] [STREAM.holr]\n"); return 2; }
  }
  if (self_test) return run_self_tests();
  if (!stream_path) {
    fprintf(stderr, "usage: hol_tcalc [--spec FILE] [--print-emits] STREAM.holr\n");
    return 2;
  }
  size_t len = 0;
  unsigned char *bytes = slurp_file(stream_path, &len);
  if (!bytes) { fprintf(stderr, "hol_tcalc: cannot read %s\n", stream_path); return 2; }

  double t0 = now_ms();
  hol_tc_init();
  ReplayOut r;
  if (!hol_replay_bytes(bytes, len, &r)) {
    fprintf(stderr, "hol_tcalc: REJECT %s at record %" PRIu32 "\n", stream_path, r.records);
    free(bytes);
    return 1;
  }
  if (spec_path && !verify_spec_file(&r, spec_path)) {
    fprintf(stderr, "hol_tcalc: SPEC MISMATCH %s vs %s\n", stream_path, spec_path);
    free(bytes);
    return 1;
  }
  double dt = now_ms() - t0;
  if (print_emits) {
    for (uint32_t i = 0; i < r.n_emits; i++) {
      char *s = print_thm(r.emits[i]);
      if (r.emit_labels[i])
        printf("%s\t%s\n", names[r.emit_labels[i]].bytes, s);
      else
        printf("%s\n", s);
      free(s);
    }
  }
  printf("OK %s: records=%" PRIu32 " theorems=%" PRIu32 " emits=%" PRIu32 " tcalc_steps=%" PRIu64 " time=%.1fms\n",
         stream_path, r.records, nthms, r.n_emits, tc_steps(), dt);
  free(bytes);
  return 0;
}
