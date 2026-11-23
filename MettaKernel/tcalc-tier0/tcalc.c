#include "tcalc.h"
#include <stdlib.h>
#include <string.h>
#ifdef __AVX2__
#include <immintrin.h>
#endif

/* ---- terms: hash-consed n-ary nodes; args live in one word arena ---- */
enum { F_META = 1, F_BV = 2, F_NAME = 4, F_PLAIN = 8 };
typedef struct {
  uint8_t kind, bound, flags, sort;
  uint8_t arity, pad; uint16_t cep; /* cep: context epoch */
  uint32_t head, args;
  uint64_t bm, vm;                  /* bm: bound variables it may mention; vm: holes */
} Node;
typedef struct {
  uint8_t sort, arity, ndum, isdef; Term t0;
  uint32_t abound; Term body;
  uint64_t retdeps, h0;
  uint8_t asort[TC_ARGS];
} Con;
typedef struct { uint32_t adeps[TC_ARGS]; uint8_t dsort[TC_VARS]; } ConDef;
typedef struct { uint8_t i, j, i0, j0; } Guard;
typedef struct { uint64_t avoid; uint16_t sort; uint8_t bound; } Hole;   /* a rule hole: sort, bound flag, and the holes it must avoid */
typedef struct {
  uint32_t ro; int n; uint32_t h0, kcode, mcode; /* the rule, at RP + ro; holes: HK[h0 .. h0+n) */
  Term make; uint32_t fl;                        /* flat rules: their layout, FL[fl] */
  uint8_t nkeep, mspace, fibre; bool pure, flat, mflat, prepped, fprepped, ks_zero;
  uint64_t implied, mimplied;       /* holes whose sort kept/make pattern formation guarantees */
  uint64_t bounds, pad;             /* the bound holes */
} RuleK;
typedef struct {                    /* a flat rule: premise tags, field guards, and where the result's fields come from */
  uint32_t ktag[TC_HYPS], mhead; uint16_t msort, mar, nguard, nconst;
  Guard guard[32]; uint8_t mi[TC_ARGS], mj[TC_ARGS]; Term mc[32];
} Flat;
typedef struct __attribute__((aligned(64))) {
  uint8_t perm[16];
  uint32_t mperm[4];
  uint32_t ktag[4], mtag;
  uint8_t ok, single_tag, pad[10];
} Flat4;

static Node *N; static Term *A, *H; static uint64_t *vval, *Nid, *Nmax, upair[1024];
static uint32_t *vis, *Nhslot, vgen, ugen[1024], ug, nn, ncap, na, acap, hmask; static Occ *Nocc;
static Con *C; static ConDef *CD; static int ncon; static uint8_t sorts[256]; static int nsort;
static RuleK *R; static int nr; static Hole *HK; static uint32_t nhk, hkcap; static Flat *FL; static uint32_t nfl, flcap; static uint8_t *RP; static size_t nrp, rpcap;
static Flat4 FF[64];
#define RULE(k) ((const Rule *)(RP + (k)->ro))
#define HOLE(k, h) HK[(k)->h0 + (uint32_t)(h)]
static uint32_t * code; static uint32_t ncode;
static Term *Wt, *Wtag, *Warg, *Wrow, *Wsp; static Occ *Wnext, *Wprev, Wlive; static uint8_t *Ws, *Wa, *Wmark; static uint32_t nw, wcap;
static Term *bind, *trail, qmeta[TC_VARS]; static uint16_t *Msort, *msort_prev; static uint32_t *msort_who, nmeta, ntrail;
static Term NE[65536][2], ncache[4096]; static int nne; static uint16_t ncache_sort;
static uint64_t next_name, nsteps; static uint16_t cepoch; static uint32_t tmark, tamark; static bool tscope, bscope, lok, slot_mode, wt_dirty, has_widecon, flat4_board; static bool sealed, has_take, protect[256];
static uint16_t space_sort_id; static Term space_terms[256]; static int handle_con_id; static Occ last_extra_occ[4];
static int q_quote_con, q_act_con, q_lam_con, q_app_con, rho_quote_con, rho_drop_con; static bool rho_allow_drop;
static int cn; static uint16_t csort[TC_VARS]; static uint8_t cbound[TC_VARS];
static uint64_t cbm[TC_VARS], cdeps[TC_VARS]; static Term cvar[TC_VARS], ecvar[TC_VARS];
static uint16_t bv_sort[64]; static unsigned bv_idx[64]; static int nbv;
static const RuleK *cur_k;
enum { CAP_CON = 16384, CAP_RULE = 65536, CAP_CODE = 1u << 20, CAP_META = 1u << 14 };

static Term mk(uint8_t k, uint32_t head, uint16_t s, uint8_t bound, uint64_t id, int ar, const Term *a);
static inline bool has_meta(Term t) { return (N[t].flags & F_META) != 0; }
static inline bool has_bv(Term t) { return (N[t].flags & F_BV) != 0; }
static inline bool name_ok(Term t) { return !(N[t].flags & F_NAME) || Nmax[t] <= next_name; }

bool tc_init(uint32_t nodes, uint32_t occs) {
  if (nodes > (1u << 28) || occs > (1u << 28)) return false;
  if (nodes < 256) nodes = 256;
  if (occs < 2) occs = 2;
  free(N); free(HK); HK = NULL; nhk = hkcap = 0; free(FL); FL = NULL; nfl = flcap = 0; free(RP); RP = NULL; nrp = rpcap = 0; free(A); free(H); free(vis); free(Nhslot); free(Nocc); Nocc = NULL; free(vval); free(Nid); free(Nmax); Nid = Nmax = NULL; free(C); free(CD); free(R); free(code); free(Wt); free(Wtag); free(Warg); free(Wrow); free(Wsp); free(Wnext); free(Wprev); free(Ws); free(Wa); free(Wmark); free(bind); free(trail); free(Msort); free(msort_prev); free(msort_who);
  for (hmask = 1; hmask < 4 * nodes; hmask <<= 1) {}
  ncap = nodes; acap = nodes * 4; wcap = occs;
  N = calloc(ncap, sizeof *N); A = calloc(acap, sizeof *A); H = calloc(hmask, sizeof *H);
  vis = calloc(ncap, sizeof *vis); Nhslot = calloc(ncap, sizeof *Nhslot);
  vval = calloc(ncap, sizeof *vval);
  C = calloc(CAP_CON, sizeof *C); CD = calloc(CAP_CON, sizeof *CD); R = calloc(CAP_RULE, sizeof *R); code = calloc(CAP_CODE, sizeof *code);
  Wt = calloc(wcap, sizeof *Wt); Wtag = calloc(wcap, sizeof *Wtag); Warg = calloc(wcap, sizeof *Warg); Wrow = calloc((size_t)wcap * 4, sizeof *Wrow); Wsp = calloc(wcap, sizeof *Wsp);
  Wnext = calloc(wcap, sizeof *Wnext); Wprev = calloc(wcap, sizeof *Wprev);
  Ws = calloc(wcap, 1); Wa = calloc(wcap, 1); Wmark = calloc(wcap, 1);
  bind = calloc(CAP_META, sizeof *bind); trail = calloc(CAP_META, sizeof *trail);
  Msort = calloc(CAP_META, sizeof *Msort); msort_prev = calloc(CAP_META, sizeof *msort_prev); msort_who = calloc(CAP_META, sizeof *msort_who);
  hmask--; vgen = 0; ug = 1; nn = 1; na = 0; ncon = 0; nsort = 1; nr = 0; ncode = 0; nw = 1; nmeta = 0; ntrail = 0; nne = 0;
  cepoch = 1;
  tscope = false; bscope = false; lok = false; slot_mode = false; wt_dirty = false; has_widecon = false; flat4_board = false; ncache_sort = 0xFFFFu;
  next_name = 0; nsteps = 0; sealed = false; has_take = false; cn = 0; nbv = 0; Wlive = 0; cur_k = NULL;
  space_sort_id = 0; handle_con_id = -1; q_quote_con = q_act_con = q_lam_con = q_app_con = -1; rho_quote_con = rho_drop_con = -1; rho_allow_drop = false;
  memset(space_terms, 0, sizeof space_terms); memset(last_extra_occ, 0, sizeof last_extra_occ);
  memset(protect, 0, sizeof protect); memset(ncache, 0, sizeof ncache); memset(ugen, 0, sizeof ugen); memset(sorts, 0, sizeof sorts); memset(ecvar, 0, sizeof ecvar); memset(FF, 0, sizeof FF);
  if (!(N && A && H && vis && Nhslot && vval && C && CD && R && code && Wt && Wtag && Warg && Wrow && Wsp && Wnext && Wprev && Ws && Wa && Wmark && bind && trail && Msort && msort_prev && msort_who)) return false;
  for (int h = 0; h < TC_VARS; h++) qmeta[h] = mk(K_META, (CAP_META - TC_VARS) + (uint32_t)h, TC_ANY, 0, 0, 0, NULL);
  return true;
}

static inline uint64_t hash(uint8_t k, uint32_t head, uint16_t s, uint64_t id, int ar, const Term *a) {
  uint64_t h = ((uint64_t)head << 24 | (uint64_t)s << 8 | k) * 0x9E3779B97F4A7C15u ^ id * 0xBF58476D1CE4E5B9u;
  for (int i = 0; i < ar; i++) h = (h ^ a[i]) * 0xD6E8FEB86659FD93u;
  return h ^ (h >> 32);
}

static __attribute__((noinline)) bool grow(uint32_t args) { /* double the node arena; rehash oldest first when the table fills */
  uint32_t nc = nn >= ncap ? 2 * ncap : ncap, ac = acap;
  while (na + args > ac) ac *= 2;
  if (nc > (1u << 28) || ac > (1u << 30)) return false;
  if (ac > acap) {
    Term *a2 = realloc(A, ac * sizeof *A); if (!a2) return false; A = a2;
    acap = ac;
  }
  if (nc <= ncap) return true;
  Node *n2 = realloc(N, nc * sizeof *N); if (!n2) return false; N = n2;
  uint64_t *w2 = realloc(vval, nc * sizeof *vval); if (!w2) return false; vval = w2;
  if (Nid) {
    uint64_t *id2 = realloc(Nid, nc * sizeof *Nid); if (!id2) return false; Nid = id2;
    uint64_t *mx2 = realloc(Nmax, nc * sizeof *Nmax); if (!mx2) return false; Nmax = mx2;
  }
  uint32_t *v2 = realloc(vis, nc * sizeof *vis); if (!v2) return false; vis = v2;
  uint32_t *hs2 = realloc(Nhslot, nc * sizeof *Nhslot); if (!hs2) return false; Nhslot = hs2;
  if (Nocc) {
    Occ *oc2 = realloc(Nocc, nc * sizeof *Nocc); if (!oc2) return false; Nocc = oc2;
    memset(Nocc + ncap, 0, (nc - ncap) * sizeof *Nocc);
  }
  memset(vis + ncap, 0, (nc - ncap) * sizeof *vis);
  ncap = nc;
  if (4 * (uint64_t)ncap <= (uint64_t)hmask + 1) return true;      /* load at most a quarter */
  uint32_t m = 2 * (hmask + 1); Term *h2 = calloc(m, sizeof *h2);
  if (!h2) return false;
  free(H); H = h2; hmask = m - 1;
  for (Term t = 1; t < nn; t++) if (Nhslot[t] != UINT32_MAX) {
    Node *x = &N[t];
    uint64_t id = x->kind == K_VAR ? x->bm : x->kind == K_NAME ? Nid[t] : 0;
    uint32_t i = (uint32_t)hash(x->kind, x->head, x->sort, id, x->arity, &A[x->args]) & hmask;
    while (H[i]) i = (i + 1) & hmask;
    H[i] = t; Nhslot[t] = i;
  }
  return true;
}

static Term mk(uint8_t k, uint32_t head, uint16_t s, uint8_t bound, uint64_t id, int ar, const Term *a) {
  uint32_t i = 0;
  if (!bscope) {
    i = (uint32_t)hash(k, head, s, id, ar, a) & hmask;
    for (Term t; (t = H[i]); i = (i + 1) & hmask) {
      Node *x = &N[t];
      if (x->head != head || x->kind != k || x->arity != ar || x->sort != s || x->bound != bound) continue;
      if (k == K_VAR ? x->bm != id : k == K_NAME && Nid[t] != id) continue;
      const Term *b = &A[x->args]; int j = 0;
      while (j < ar && b[j] == a[j]) j++;
      if (j < ar) continue;
      if (x->vm && x->cep != cepoch && k == K_APP) {         /* an older term met again: refresh its scope verdict */
        bool scoped = true;
        for (j = 0; j < ar; j++) scoped &= !N[a[j]].vm || N[a[j]].cep == cepoch;
        if (scoped) x->cep = cepoch;
      }
      return t;
    }
  }
  if (nn >= ncap || na + ar > acap) {                     /* grow, then intern again: a may point into A */
    Term c[TC_ARGS];
    if (ar > TC_ARGS) return 0;
    for (int j = 0; j < ar; j++) c[j] = a[j];
    return grow((uint32_t)ar) ? mk(k, head, s, bound, id, ar, ar ? c : NULL) : 0;
  }
  Term t = nn++;
  uint8_t fl = k == K_META ? F_META : k == K_BV ? F_BV : k == K_NAME ? F_NAME : 0;
  uint64_t bm = k == K_BV ? 1ull << head : k == K_VAR ? id : 0;
  uint64_t vm = k == K_VAR ? 1ull << head : 0;
  uint32_t a0 = na; na += (uint32_t)ar;
  bool scoped = true;                                     /* well-scoped in the current context, if its children are */
  for (int j = 0; j < ar; j++) {
    Term cj = a[j];
    A[a0 + (uint32_t)j] = cj;
    const Node *y = &N[cj];
    bm |= y->bm; vm |= y->vm; fl |= y->flags;
    scoped &= !y->vm || y->cep == cepoch;
  }
  N[t] = (Node){ k, bound, fl, (uint8_t)s, (uint8_t)ar, 0, k == K_APP && scoped ? cepoch : 0, head, a0, bm, vm };
  if (bscope) { Nhslot[t] = UINT32_MAX; return t; }
  Nhslot[t] = i;
  if (__builtin_expect((fl & F_NAME) != 0, 0)) {
    Nid[t] = k == K_NAME ? id : 0;
    uint64_t mx = k == K_NAME ? ((id >> 62) == 1 ? 0 : (id == UINT64_MAX ? id : id + 1)) : 0;
    for (int j = 0; j < ar; j++) if ((N[a[j]].flags & F_NAME) && Nmax[a[j]] > mx) mx = Nmax[a[j]];
    Nmax[t] = mx;
  }
  return H[i] = t;
}

static const Term *argv(Term t) { return &A[N[t].args]; }
static bool is_bvar(Term t) { return (N[t].kind == K_VAR && N[t].bound) || N[t].kind == K_BV; }
uint16_t tc_sort_of(Term t) { return t < nn ? N[t].sort : 0; }
uint64_t tc_name_id(Term t) { return t < nn && N[t].kind == K_NAME ? Nid[t] : 0; }
uint64_t tc_steps(void) { return nsteps; }
void tc_node(Term t, uint8_t *k, uint32_t *head, int *ar, const Term **a) {
  if (t >= nn) t = 0;
  *k = N[t].kind; *head = N[t].head; *ar = N[t].arity; *a = argv(t);
}
static __attribute__((noinline)) Term tc_name_slow(uint16_t s, uint64_t id) {
  if (s >= (uint16_t)nsort) return 0;
  if (!Nid) { Nid = calloc(ncap, sizeof *Nid); Nmax = calloc(ncap, sizeof *Nmax); if (!Nid || !Nmax) return 0; }
  Term c = id < 4096 ? ncache[id] : 0;
  if (c && c < nn && N[c].kind == K_NAME && Nid[c] == id && N[c].sort == s) {
    if (!tscope && ncache_sort == s && id < next_name) N[c].flags |= F_PLAIN;
    return c;
  }
  Term t = mk(K_NAME, 0, s, 0, id, 0, NULL);
  if (id < 4096 && t && !tscope) {
    if (ncache_sort == 0xFFFFu) ncache_sort = s;
    if (ncache_sort == s) { ncache[id] = t; if (id < next_name) N[t].flags |= F_PLAIN; }
  }
  return t;
}
Term tc_name(uint16_t s, uint64_t id) {
  if (__builtin_expect(!tscope && s == ncache_sort && id < 4096 && ncache[id] != 0, 1)) return ncache[id];
  return tc_name_slow(s, id);
}
Term tc_bv(uint16_t s, unsigned i) {
  if (s >= (uint16_t)nsort || (sorts[s] & SORT_STRICT)) return 0;
  int bit = -1;
  for (int j = 0; j < nbv; j++) if (bv_sort[j] == s && bv_idx[j] == i) { bit = j; break; }
  if (bit < 0) {
    if (nbv >= 64) return 0;
    bit = nbv++; bv_sort[bit] = s; bv_idx[bit] = i;
  }
  return mk(K_BV, (uint32_t)bit, s, 1, 0, 0, NULL);
}
Term tc_meta(void) { tscope = bscope = false; return nmeta < CAP_META - TC_VARS ? mk(K_META, nmeta++, TC_ANY, 0, 0, 0, NULL) : 0; }
uint64_t tc_fresh_name(void) { return next_name >= UINT64_MAX - 1 ? UINT64_MAX : next_name++; }
uint64_t tc_next_name(void) { return next_name; }
void tc_protect(uint8_t s) { protect[s] = true; if (!s) flat4_board = false; }
static void prep_flat(RuleK *k);
void tc_seal(void) {
  sealed = true;
  for (int i = 0; i < nr; i++) if (!R[i].fprepped) prep_flat(&R[i]);
  flat4_board = slot_mode && !has_take && !protect[0] && ncon == 1 && C[0].arity == 4 &&
                ncache_sort < (uint16_t)nsort &&
                C[0].asort[0] == ncache_sort && C[0].asort[1] == ncache_sort &&
                C[0].asort[2] == ncache_sort && C[0].asort[3] == ncache_sort;
}

int tc_sort(uint8_t flags) { if (nsort >= 256) return -1; sorts[nsort] = flags; return nsort++; }

static bool binders_ok(int n, const Binder *b, uint64_t *bits) {   /* deps: earlier bound positions */
  if (n < 0 || (n > 0 && !b)) return false;
  uint64_t bound = 0, next = 1;
  for (int i = 0; i < n; i++) {
    if (b[i].sort >= nsort || (b[i].deps & ~bound)) return false;
    if (b[i].bound) {
      if ((sorts[b[i].sort] & SORT_STRICT) || !next) return false;
      bound |= 1ull << i; if (bits) bits[i] = next; next <<= 1;
    } else if (bits) {
      bits[i] = 0;
      for (int j = 0; j < i; j++) if (b[i].deps >> j & 1) bits[i] |= bits[j];
    }
  }
  return true;
}

int tc_con(uint16_t s, uint64_t retdeps, int ar, const Binder *a) {
  uint64_t bound = 0;
  if (ncon >= CAP_CON || ar < 0 || ar > TC_ARGS || s >= nsort || (sorts[s] & SORT_PURE) || !binders_ok(ar, a, NULL)) return -1;
  for (int i = 0; i < ar; i++) if (a[i].bound) bound |= 1ull << i;
  if (retdeps & ~bound) return -1;
  uint64_t h0 = ((uint64_t)(uint32_t)ncon << 24 | (uint64_t)s << 8 | K_APP) * 0x9E3779B97F4A7C15u;
  C[ncon] = (Con){ .sort = (uint8_t)s, .arity = (uint8_t)ar, .abound = (uint32_t)bound, .retdeps = retdeps, .h0 = h0 };
  if (ar > 4) has_widecon = true;
  for (int i = 0; i < ar; i++) C[ncon].asort[i] = (uint8_t)a[i].sort;
  if (bound) for (int i = 0; i < ar; i++) CD[ncon].adeps[i] = (uint32_t)a[i].deps;
  return ncon++;
}

bool tc_ctx(int n, const Binder *v) {                    /* all or nothing */
  uint64_t bits[TC_VARS]; Term vars[TC_VARS];
  tscope = bscope = false; lok = false;
  if (n < 0 || n > TC_VARS || !binders_ok(n, v, bits)) return false;
  bool bump = false;
  for (int i = 0; i < n; i++) {
    if (!(vars[i] = mk(K_VAR, (uint32_t)i, v[i].sort, v[i].bound, bits[i], 0, NULL))) return false;
    bump |= ecvar[i] && ecvar[i] != vars[i];
  }
  if (bump) {
    if (!++cepoch) { for (uint32_t i = 0; i < nn; i++) N[i].cep = 0; cepoch = 1; }
    memset(ecvar, 0, sizeof ecvar);
  }
  for (int i = 0; i < n; i++) {
    csort[i] = v[i].sort; cbound[i] = v[i].bound; cdeps[i] = v[i].deps; cbm[i] = bits[i];
    cvar[i] = ecvar[i] = vars[i]; N[vars[i]].cep = cepoch;
  }
  cn = n;
  return true;
}
bool tc_ctx_push(Binder v) {                             /* one more variable; earlier terms stay well-scoped */
  uint64_t bound = 0, bits = 0; int nbd = 0;
  for (int i = 0; i < cn; i++) if (cbound[i]) { bound |= 1ull << i; nbd++; }
  if (cn >= TC_VARS || v.sort >= nsort || (v.deps & ~bound)) return false;
  if (v.bound) { if ((sorts[v.sort] & SORT_STRICT) || nbd >= 64) return false; bits = 1ull << nbd; }
  else for (int j = 0; j < cn; j++) if (v.deps >> j & 1) bits |= cbm[j];
  Term x = mk(K_VAR, (uint32_t)cn, v.sort, v.bound, bits, 0, NULL);
  if (!x) return false;
  if (ecvar[cn] && ecvar[cn] != x) {
    if (!++cepoch) { for (uint32_t i = 0; i < nn; i++) N[i].cep = 0; cepoch = 1; }
    memset(ecvar, 0, sizeof ecvar);
    for (int i = 0; i < cn; i++) { ecvar[i] = cvar[i]; N[cvar[i]].cep = cepoch; }
  }
  csort[cn] = v.sort; cbound[cn] = v.bound; cdeps[cn] = v.deps; cbm[cn] = bits;
  cvar[cn] = ecvar[cn] = x; cn++; N[x].cep = cepoch;
  return true;
}
Term tc_v(int i) { return i >= 0 && i < cn ? cvar[i] : 0; }

static __attribute__((noinline)) Term app_intern(int con, const Term *a) {
  Con *c = &C[con];
  int ar = c->arity;
  if (!ar) {
    Term t = c->t0;
    if (t && t < nn && N[t].kind == K_APP && N[t].head == (uint32_t)con && !N[t].arity) return t;
    return c->t0 = mk(K_APP, (uint32_t)con, c->sort, 0, 0, 0, NULL);
  }
  if (!a) return 0;
  uint16_t cs = c->sort;
  uint64_t h = c->h0;
  for (int k = 0; k < ar; k++) h = (h ^ a[k]) * 0xD6E8FEB86659FD93u;
  uint32_t slot = (uint32_t)(h ^ (h >> 32)) & hmask;
  Term hit = 0;
  for (Term t; (t = H[slot]); slot = (slot + 1) & hmask) {
    Node *x = &N[t];
    if (x->head != (uint32_t)con || x->kind != K_APP) continue;
    const Term *b = &A[x->args]; int j = 0;
    while (j < ar && b[j] == a[j]) j++;
    if (j < ar) continue;
    if (__builtin_expect((x->flags & F_META) != 0, 0)) { hit = t; break; }
    if (__builtin_expect(x->vm && x->cep != cepoch, 0)) {
      bool sc = true;
      for (j = 0; j < ar; j++) sc &= !N[a[j]].vm || N[a[j]].cep == cepoch;
      if (sc) x->cep = cepoch;
    }
    return t;
  }
  uint32_t ab = c->abound;
  uint64_t bm = 0, vm = 0;
  uint8_t fl = 0;
  bool scoped = true, has_m = false;
  for (int i = 0; i < ar; i++) {
    Term x = a[i];
    if (!x || x >= nn) return 0;
    const Node *nx = &N[x];
    if (__builtin_expect(nx->sort != c->asort[i], 0)) {
      if (nx->kind == K_META && !(ab >> i & 1)) { has_m = true; goto step; }
      return 0;
    }
    if ((ab >> i & 1) && !((nx->kind == K_VAR && nx->bound) || nx->kind == K_BV)) return 0;
  step:
    bm |= nx->bm; vm |= nx->vm; fl |= nx->flags;
    scoped &= !nx->vm || nx->cep == cepoch;
  }
  if (__builtin_expect(has_m, 0)) {
    for (int i = 0; i < ar; i++) if (N[a[i]].kind == K_META) {
      uint32_t mh = N[a[i]].head;
      if (mh >= CAP_META - TC_VARS) continue;
      uint16_t s = c->asort[i];
      if (Msort[mh] != TC_ANY && Msort[mh] != s) return 0;
      Term x = a[i]; while (N[x].kind == K_META && bind[N[x].head]) x = bind[N[x].head];
      uint16_t ws = N[x].kind == K_META ? Msort[N[x].head] : N[x].sort;
      if (ws != TC_ANY && ws != s) return 0;
      Msort[mh] = s;
      if (N[x].kind == K_META && N[x].head < CAP_META - TC_VARS) Msort[N[x].head] = s;
    }
  }
  if (hit) {
    if (vm && scoped && N[hit].cep != cepoch) N[hit].cep = cepoch;
    return hit;
  }
  if (__builtin_expect(nn >= ncap || na + ar > acap, 0))
    return mk(K_APP, (uint32_t)con, cs, 0, 0, ar, a);
  Term t = nn++;
  uint32_t a0 = na; na += (uint32_t)ar;
  for (int j = 0; j < ar; j++) A[a0 + (uint32_t)j] = a[j];
  N[t] = (Node){ K_APP, 0, fl, (uint8_t)cs, (uint8_t)ar, 0, scoped ? cepoch : 0, (uint32_t)con, a0, bm, vm };
  Nhslot[t] = slot;
  if (__builtin_expect((fl & F_NAME) != 0, 0)) {
    Nid[t] = 0;
    uint64_t mx = 0;
    for (int j = 0; j < ar; j++) if ((N[a[j]].flags & F_NAME) && Nmax[a[j]] > mx) mx = Nmax[a[j]];
    Nmax[t] = mx;
  }
  return H[slot] = t;
}

Term tc_app(int con, const Term *a) {
  if ((unsigned)con >= (unsigned)ncon) return 0;
  if (!bscope) return app_intern(con, a);
  Con *c = &C[con];
  int ar = c->arity;
  if (ar && !a) return 0;
  uint32_t ab = c->abound;
  uint64_t bm = 0, vm = 0;
  uint8_t fl = 0;
  bool scoped = true;
  for (int i = 0; i < ar; i++) {
    Term x = a[i];
    if (!x || x >= nn) return 0;
    const Node *nx = &N[x];
    if (__builtin_expect(nx->sort != c->asort[i], 0)) return 0;
    if ((ab >> i & 1) && !((nx->kind == K_VAR && nx->bound) || nx->kind == K_BV)) return 0;
    bm |= nx->bm; vm |= nx->vm; fl |= nx->flags;
    scoped &= !nx->vm || nx->cep == cepoch;
  }
  if (__builtin_expect(nn >= ncap || na + ar > acap, 0))
    return mk(K_APP, (uint32_t)con, c->sort, 0, 0, ar, a);
  Term t = nn++;
  uint32_t a0 = na; na += (uint32_t)ar;
  for (int j = 0; j < ar; j++) A[a0 + (uint32_t)j] = a[j];
  N[t] = (Node){ K_APP, 0, fl, c->sort, (uint8_t)ar, 0, scoped ? cepoch : 0, (uint32_t)con, a0, bm, vm };
  Nhslot[t] = UINT32_MAX;
  return t;
}

/* ---- unknowns: bindings with a trail ---- */
static uint32_t next_vgen(void) { if (++vgen) return vgen; memset(vis, 0, nn * sizeof *vis); return vgen = 1; }
static Term walk(Term t) { while (N[t].kind == K_META && bind[N[t].head]) t = bind[N[t].head]; return t; }
static Term norm_rec(Term t, uint32_t g, int d) {
  if (d > 4096) return 0;
  t = walk(t);
  if (!has_meta(t) || N[t].kind != K_APP) return t;
  if (vis[t] == g) return (Term)vval[t];
  Term b[TC_ARGS];
  for (int i = 0; i < N[t].arity; i++) if (!(b[i] = norm_rec(argv(t)[i], g, d + 1))) return 0;
  Term r = tc_app((int)N[t].head, b);
  vis[t] = g; vval[t] = r; return r;
}
static Term norm(Term t) { return norm_rec(t, next_vgen(), 0); }
Term tc_deref(Term t) { return t && t < nn ? norm(t) : 0; }
static bool occ_rec(Term m, Term t, uint32_t g, int d) {
  if (d > 4096) return true;
  t = walk(t);
  if (t == m) return true;
  if (!has_meta(t) || vis[t] == g) return false;
  vis[t] = g;
  for (int i = 0; i < N[t].arity; i++) if (occ_rec(m, argv(t)[i], g, d + 1)) return true;
  return false;
}
static bool occurs(Term m, Term t) { return occ_rec(m, t, next_vgen(), 0); }
static bool ucache(uint64_t key, bool set) {
  uint32_t i = (uint32_t)((key * 0x9E3779B97F4A7C15ull) >> 54);
  if (!set) return ugen[i] == ug && upair[i] == key;
  ugen[i] = ug; upair[i] = key; return true;
}
static bool unify_rec(Term u, Term v, int d) {
  if (d > 4096) return false;
  u = walk(u); v = walk(v);
  if (u == v) return true;
  if (N[v].kind == K_META && (N[u].kind != K_META || N[u].head < N[v].head)) { Term s = u; u = v; v = s; }
  if (N[u].kind == K_META) {
    if (occurs(u, v) || ntrail >= CAP_META) return false;
    uint16_t su = Msort[N[u].head], sv = N[v].kind == K_META ? Msort[N[v].head] : N[v].sort;
    if (su != TC_ANY && sv != TC_ANY && su != sv) return false;
    uint32_t hv = N[v].kind == K_META ? N[v].head : 0;
    msort_who[ntrail] = hv; msort_prev[ntrail] = Msort[hv];
    if (N[v].kind == K_META && Msort[hv] == TC_ANY && su != TC_ANY && hv < CAP_META - TC_VARS) Msort[hv] = su;
    bind[N[u].head] = v; trail[ntrail++] = N[u].head; tscope = bscope = false; return true;   /* K may now hold transient terms */
  }
  if (N[u].kind != K_APP || N[v].kind != K_APP || N[u].head != N[v].head) return false;
  uint64_t key = ((uint64_t)u << 32) | v;
  if (ucache(key, false)) return true;
  for (int i = 0; i < N[u].arity; i++) if (!unify_rec(argv(u)[i], argv(v)[i], d + 1)) return false;
  return ucache(key, true);
}
static bool unify(Term u, Term v) { return unify_rec(u, v, 0); }
static void undo(uint32_t mark) {
  if (ntrail > mark) ug++;
  if (!ug) { memset(ugen, 0, sizeof ugen); ug = 1; }
  while (ntrail > mark) { --ntrail; Msort[msort_who[ntrail]] = msort_prev[ntrail]; bind[trail[ntrail]] = 0; }
}
static bool diseqs_ok(void) {
  for (int i = 0; i < nne; i++) { Term a = norm(NE[i][0]), b = norm(NE[i][1]); if (!a || !b || a == b) return false; }
  return true;
}
bool tc_tell(Term u, Term v) {
  tscope = bscope = false;
  if (!u || !v || u >= nn || v >= nn || N[u].vm || N[v].vm || !name_ok(u) || !name_ok(v)) return false;
  uint32_t m = ntrail;
  if (u && v && u < nn && v < nn && unify(u, v) && diseqs_ok()) return true;
  undo(m); return false;
}
bool tc_tell_neq(Term u, Term v) {
  tscope = bscope = false;
  if (!u || !v || u >= nn || v >= nn || N[u].vm || N[v].vm || !name_ok(u) || !name_ok(v) || nne >= 65536) return false;
  Term na = norm(u), nb = norm(v);
  if (!na || !nb || na == nb) return false;
  if (!has_meta(na) && !has_meta(nb)) return true;
  NE[nne][0] = u; NE[nne][1] = v; nne++;
  if (diseqs_ok()) return true;
  nne--; return false;
}

/* ---- rules: premises compiled to preorder bytecode ---- */
enum { OP_APP = 1u << 28, OP_HOLE = 2u << 28, OP_SAME = 3u << 28, OP_FLAT = 4u << 28, OP_CON = 5u << 28, OP_MASK = 15u << 28 };
static bool emit(Term p, uint32_t lim, const RuleK *k, uint64_t *imp) {
  if (ncode >= lim) return false;
  if (N[p].kind == K_VAR) { code[ncode++] = OP_HOLE | N[p].head; return true; }
  if (!bscope && !N[p].vm) return p < (1u << 28) && (code[ncode++] = OP_SAME | p, true);
  if (N[p].kind == K_APP && N[p].arity == 0) { code[ncode++] = OP_CON | N[p].head; return true; }
  if (N[p].kind != K_APP) return p < (1u << 28) && (code[ncode++] = OP_SAME | p, true);
  bool flat = true;                                       /* FLAT: an application of leaves, matched in place */
  const Con *c = &C[N[p].head]; const Term *pa = argv(p); int ar = N[p].arity;
  for (int i = 0; i < ar; i++) {
    Term a = pa[i];
    if (N[a].kind == K_VAR) {
      int h = (int)N[a].head;
      if ((HOLE(k, h).sort == TC_ANY || c->asort[i] == HOLE(k, h).sort) && (!HOLE(k, h).bound || (c->abound >> i & 1))) *imp |= 1ull << h;
    } else flat &= (!bscope && !N[a].vm) || (N[a].kind == K_APP && N[a].arity == 0) || N[a].kind != K_APP;
  }
  code[ncode++] = (flat ? OP_FLAT : OP_APP) | ((uint32_t)ar << 20) | N[p].head;
  for (int i = 0; i < ar; i++) if (!emit(pa[i], lim, k, imp)) return false;
  return true;
}
static inline bool leaf(uint32_t op, Term x, Term *S, bool exact) {
  if ((op & OP_MASK) == OP_HOLE) {
    Term *s = &S[op & 0xFFFFFu];
    if (*s == x) return true;
    if (!*s) { *s = x; return true; }
    return !exact && has_meta(*s) && unify(*s, x);
  }
  if ((op & OP_MASK) == OP_CON) return N[x].kind == K_APP && N[x].head == (op & 0xFFFFFu);
  return x == (op & 0xFFFFFFFu);
}
static Term run_st[512];
static bool run_stack(uint32_t pc, int sp, Term *S, bool exact) {   /* run_st[0..sp) has no unknowns */
  while (sp) {
    Term x = run_st[--sp]; uint32_t op = code[pc++];
    switch (op & OP_MASK) {
      case OP_SAME: case OP_HOLE: case OP_CON: if (!leaf(op, x, S, exact)) return false; break;
      case OP_FLAT: {
        if (N[x].kind != K_APP || N[x].head != (op & 0xFFFFFu)) return false;
        const Term *a = argv(x); int ar = (int)((op >> 20) & 0xFFu);
        for (int i = 0; i < ar; i++) if (!leaf(code[pc++], a[i], S, exact)) return false;
        break;
      }
      default: {
        int ar = (int)((op >> 20) & 0xFFu);
        if (N[x].kind != K_APP || N[x].head != (op & 0xFFFFFu) || sp + ar > 512) return false;
        const Term *a = argv(x);
        for (int i = ar - 1; i >= 0; i--) run_st[sp++] = a[i];
      }
    }
  }
  return true;
}
/* Instantiate a template. Closed instantiation keeps formation (holes hold terms of their
   sorts), so it builds directly; open instantiation (unbound holes become unknowns) rechecks. */
static Term inst_rec(Term p, Term *S, bool open, uint32_t g, int d) {
  if (!p || d > 4096) return 0;
  if (!N[p].vm) return p;
  if (N[p].kind == K_VAR) { Term *s = &S[N[p].head]; if (!*s && open) *s = tc_meta(); return *s; }
  if (vis[p] == g) return (Term)vval[p];
  Term b[TC_ARGS];
  for (int i = 0; i < N[p].arity; i++) if (!(b[i] = inst_rec(argv(p)[i], S, open, g, d + 1))) return 0;
  Term r = open ? tc_app((int)N[p].head, b) : mk(K_APP, N[p].head, N[p].sort, 0, 0, N[p].arity, b);
  vis[p] = g; vval[p] = r; return r;
}
static Term inst(Term p, Term *S, bool open) { return inst_rec(p, S, open, next_vgen(), 0); }
static bool umatch_rec(Term p, Term t, Term *S, int d) {  /* two-way, for terms with unknowns */
  if (d > 4096) return false;
  t = walk(t);
  if (N[p].kind == K_VAR) { Term *s = &S[N[p].head]; if (!*s) { *s = t; return true; } return unify(*s, t); }
  if (!N[p].vm || N[t].kind == K_META) { Term q = inst(p, S, true); return q && unify(q, t); }
  if (N[t].kind != K_APP || N[t].head != N[p].head) return false;
  uint64_t key = (1ull << 63) | ((uint64_t)p << 32) | t;
  if (ucache(key, false)) return true;
  for (int i = 0; i < N[p].arity; i++) if (!umatch_rec(argv(p)[i], argv(t)[i], S, d + 1)) return false;
  return ucache(key, true);
}
static bool umatch(Term p, Term t, Term *S) {
  if (!++ug) { memset(ugen, 0, sizeof ugen); ug = 1; }
  return umatch_rec(p, t, S, 0);
}

static bool ctx_rec(Term t, int d) {                   /* every hole below t is the current context's variable */
  if (!t || t >= nn || d > 4096) return false;
  if (!N[t].vm || N[t].cep == cepoch) return true;
  if (N[t].kind == K_VAR) return N[t].head < (uint32_t)cn && t == cvar[N[t].head];
  for (int i = 0; i < N[t].arity; i++) if (!ctx_rec(argv(t)[i], d + 1)) return false;
  N[t].cep = cepoch; return true;
}
static inline bool ctx_ok(Term t) { return t && t < nn && (!N[t].vm || N[t].cep == cepoch || ctx_rec(t, 0)); }

enum { HEAD_AT_SPACE = 0xFFFFFFFEu, HEAD_AT_BIRTH = 0xFFFFFFFFu };
static inline bool is_at_node(Term t) {
  return t && t < nn && N[t].kind == K_APP && N[t].arity == 2 && N[t].head >= HEAD_AT_SPACE;
}
static inline void unpack_pat(Term pt, Term *t_out, Term *sp_out, uint8_t *mark_out) {
  if (is_at_node(pt)) {
    *sp_out = argv(pt)[0];
    *t_out  = argv(pt)[1];
    *mark_out = N[pt].head == HEAD_AT_BIRTH ? 1 : 0;
  } else {
    *sp_out = 0;
    *t_out  = pt;
    *mark_out = 0;
  }
}
Term tc_at_space(Term space, Term t) {
  if (!space || space >= nn || !t || t >= nn || is_at_node(space) || is_at_node(t)) return 0;
  return mk(K_APP, HEAD_AT_SPACE, N[t].sort, 0, 0, 2, (Term[2]){ space, t });
}
Term tc_at_birth(Term space, Term t) {
  if (!space || space >= nn || !t || t >= nn || is_at_node(space) || is_at_node(t)) return 0;
  return mk(K_APP, HEAD_AT_BIRTH, N[t].sort, 0, 0, 2, (Term[2]){ space, t });
}
static bool pats_ok(const Pat *p, int n, uint64_t ctx) {
  for (int i = 0; i < n; i++)
    if (!p[i].t || p[i].t >= nn || !ctx_ok(p[i].t) || (N[p[i].t].vm & ~ctx) || has_bv(p[i].t) || !name_ok(p[i].t)) return false;
  return true;
}
static uint64_t mask(int n) { return n >= 64 ? ~0ull : (1ull << n) - 1; }

static bool linear_pat(Term p, uint64_t *seen, int d) {
  if (d > 4096) return false;
  if (!N[p].vm) return true;
  if (*seen & N[p].vm) return false;
  if (N[p].kind == K_VAR) { *seen |= N[p].vm; return true; }
  for (int i = 0; i < N[p].arity; i++) if (!linear_pat(argv(p)[i], seen, d + 1)) return false;
  return true;
}

/* ---- transient terms: made since tc_transient(), released when the next rule is installed ----
   Hash-consing is stack-disciplined and topologically ordered (children < parent): a kept prefix
   stays in place, and any kept nodes after the first dead node slide down in a single pass. */
void tc_transient(void) { tscope = true; bscope = false; tmark = nn; tamark = na; }
void tc_birth(void) { tscope = true; bscope = true; tmark = nn; tamark = na; }
static bool mark_rec(Term t, uint32_t g, int d) {
  if (t < tmark || (t < nn && vis[t] == g)) return true;
  if (t >= nn || d > 4096) return false;
  for (int i = 0; i < N[t].arity; i++) if (!mark_rec(argv(t)[i], g, d + 1)) return false;
  vis[t] = g; return true;
}
static void release(Term *const *ts, int n) {   /* ts: the installed patterns, rewritten in place */
  if (!tscope) return;
  bool bs = bscope;
  tscope = bscope = false;
  uint32_t g = n ? next_vgen() : 0;
  for (int i = 0; i < n; i++) if (!mark_rec(*ts[i], g, 0)) return;
  if (n) while (tmark < nn && vis[tmark] == g) { tamark += N[tmark].arity; tmark++; }
  if (!bs) for (Term t = tmark; t < nn; t++) {
    if (Nhslot[t] != UINT32_MAX) H[Nhslot[t]] = 0;
    if (N[t].kind == K_NAME && Nid && Nid[t] < 4096 && ncache[Nid[t]] >= tmark) ncache[Nid[t]] = 0;
  }
  uint32_t end = nn; nn = tmark; na = tamark;
  if (!++ug) { memset(ugen, 0, sizeof ugen); ug = 1; }     /* the unify cache is keyed by term ids */
  for (Term t = tmark; n && t < end; t++) if (vis[t] == g) {   /* slide kept nodes down, children first */
    Node x = N[t]; Term nt = nn++;
    uint32_t a0 = na; na += x.arity;
    for (int j = 0; j < x.arity; j++) { Term c = A[x.args + (uint32_t)j]; A[a0 + (uint32_t)j] = c < tmark ? c : (Term)vval[c]; }
    uint64_t id = x.kind == K_VAR ? x.bm : (x.flags & F_NAME) && x.kind == K_NAME ? Nid[t] : 0;
    x.args = a0; N[nt] = x; vval[t] = nt;
    if (bs) {
      Nhslot[nt] = UINT32_MAX;
    } else {
      uint32_t i = (uint32_t)hash(x.kind, x.head, x.sort, id, x.arity, &A[a0]) & hmask;
      while (H[i]) i = (i + 1) & hmask;
      H[i] = nt; Nhslot[nt] = i;
    }
    if (__builtin_expect((x.flags & F_NAME) != 0, 0)) {
      Nid[nt] = id;
      uint64_t mx = x.kind == K_NAME ? ((id >> 62) == 1 ? 0 : (id == UINT64_MAX ? id : id + 1)) : 0;
      for (int j = 0; j < x.arity; j++) { Term cj = A[a0 + (uint32_t)j]; if ((N[cj].flags & F_NAME) && Nmax[cj] > mx) mx = Nmax[cj]; }
      Nmax[nt] = mx;
    }
  }
  for (int i = 0; i < n; i++) if (*ts[i] >= tmark) *ts[i] = (Term)vval[*ts[i]];
  for (int i = 0; i < 256; i++) if (space_terms[i] >= tmark) space_terms[i] = vis[space_terms[i]] == g ? (Term)vval[space_terms[i]] : 0;
  for (int i = 0; i < TC_VARS; i++) if (ecvar[i] >= tmark) ecvar[i] = 0;
  for (int i = 0; i < cn; i++) if (cvar[i] >= tmark) { cn = i; break; }   /* variables pushed since the mark go too */
}

static int add_rule(const Rule *r, int n) {
  RuleK *k = &R[nr];
  uint64_t ctx = mask(n);
  Pat tells[24] = {0}; int nt = 0;
  if (nhk + (uint32_t)n > hkcap) {
    uint32_t m = hkcap ? hkcap : 4096; while (m < nhk + (uint32_t)n) m *= 2;
    Hole *g = realloc(HK, m * sizeof *g); if (!g) return -1;
    HK = g; hkcap = m;
  }
  if (nr >= CAP_RULE || n > cn || r->ntake > 4 || r->nkeep > TC_HYPS || r->nabsent > 4 || r->ncount > 4 || r->ntell > 4 || r->nneq > 4 || r->nmake_extra > 4) return -1;
  for (int i = 0; i < r->ntell; i++) { tells[nt++] = (Pat){ r->tell[i][0], 0 }; tells[nt++] = (Pat){ r->tell[i][1], 0 }; }
  for (int i = 0; i < r->nneq; i++) { tells[nt++] = (Pat){ r->neq[i][0], 0 }; tells[nt++] = (Pat){ r->neq[i][1], 0 }; }
  for (int i = 0; i < r->ncount; i++) tells[nt++] = (Pat){ r->count[i].t, r->count[i].space };
  if (!pats_ok(r->take, r->ntake, ctx) || !pats_ok(r->keep, r->nkeep, ctx) || !pats_ok(r->absent, r->nabsent, ctx)
      || !pats_ok(&r->make, 1, ctx) || !pats_ok(r->make_extra, r->nmake_extra, ctx) || !pats_ok(tells, nt, ctx)
      || (r->fresh >= 0 && (r->fresh >= n || cbound[r->fresh]))) return -1;
  for (int i = 0; i < r->nkeep; i++) if (r->fresh >= 0 && (N[r->keep[i].t].vm >> r->fresh & 1)) return -1;
  for (int i = 0; r->fresh >= 0 && i < nt; i++) if (N[tells[i].t].vm >> r->fresh & 1) return -1;
  for (int i = 0; r->fresh >= 0 && i < r->ntake; i++) if (N[r->take[i].t].vm >> r->fresh & 1) return -1;
  for (int i = 0; r->fresh >= 0 && i < r->nabsent; i++) if (N[r->absent[i].t].vm >> r->fresh & 1) return -1;
  bool meta_pat = has_meta(r->make.t), ks_zero = true;
  bool dyn_space = is_at_node(r->make.t) || r->nmake_extra > 0 || r->birth_law != 0;
  for (int i = 0; i < r->nkeep; i++) {
    meta_pat |= has_meta(r->keep[i].t);
    ks_zero &= !r->keep[i].space && !is_at_node(r->keep[i].t);
    dyn_space |= is_at_node(r->keep[i].t);
  }
  for (int i = 0; i < r->ntake; i++) dyn_space |= is_at_node(r->take[i].t);
  for (int i = 0; i < r->nabsent; i++) dyn_space |= is_at_node(r->absent[i].t);
  for (int i = 0; i < r->ncount; i++) dyn_space |= is_at_node(r->count[i].t);
  size_t rsz = (offsetof(Rule, keep) + r->nkeep * sizeof(Pat) + 7) & ~(size_t)7;
  if (nrp + rsz > rpcap) {
    size_t m = rpcap ? 2 * rpcap : 1u << 16; while (m < nrp + rsz) m *= 2;
    uint8_t *g = realloc(RP, m); if (!g) return -1;
    RP = g; rpcap = m;
  }
  bool pure = !meta_pat && !dyn_space && !r->ntake && !r->nabsent && !r->ncount && !r->ntell && !r->nneq && r->fresh < 0;
  *k = (RuleK){ .ro = (uint32_t)nrp, .n = n, .h0 = nhk, .make = r->make.t, .nkeep = r->nkeep, .mspace = r->make.space,
                .fibre = pure ? FIBRE_PURE : 0, .pure = pure, .ks_zero = ks_zero };
  for (int h = 0; h < n; h++) {
    HOLE(k, h) = (Hole){ 0, csort[h], cbound[h] }; if (cbound[h]) k->bounds |= 1ull << h;
    for (int j = 0; cbound[h] && j < n; j++)            /* a bound hole avoids every hole not depending on it */
      if (j != h && !(cbm[j] & cbm[h])) HOLE(k, h).avoid |= 1ull << j;
  }
  if (r->ntake || r->ncount || dyn_space) has_take = true;
  memcpy(RP + nrp, r, rsz < sizeof *r ? rsz : sizeof *r); nrp += rsz;
  nhk += (uint32_t)n;
  return nr++;
}
static void prep_rule(RuleK *k) {
  k->prepped = true;
  const Rule *r = RULE(k);
  uint32_t s = ncode, lim = s + 4096 < CAP_CODE ? s + 4096 : CAP_CODE;
  bool ok = k->pure;
  uint64_t imp = 0;
  for (int i = 0; ok && i < k->nkeep; i++) ok = emit(r->keep[i].t, lim, k, &imp);
  k->kcode = ok ? s : (ncode = s, UINT32_MAX);
  k->implied = ok ? imp : 0;
  uint32_t ms = ncode, mlim = ms + 4096 < CAP_CODE ? ms + 4096 : CAP_CODE;
  uint64_t mimp = k->implied;
  k->mcode = ok && emit(k->make, mlim, k, &mimp) ? ms : (ncode = ms, UINT32_MAX);
  k->mimplied = k->mcode != UINT32_MAX ? mimp : k->implied;
}
static void prep_flat(RuleK *k) {
  if (!k->prepped) prep_rule(k);
  k->fprepped = true;
  const Rule *r = RULE(k);
  if (k->nkeep == 0 && !r->ntake && !r->nabsent && !r->ncount && !r->ntell && !r->nneq && !k->bounds
      && !has_meta(k->make) && N[k->make].kind == K_APP) {
    bool mf = true;
    for (int j = 0; mf && j < N[k->make].arity; j++) {
      Term a = argv(k->make)[j];
      mf = !N[a].vm || N[a].kind == K_VAR;
    }
    k->mflat = mf;
  }
  if (!k->pure) return;
  bool gnd = k->nkeep > 0 && !(k->implied & k->bounds) && !(N[k->make].vm & ~k->implied), lin = gnd;
  uint64_t lseen = 0;
  for (int i = 0; i < k->nkeep; i++) {
    gnd &= !(N[r->keep[i].t].vm & ~k->implied);
    lin &= gnd && linear_pat(r->keep[i].t, &lseen, 0);
  }
  if (gnd) k->fibre |= FIBRE_GROUND;
  if (lin) k->fibre |= FIBRE_LINEAR;
  if (gnd && N[k->make].kind == K_APP) {
    int8_t fi[TC_VARS], fj[TC_VARS]; memset(fi, -1, sizeof fi);
    Flat f = { 0 }, *q = &f;
    bool ok = true;
    for (int i = 0; ok && i < k->nkeep; i++) {
      Term p = r->keep[i].t;
      if (N[p].kind != K_APP || (N[p].vm & ~k->implied)) { ok = false; break; }
      q->ktag[i] = (N[p].head << 9) | ((uint32_t)r->keep[i].space << 1) | 1u;
      for (int j = 0; j < N[p].arity; j++) {
        Term a = argv(p)[j];
        if (!N[a].vm) {
          if (q->nguard >= 32 || q->nconst >= 32) { ok = false; break; }
          q->mc[q->nconst] = a;
          q->guard[q->nguard++] = (Guard){ (uint8_t)i, (uint8_t)j, k->nkeep, (uint8_t)q->nconst++ };
        } else if (N[a].kind == K_VAR) {
          int h = (int)N[a].head;
          if (fi[h] < 0) { fi[h] = (int8_t)i; fj[h] = (int8_t)j; }
          else if (q->nguard < 32) q->guard[q->nguard++] = (Guard){ (uint8_t)i, (uint8_t)j, (uint8_t)fi[h], (uint8_t)fj[h] };
          else { ok = false; break; }
        } else { ok = false; break; }
      }
    }
    Term m = k->make; q->mhead = N[m].head; q->msort = N[m].sort; q->mar = N[m].arity;
    for (int j = 0; ok && j < q->mar; j++) {
      Term a = argv(m)[j];
      if (!N[a].vm && q->nconst < 32) { q->mc[q->nconst] = a; q->mi[j] = k->nkeep; q->mj[j] = (uint8_t)q->nconst++; }
      else if (N[a].kind == K_VAR && fi[N[a].head] >= 0) { q->mi[j] = (uint8_t)fi[N[a].head]; q->mj[j] = (uint8_t)fj[N[a].head]; }
      else ok = false;
    }
    if (ok && nfl >= flcap) {
      uint32_t cap = flcap ? 2 * flcap : 256; Flat *g = realloc(FL, cap * sizeof *g);
      if (g) { FL = g; flcap = cap; } else ok = false;
    }
    if (ok) {
      int rid = (int)(k - R);
      bool ar4 = rid >= 0 && rid < 64 && q->nconst == 0 && k->nkeep == 4 && q->mar == 4;
      for (int i = 0; ar4 && i < 4; i++) if (N[r->keep[i].t].arity != 4) ar4 = false;
      if (ar4) {
        Flat4 *f4 = &FF[rid];
        for (int i = 0; i < 4; i++) f4->ktag[i] = q->ktag[i];
        f4->mtag = (q->mhead << 9) | ((uint32_t)k->mspace << 1) | 1u;
        f4->ok = 1;
        f4->single_tag = (slot_mode && !has_take && ncon == 1 && k->mspace == 0 &&
                          q->ktag[0] == Wtag[0] && q->ktag[1] == Wtag[0] &&
                          q->ktag[2] == Wtag[0] && q->ktag[3] == Wtag[0]);
        for (int i = 0; i < 4; i++) {
          Term p = r->keep[i].t;
          for (int j = 0; j < 4; j++) {
            int h = (int)N[argv(p)[j]].head;
            f4->perm[i * 4 + j] = (uint8_t)(fi[h] * 4 + fj[h]);
          }
        }
        for (int j = 0; j < 4; j++) f4->mperm[j] = (uint32_t)q->mi[j] * 4u + (uint32_t)q->mj[j];
      }
      FL[nfl] = f; k->fl = nfl++; k->flat = true; k->fibre |= FIBRE_FLAT;
    }
  }
}
int tc_rule(const Rule *r) {
  if (sealed || !r || r->ntake > 4 || r->nkeep > TC_HYPS || r->nabsent > 4 || r->ncount > 4 || r->ntell > 4 || r->nneq > 4 || r->nmake_extra > 4) { tscope = bscope = false; return -1; }
  if (bscope) {
    int rid = add_rule(r, cn);
    if (rid >= 0) prep_rule(&R[rid]);
    release(NULL, 0);
    return rid;
  }
  Rule c = *r; Term *ts[64]; int n = 0;                     /* every pattern, for release */
  for (int i = 0; i < c.ntake; i++) ts[n++] = &c.take[i].t;
  for (int i = 0; i < c.nkeep; i++) ts[n++] = &c.keep[i].t;
  for (int i = 0; i < c.nabsent; i++) ts[n++] = &c.absent[i].t;
  for (int i = 0; i < c.ncount; i++) ts[n++] = &c.count[i].t;
  for (int i = 0; i < c.ntell; i++) { ts[n++] = &c.tell[i][0]; ts[n++] = &c.tell[i][1]; }
  for (int i = 0; i < c.nneq; i++) { ts[n++] = &c.neq[i][0]; ts[n++] = &c.neq[i][1]; }
  ts[n++] = &c.make.t;
  for (int i = 0; i < c.nmake_extra; i++) ts[n++] = &c.make_extra[i].t;
  release(ts, n);
  return add_rule(&c, cn);
}
uint8_t tc_rule_fibre(int rid) {
  if (rid < 0 || rid >= nr) return 0;
  if (!R[rid].fprepped) prep_flat(&R[rid]);
  return R[rid].fibre;
}

/* Sorts, binders and separation, for the holes that are bound.
   given: holes the caller supplied; the others came from matching well-formed premises. */
static bool holes_ok(const RuleK *k, Term *S, uint64_t given, bool clean) {
  Term U[TC_VARS];
  for (int h = 0; h < k->n; h++) {
    if (!(U[h] = S[h])) continue;
    Term t = U[h] = walk(S[h]);
    if (N[t].vm) return false;
    if ((k->implied >> h & 1) && !(given >> h & 1) && clean) continue;
    if (HOLE(k, h).sort != TC_ANY && N[t].sort != HOLE(k, h).sort) return false;
    if (HOLE(k, h).bound && !is_bvar(t)) return false;
  }
  for (uint64_t m = k->bounds; m; m &= m - 1) {
    int h = __builtin_ctzll(m);
    for (uint64_t a = U[h] ? HOLE(k, h).avoid : 0; a; a &= a - 1) {
      int j = __builtin_ctzll(a);
      if (U[j] && (has_meta(U[j]) || (N[U[h]].bm & N[U[j]].bm))) return false;
    }
  }
  return true;
}

/* ---- conversion: definitional unfolding, congruence, symmetry ---- */
static uint64_t fv_rec(Term t, uint32_t g, int depth) {
  if (depth > 4096) return ~0ull;
  if (N[t].kind != K_APP || !N[t].bm) return N[t].bm;
  if (vis[t] == g) return vval[t];
  const Con *c = &C[N[t].head]; const Term *a = argv(t);
  uint64_t acc = 0, bd[TC_ARGS];
  for (int i = 0; i < c->arity; i++) {
    if (c->abound >> i & 1) { bd[i] = N[a[i]].bm; if (c->retdeps >> i & 1) acc |= bd[i]; continue; }
    uint64_t d = fv_rec(a[i], g, depth + 1);
    uint32_t deps = c->abound ? CD[N[t].head].adeps[i] : 0;
    for (int j = 0; j < i; j++) if (deps >> j & 1) d &= ~bd[j];
    acc |= d;
  }
  vis[t] = g; return vval[t] = acc;
}
static uint64_t fv(Term t) { return fv_rec(t, next_vgen(), 0); }

int tc_def(uint16_t s, uint64_t retdeps, int ar, int nd, Term body) {
  if (ncon >= CAP_CON || ar + nd != cn || ar > TC_ARGS || ar < 0 || nd < 0 || s >= nsort || (sorts[s] & SORT_PURE)
      || !body || body >= nn || !ctx_ok(body) || (N[body].flags & (F_META | F_BV)) || (N[body].vm & ~mask(cn))
      || N[body].sort != s || !name_ok(body)) { tscope = bscope = false; return -1; }
  Binder a[TC_ARGS];
  uint64_t retbits = 0;
  for (int i = 0; i < ar; i++) {
    a[i] = (Binder){ csort[i], cbound[i], cdeps[i] };
    if (retdeps >> i & 1) { if (!cbound[i]) { tscope = bscope = false; return -1; } retbits |= cbm[i]; }
  }
  for (int i = ar; i < cn; i++) if (!cbound[i] || (sorts[csort[i]] & (SORT_STRICT | SORT_FREE))) { tscope = bscope = false; return -1; }
  if (fv(body) & ~retbits) { tscope = bscope = false; return -1; }               /* free variables, binders respected, are declared */
  int id = tc_con(s, retdeps, ar, a);
  if (id < 0) { tscope = bscope = false; return -1; }
  for (int i = 0; i < nd; i++) CD[id].dsort[i] = (uint8_t)csort[ar + i];
  tscope = bscope = false;
  C[id].isdef = 1; C[id].body = body; C[id].ndum = (uint16_t)nd;
  return id;
}

static bool smatch(Term p, Term t, const Term *S, int d) {   /* t is p with its holes at S: holes by identity */
  if (d > 4096 || !t || t >= nn) return false;
  if (N[p].kind == K_VAR) return S[N[p].head] == t;
  if (N[p].kind != K_APP) return p == t;
  if (N[t].kind != K_APP || N[t].head != N[p].head || N[t].arity != N[p].arity) return false;
  for (int i = 0; i < N[p].arity; i++) if (!smatch(argv(p)[i], argv(t)[i], S, d + 1)) return false;
  return true;
}
static bool conv(const Conv *c, Term l, Term r, int depth) {   /* c proves l = r */
  if (!c || depth > 1000 || !l || !r || l >= nn || r >= nn) return false;
  switch (c->kind) {
    case CV_REFL:
      if (l == r) return true;
      return rho_quote_con >= 0 && rho_drop_con >= 0 && tc_rho_norm_name(l) == tc_rho_norm_name(r);
    case CV_SYM: return conv(c->kid, r, l, depth + 1);
    case CV_CONG: {
      int n = c->n;
      if (c->con < 0 || c->con >= ncon || n != C[c->con].arity || (n > 0 && !c->kid)) return false;
      if (N[l].kind != K_APP || N[r].kind != K_APP || N[l].head != (uint32_t)c->con || N[r].head != (uint32_t)c->con) return false;
      if (c->con == q_quote_con) return l == r;          /* inert quotation: no congruence inside quote */
      Term ls[TC_ARGS], rs[TC_ARGS];                      /* copied: a kid may make terms */
      for (int i = 0; i < n; i++) { ls[i] = argv(l)[i]; rs[i] = argv(r)[i]; }
      for (int i = 0; i < n; i++) if (!conv(&c->kid[i], ls[i], rs[i], depth + 1)) return false;
      return true;
    }
    case CV_UNFOLD: {                                     /* l = D(args); its body at args and dummies is c->t, or is made */
      if (c->con < 0 || c->con >= ncon || !C[c->con].isdef || !c->kid) return false;
      const Con *d = &C[c->con];
      if (N[l].kind != K_APP || N[l].head != (uint32_t)c->con || has_meta(l) || (d->ndum > 0 && !c->dummies)) return false;
      Term S[TC_VARS];
      for (int i = 0; i < d->arity; i++) {
        S[i] = argv(l)[i];
        if (c->args && c->args[i] != S[i]) return false;
      }
      for (int k = 0; k < d->ndum; k++) {                /* dummies: distinct bound variables, fresh for the args */
        Term x = S[d->arity + k] = c->dummies[k];
        if (!x || x >= nn || !is_bvar(x) || N[x].sort != CD[c->con].dsort[k]) return false;
        for (int i = 0; i < d->arity + k; i++) if (N[S[i]].bm & N[x].bm) return false;
      }
      Term e = c->t;
      if (e ? !smatch(d->body, e, S, 0) : !(e = inst(d->body, S, false))) return false;
      return conv(c->kid, e, r, depth + 1);
    }
  }
  return false;
}

/* ---- the board ---- */
static inline const Term *wargs(Occ o, uint32_t head) {
  return __builtin_expect(!has_widecon, 1) || C[head].arity <= 4 ? &Wrow[(size_t)o << 2] : &A[Warg[o]];
}
static __attribute__((noinline)) bool grow_w(uint32_t need) {
  uint32_t m = wcap ? wcap : 2;
  while (m <= need) {
    if (m > (1u << 27)) return false;
    m *= 2;
  }
  Term *a = realloc(Wt, m * sizeof *a), *d = realloc(Wtag, m * sizeof *d), *e = realloc(Warg, m * sizeof *e);
  Term *rw = realloc(Wrow, (size_t)m * 4 * sizeof *rw), *sp = realloc(Wsp, m * sizeof *sp);
  Occ *nx = realloc(Wnext, m * sizeof *nx), *pr = realloc(Wprev, m * sizeof *pr);
  uint8_t *b = realloc(Ws, m), *c = realloc(Wa, m), *mk_b = realloc(Wmark, m);
  if (a) Wt = a;
  if (d) Wtag = d;
  if (e) Warg = e;
  if (rw) Wrow = rw;
  if (sp) Wsp = sp;
  if (nx) Wnext = nx;
  if (pr) Wprev = pr;
  if (b) Ws = b;
  if (c) Wa = c;
  if (mk_b) Wmark = mk_b;
  if (!a || !d || !e || !rw || !sp || !nx || !pr || !b || !c || !mk_b) return false;
  memset(Wt + wcap, 0, (m - wcap) * sizeof *Wt);
  memset(Wtag + wcap, 0, (m - wcap) * sizeof *Wtag);
  memset(Warg + wcap, 0, (m - wcap) * sizeof *Warg);
  memset(Wsp + wcap, 0, (m - wcap) * sizeof *Wsp);
  memset(Wnext + wcap, 0, (m - wcap) * sizeof *Wnext);
  memset(Wprev + wcap, 0, (m - wcap) * sizeof *Wprev);
  memset(Ws + wcap, 0, m - wcap);
  memset(Wa + wcap, 0, m - wcap);
  memset(Wmark + wcap, 0, m - wcap);
  if (slot_mode) {
    uint32_t tag0 = Wtag[0];
    uint8_t s0 = Ws[0];
    Term r0 = Wrow[0], r1 = Wrow[1], r2 = Wrow[2], r3 = Wrow[3];
    for (uint32_t i = wcap; i < m; i++) {
      Term *ri = &Wrow[(size_t)i << 2];
      ri[0] = r0; ri[1] = r1; ri[2] = r2; ri[3] = r3;
      Wtag[i] = tag0; Ws[i] = s0; Wa[i] = 1;
    }
    nw = m;
  } else {
    memset(Wrow + (size_t)wcap * 4, 0, (size_t)(m - wcap) * 4 * sizeof *Wrow);
  }
  wcap = m;
  return true;
}
void tc_unset(Occ u) {
  if (!u || u >= nw || !Wtag[u] || C[Wtag[u] >> 9].arity > 4) return;
  slot_mode = true;
  uint32_t tag0 = Wtag[0] = Wtag[u];
  uint8_t s0 = Ws[0] = Ws[u]; Wa[0] = 1;
  const Term *ru = wargs(u, tag0 >> 9);
  Term r0 = ru[0], r1 = ru[1], r2 = ru[2], r3 = ru[3];
  Wrow[0] = r0; Wrow[1] = r1; Wrow[2] = r2; Wrow[3] = r3;
  Wt[u] = 0; wt_dirty = false;
  for (uint32_t i = nw; i < wcap; i++) {
    Term *ri = &Wrow[(size_t)i << 2];
    ri[0] = r0; ri[1] = r1; ri[2] = r2; ri[3] = r3;
    Wtag[i] = tag0; Ws[i] = s0; Wa[i] = 1;
  }
  nw = wcap;
}
static Occ post(uint8_t s, Term t) {
  tscope = bscope = false;
  if (!Nocc && !(Nocc = calloc(ncap, sizeof *Nocc))) return 0;
  Occ o = Nocc[t];
  if (sealed && !has_take && o && o < nw && Wt[o] == t && Ws[o] == s && !Wsp[o] && !Wmark[o] && Wa[o]) return o;
  if (nw >= wcap && !grow_w(nw)) return 0;
  Nocc[t] = nw; Wt[nw] = t; Ws[nw] = s; Wsp[nw] = 0; Wmark[nw] = 0; Wa[nw] = 1; wt_dirty = true;
  Wtag[nw] = !has_meta(t) && N[t].kind == K_APP ? (N[t].head << 9) | ((uint32_t)s << 1) | 1u : 0;
  Warg[nw] = N[t].args;
  if (Wtag[nw] && N[t].arity <= 4) {
    Term *rw = &Wrow[(size_t)nw << 2]; const Term *a = &A[N[t].args];
    for (int j = 0; j < N[t].arity; j++) rw[j] = a[j];
  }
  Wprev[nw] = 0; Wnext[nw] = Wlive; if (Wlive) Wprev[Wlive] = nw; Wlive = nw;
  return nw++;
}
uint16_t tc_space_sort(void) {
  if (!space_sort_id) {
    int s = tc_sort(0);
    if (s < 0) return 0;
    space_sort_id = (uint16_t)s;
  }
  return space_sort_id;
}
Term tc_space_term(uint8_t s) {
  uint16_t sp_sort = tc_space_sort();
  if (!sp_sort) return 0;
  Term c = space_terms[s];
  if (c && c < nn && N[c].kind == K_NAME && N[c].sort == sp_sort && Nid && Nid[c] == ((1ull << 62) | (uint64_t)s))
    return c;
  if (!Nid) { Nid = calloc(ncap, sizeof *Nid); Nmax = calloc(ncap, sizeof *Nmax); if (!Nid || !Nmax) return 0; }
  bool old_ts = tscope, old_bs = bscope;
  tscope = bscope = false;
  Term t = mk(K_NAME, 0, sp_sort, 0, (1ull << 62) | (uint64_t)s, 0, NULL);
  tscope = old_ts; bscope = old_bs;
  if (t) { Nmax[t] = 0; space_terms[s] = t; }
  return t;
}
static int static_space_of(Term sp) {
  if (space_sort_id && sp && sp < nn && N[sp].kind == K_NAME && N[sp].sort == space_sort_id && Nid && (Nid[sp] >> 62) == 1)
    return (int)(Nid[sp] & 0xFFu);
  return -1;
}
static Occ post_at_internal(Term sp, Term t, uint8_t marker) {
  tscope = bscope = false;
  if (!sp) return 0;
  int s_idx = static_space_of(sp);
  if (s_idx >= 0 && !marker) return post((uint8_t)s_idx, t);
  has_take = true;
  if (!Nocc && !(Nocc = calloc(ncap, sizeof *Nocc))) return 0;
  if (nw >= wcap && !grow_w(nw)) return 0;
  uint8_t s = s_idx >= 0 ? (uint8_t)s_idx : 255;
  Occ o = nw++;
  Wt[o] = t; Ws[o] = s; Wsp[o] = sp; Wmark[o] = marker ? 1 : 0; Wa[o] = 1; wt_dirty = true;
  Wtag[o] = 0; Warg[o] = N[t].args;
  Wprev[o] = 0; Wnext[o] = Wlive; if (Wlive) Wprev[Wlive] = o; Wlive = o;
  return o;
}
Occ tc_post(uint8_t s, Term t) {
  if (!t || t >= nn || N[t].vm || !name_ok(t) || (protect[s] && sealed)) return 0;
  return post(s, t);
}
Occ tc_post_at(Term space, Term t, bool marker) {
  if (!space || space >= nn || N[space].vm || !name_ok(space) || !t || t >= nn || N[t].vm || !name_ok(t)) return 0;
  int s_idx = static_space_of(space);
  if (s_idx >= 0 && protect[s_idx] && sealed) return 0;
  return post_at_internal(space, t, marker ? 1 : 0);
}
Term tc_occ_space(Occ o) {
  if (!o || o >= nw || !Wa[o]) return 0;
  return Wsp[o] ? Wsp[o] : tc_space_term(Ws[o]);
}
bool tc_occ_marker(Occ o) { return o && o < nw && Wa[o] && Wmark[o] != 0; }
bool tc_space_born(Term space) {
  if (!space || space >= nn) return false;
  space = norm(space);
  for (Occ o = Wlive; o; o = Wnext[o])
    if (Wa[o] && Wmark[o] && norm(tc_occ_space(o)) == space) return true;
  return false;
}
bool tc_alive(Occ o) { return o && o < nw && Wa[o]; }
Term tc_term(Occ o) {
  if (o >= nw || !Wa[o]) return 0;
  if (!Wt[o] && Wtag[o]) { Wt[o] = tc_app((int)(Wtag[o] >> 9), wargs(o, Wtag[o] >> 9)); wt_dirty = true; }
  return Wt[o];
}
const Term *tc_flat_args(Occ o, uint32_t ktag) {
  Occ u = o < nw ? o : 0;
  return __builtin_expect(ktag != 0 && Wtag[u] == ktag, 1) ? wargs(u, ktag >> 9) : NULL;
}
static __attribute__((noinline)) Occ flat_store_slow(Occ dest, uint32_t tag, const Term *b) {
  uint32_t head = tag >> 9;
  uint8_t s = (uint8_t)((tag >> 1) & 0xFFu);
  uint16_t sort = C[head].sort;
  int ar = C[head].arity;
  if (!has_take && dest && dest < nw && Wtag[dest] == tag) {
    Term *dst = ar <= 4 ? &Wrow[(size_t)dest << 2] : &A[Warg[dest]];
    for (int j = 0; j < ar; j++) dst[j] = b[j];
    if (wt_dirty) Wt[dest] = 0;
    return dest;
  }
  if (slot_mode && !has_take && dest >= nw && ar <= 4) {
    if (!grow_w(dest)) return 0;
    Term *dst = &Wrow[(size_t)dest << 2];
    for (int j = 0; j < ar; j++) dst[j] = b[j];
    Wtag[dest] = tag; Ws[dest] = s; Wa[dest] = 1;
    if (wt_dirty) Wt[dest] = 0;
    return dest;
  }
  if (__builtin_expect(nw >= wcap || (ar > 4 && na + (uint32_t)ar > acap), 0)) {
    Term out = mk(K_APP, head, sort, 0, 0, ar, b);
    return out ? post(s, out) : 0;
  }
  Occ o = nw++;
  if (ar <= 4) {
    Term *dst = &Wrow[(size_t)o << 2];
    for (int j = 0; j < ar; j++) dst[j] = b[j];
    Warg[o] = 0;
  } else {
    uint32_t a0 = na; na += (uint32_t)ar;
    for (int j = 0; j < ar; j++) A[a0 + (uint32_t)j] = b[j];
    Warg[o] = a0;
  }
  Wt[o] = 0; Wtag[o] = tag; Ws[o] = s; Wa[o] = 1;
  Wprev[o] = 0; Wnext[o] = Wlive; if (Wlive) Wprev[Wlive] = o; Wlive = o;
  return o;
}
static inline Occ flat_store(Occ dest, uint32_t tag, int ar, const Term *b) {
  if (__builtin_expect(!has_take && dest - 1u < nw - 1u && Wtag[dest] == tag && ar <= 4, 1)) {
    Term *dst = &Wrow[(size_t)dest << 2];
    for (int j = 0; j < ar; j++) dst[j] = b[j];
    if (__builtin_expect(wt_dirty, 0)) Wt[dest] = 0;
    return dest;
  }
  return flat_store_slow(dest, tag, b);
}
Occ tc_flat_make(uint8_t s, uint32_t head, uint16_t sort, int ar, const Term *a) {
  if (head >= (uint32_t)ncon || C[head].sort != sort || C[head].arity != ar) return 0;
  return tc_post(s, tc_app((int)head, a));
}
static __attribute__((noinline)) Occ tc_flat_put_slow(Occ dest, uint8_t s, int con, const Term *a) {
  if ((unsigned)con >= (unsigned)ncon || (protect[s] && sealed)) return 0;
  const Con *c = &C[con];
  int ar = c->arity;
  for (int i = 0; i < ar; i++) {
    Term x = a[i];
    if (!x || x >= nn || N[x].sort != c->asort[i] || N[x].vm || !name_ok(x)) return 0;
    if (!tscope && !has_meta(x) && c->asort[i] == ncache_sort) N[x].flags |= F_PLAIN;
  }
  return flat_store(dest, ((uint32_t)con << 9) | ((uint32_t)s << 1) | 1u, ar, a);
}
Occ tc_flat_put(Occ dest, uint8_t s, int con, const Term *a) {
  if (__builtin_expect(flat4_board && !s && !con && dest - 1u < nw - 1u, 1)) {
    Term x0 = a[0], x1 = a[1], x2 = a[2], x3 = a[3];
    uint32_t lim = nn;
    if (__builtin_expect(x0 < lim && x1 < lim && x2 < lim && x3 < lim &&
        ((N[x0].flags & N[x1].flags & N[x2].flags & N[x3].flags & F_PLAIN) != 0), 1)) {
      Term *dst = &Wrow[(size_t)dest << 2];
      dst[0] = x0; dst[1] = x1; dst[2] = x2; dst[3] = x3;
      if (__builtin_expect(wt_dirty, 0)) Wt[dest] = 0;
      return dest;
    }
  }
  return tc_flat_put_slow(dest, s, con, a);
}
Occ tc_flat_out(Occ dest, uint8_t s, int con, const Term *a) {
  if ((unsigned)con >= (unsigned)ncon || (protect[s] && sealed)) return 0;
  return flat_store(dest, ((uint32_t)con << 9) | ((uint32_t)s << 1) | 1u, C[con].arity, a);
}
static __attribute__((noinline)) Occ tc_flat_fire_slow(int rid, const Occ *keep, const Term *in, Occ dest) {
  if ((unsigned)rid >= (unsigned)nr) return 0;
  RuleK *k = &R[rid];
  if (__builtin_expect(!k->fprepped, 0)) prep_flat(k);
  if (__builtin_expect(!in && k->flat && keep != NULL, 1)) {
    const Flat *q = &FL[k->fl];
    int nk = k->nkeep, ng = q->nguard, ar = q->mar;
    const Term *pa[TC_HYPS + 1];
    pa[nk] = q->mc;
    for (int i = 0; i < nk; i++) {
      Occ o = keep[i];
      if (slot_mode) {
        Occ u = o < nw ? o : 0;
        if (__builtin_expect(Wtag[u] != q->ktag[i], 0)) return 0;
        pa[i] = wargs(u, q->ktag[i] >> 9);
      } else {
        if (__builtin_expect(!o || o >= nw || Wtag[o] != q->ktag[i], 0)) return 0;
        pa[i] = wargs(o, q->ktag[i] >> 9);
      }
    }
    for (int g = 0; g < ng; g++) {
      Guard e = q->guard[g];
      if (pa[e.i][e.j] != pa[e.i0][e.j0]) return 0;
    }
    Term b[TC_ARGS];
    for (int j = 0; j < ar; j++) b[j] = pa[q->mi[j]][q->mj[j]];
    return flat_store(dest, (q->mhead << 9) | ((uint32_t)k->mspace << 1) | 1u, ar, b);
  }
  if (__builtin_expect(!keep && k->mflat && in != NULL, 1)) {
    const Rule *r = RULE(k);
    Term m = k->make;
    uint64_t req = N[m].vm & ~(r->fresh >= 0 ? (1ull << r->fresh) : 0ull);
    if (r->fresh >= 0 && in[r->fresh]) return 0;
    for (int h = 0; h < k->n; h++) {
      Term t = in[h];
      if (!t) { if (req >> h & 1) return 0; continue; }
      if (t >= nn || N[t].vm || has_meta(t)) goto full;
      if (HOLE(k, h).sort != TC_ANY && N[t].sort != HOLE(k, h).sort) return 0;
      if (!k->pure && !name_ok(t)) return 0;
    }
    Term ft = 0;
    uint64_t nmark = next_name;
    if (r->fresh >= 0) {
      if (next_name >= UINT64_MAX - 1 || !(ft = tc_name(HOLE(k, r->fresh).sort, next_name))) return 0;
      next_name++;
    }
    int ar = N[m].arity;
    const Term *ma = argv(m);
    Term b[TC_ARGS];
    for (int j = 0; j < ar; j++) {
      Term a = ma[j];
      b[j] = !N[a].vm ? a : ((int)N[a].head == r->fresh ? ft : in[N[a].head]);
    }
    Occ o = flat_store(dest, (N[m].head << 9) | ((uint32_t)k->mspace << 1) | 1u, ar, b);
    if (!o) next_name = nmark;
    else if (ft && !tscope && ncache_sort == HOLE(k, r->fresh).sort) N[ft].flags |= F_PLAIN;
    return o;
  }
full:;
  Occ o = tc_fire(rid, NULL, keep, in);
  if (!o || !Wtag[o]) return o;
  uint32_t head = Wtag[o] >> 9;
  const Term *src = wargs(o, head);
  Term b[TC_ARGS];
  for (int j = 0; j < C[head].arity; j++) b[j] = src[j];
  return flat_store(dest, Wtag[o], C[head].arity, b);
}
Occ tc_flat_fire(int rid, const Occ *keep, const Term *in, Occ dest) {
#ifdef __AVX512F__
  if (__builtin_expect((unsigned)rid < 64 && FF[rid].single_tag && !in && keep != NULL && !has_take, 1)) {
    const Flat4 *q = &FF[rid];
    uint32_t lim = nw;
    if (__builtin_expect(dest - 1u >= lim - 1u, 0)) return tc_flat_fire_slow(rid, keep, in, dest);
    Occ o0 = keep[0], o1 = keep[1], o2 = keep[2], o3 = keep[3];
    o0 = o0 < lim ? o0 : 0;
    o1 = o1 < lim ? o1 : 0;
    o2 = o2 < lim ? o2 : 0;
    o3 = o3 < lim ? o3 : 0;
    const Term *w = Wrow;
    __m128i x0 = _mm_loadu_si128((const __m128i *)&w[(size_t)o0 << 2]);
    __m128i x1 = _mm_loadu_si128((const __m128i *)&w[(size_t)o1 << 2]);
    __m128i x2 = _mm_loadu_si128((const __m128i *)&w[(size_t)o2 << 2]);
    __m128i x3 = _mm_loadu_si128((const __m128i *)&w[(size_t)o3 << 2]);
    __m256i y0 = _mm256_inserti128_si256(_mm256_castsi128_si256(x0), x1, 1);
    __m256i y1 = _mm256_inserti128_si256(_mm256_castsi128_si256(x2), x3, 1);
    __m512i z = _mm512_inserti64x4(_mm512_castsi256_si512(y0), y1, 1);
    __m512i perm = _mm512_cvtepu8_epi32(_mm_load_si128((const __m128i *)q->perm));
    if (_mm512_cmpneq_epi32_mask(z, _mm512_permutexvar_epi32(perm, z))) return 0;
    __m512i mperm = _mm512_zextsi128_si512(_mm_load_si128((const __m128i *)q->mperm));
    __m128i out = _mm512_castsi512_si128(_mm512_permutexvar_epi32(mperm, z));
    _mm_storeu_si128((__m128i *)&w[(size_t)dest << 2], out);
    if (__builtin_expect(wt_dirty, 0)) Wt[dest] = 0;
    return dest;
  }
#endif
  return tc_flat_fire_slow(rid, keep, in, dest);
}

static bool in_term_set(Term t, const Term *set, int n) {
  if (!t) return false;
  t = norm(t);
  for (int i = 0; i < n; i++) if (norm(set[i]) == t) return true;
  return false;
}
void tc_set_handle_con(int con) { handle_con_id = con; }
static void collect_handles(Term t, Term *out, int *nr_sp, int cap, bool *changed, int d) {
  if (!t || t >= nn || d > 256) return;
  if (handle_con_id >= 0) {
    if (N[t].kind == K_APP && (int)N[t].head == handle_con_id && N[t].arity >= 1) {
      Term h = norm(argv(t)[0]);
      if (h && !in_term_set(h, out, *nr_sp) && *nr_sp < cap) { out[(*nr_sp)++] = h; *changed = true; }
    }
    if (N[t].kind == K_APP) for (int i = 0; i < N[t].arity; i++) collect_handles(argv(t)[i], out, nr_sp, cap, changed, d + 1);
  } else {
    if (space_sort_id && N[t].sort == space_sort_id) {
      Term h = norm(t);
      if (h && !in_term_set(h, out, *nr_sp) && *nr_sp < cap) { out[(*nr_sp)++] = h; *changed = true; }
    }
    if (N[t].kind == K_APP) for (int i = 0; i < N[t].arity; i++) collect_handles(argv(t)[i], out, nr_sp, cap, changed, d + 1);
  }
}
int tc_reach(const Term *seeds, int nseed, Term *out, int cap) {
  if (!out || cap <= 0) return 0;
  int nr_sp = 0;
  for (int i = 0; i < nseed; i++) {
    Term s = seeds[i] ? norm(seeds[i]) : 0;
    if (!s) continue;
    if (handle_con_id >= 0 && N[s].kind == K_APP && (int)N[s].head == handle_con_id) {
      bool dummy = false;
      collect_handles(s, out, &nr_sp, cap, &dummy, 0);
    } else if (!in_term_set(s, out, nr_sp) && nr_sp < cap) {
      out[nr_sp++] = s;
    }
  }
  bool changed = true;
  while (changed) {
    changed = false;
    for (Occ o = Wlive; o; o = Wnext[o]) if (Wa[o] && !Wmark[o]) {
      Term osp = tc_occ_space(o);
      if (!in_term_set(osp, out, nr_sp)) continue;
      collect_handles(norm(tc_term(o)), out, &nr_sp, cap, &changed, 0);
    }
  }
  return nr_sp;
}
Occ tc_last_extra(int idx) { return (idx >= 0 && idx < 4) ? last_extra_occ[idx] : 0; }

static bool count_ok_at(Term pat, uint8_t space, Term space_term, uint32_t want, const Term *S, int n,
                        const Term *reach_set, int nreach, bool enforce_reach) {
  const RuleK *rk = cur_k;
  if (enforce_reach) {
    if (space_term) {
      Term sp_b = inst(space_term, (Term *)S, false);
      if (!sp_b || N[sp_b].vm) return false;
      sp_b = norm(sp_b);
      if (!sp_b || has_meta(sp_b) || !in_term_set(sp_b, reach_set, nreach)) return false;
    } else if (!in_term_set(tc_space_term(space), reach_set, nreach)) return false;
  }
  uint32_t m_local = CAP_META - TC_VARS, hits = 0;
  Term E[TC_VARS];
  for (int h = 0; h < n; h++) E[h] = S[h] ? S[h] : qmeta[h];
  Term p = inst(pat, E, false);
  if (!p) return false;
  Term sp_p = space_term ? inst(space_term, E, false) : 0;
  if (space_term && !sp_p) return false;
  uint64_t vm_mask = N[pat].vm | (space_term ? N[space_term].vm : 0);
  for (Occ o = Wlive, nxt; o; o = nxt) {
    nxt = Wnext[o];
    if (!Wa[o]) {
      if (Wprev[o]) Wnext[Wprev[o]] = Wnext[o]; else Wlive = Wnext[o];
      if (Wnext[o]) Wprev[Wnext[o]] = Wprev[o];
    }
    if (!Wa[o] || Wmark[o]) continue;
    if (!space_term && (Ws[o] != space || (Wsp[o] && Wsp[o] != tc_space_term(space)))) continue;
    uint32_t m = ntrail;
    bool hit = (!space_term || unify(sp_p, tc_occ_space(o))) && unify(p, tc_term(o)) && diseqs_ok(), amb = false;
    for (uint32_t k = m; hit && k < ntrail; k++) amb |= trail[k] < m_local;
    if (hit && !amb && rk && vm_mask) {
      Term Q[TC_VARS] = {0};
      for (int h = 0; h < n; h++) if (S[h] || (vm_mask >> h & 1)) {
        Term t = Q[h] = norm(E[h]);
        uint16_t ts = N[t].kind == K_META ? Msort[N[t].head] : N[t].sort;
        if (HOLE(rk, h).sort != TC_ANY && ts != HOLE(rk, h).sort) { if (ts == TC_ANY) amb = true; else hit = false; }
        if (rk->bounds && has_meta(t)) amb = true;
      }
      if (hit && !amb && rk->bounds && !holes_ok(rk, Q, vm_mask, false)) hit = false;
    }
    undo(m);
    if (amb || (hit && ++hits > want)) return false;
  }
  return hits == want;
}

static Occ fire_ex(int rid, const Occ *take, const Occ *keep, const Term *in,
                   const Term *reach_seeds, int nseed, bool enforce_reach) {
  if (rid < 0 || rid >= nr) return 0;
  nsteps++;
  RuleK *k = &R[rid];
  if (__builtin_expect(!k->fprepped, 0)) prep_flat(k);
  const Rule *r = RULE(k);
  if (!enforce_reach && !in && !take && k->flat && keep) {
    const Flat *q = &FL[k->fl];
    const Term *pa[TC_HYPS + 1]; pa[k->nkeep] = q->mc;
    for (int i = 0; i < k->nkeep; i++) {
      Occ o = keep[i];
      if (!o || o >= nw || Wtag[o] != q->ktag[i]) {
        if (o && o < nw && Wa[o] && has_meta(tc_term(o))) goto slow;
        return 0;
      }
      pa[i] = wargs(o, q->ktag[i] >> 9);
    }
    for (int g = 0; g < q->nguard; g++) {
      Guard e = q->guard[g];
      if (pa[e.i][e.j] != pa[e.i0][e.j0]) return 0;
    }
    Term b[TC_ARGS];
    for (int j = 0; j < q->mar; j++) b[j] = pa[q->mi[j]][q->mj[j]];
    Term out = mk(K_APP, q->mhead, q->msort, 0, 0, q->mar, b);
    return out ? post(k->mspace, out) : 0;
  }
slow:;
  Term S[TC_VARS]; uint64_t given = 0;
  uint32_t mmark = nmeta;
  uint32_t mark = ntrail; int nemark = nne; uint64_t nmark = next_name;
  Term reach_set[512]; int nreach = 0;
  if (enforce_reach) nreach = tc_reach(reach_seeds, nseed, reach_set, 512);
  ug++;
  if (!ug) { memset(ugen, 0, sizeof ugen); ug = 1; }
  for (int h = 0; h < k->n; h++) {
    S[h] = in ? in[h] : 0;
    if (S[h] && (S[h] >= nn || N[S[h]].vm)) return 0;
    if (S[h]) given |= 1ull << h;
  }
  if (r->fresh >= 0 && S[r->fresh]) return 0;
  for (int i = 0; i < r->ntake; i++) {
    if (!take || !tc_alive(take[i]) || Wmark[take[i]]) goto fail;  /* Births.keeps: never take a marker */
    for (int j = 0; j < i; j++) if (take[j] == take[i]) goto fail;
    Term osp = tc_occ_space(take[i]), pt, psp; uint8_t pmk;
    unpack_pat(r->take[i].t, &pt, &psp, &pmk);
    if (enforce_reach && !in_term_set(osp, reach_set, nreach)) goto fail;
    if (psp) {
      if (!umatch(psp, osp, S)) goto fail;
    } else if (Ws[take[i]] != r->take[i].space || (Wsp[take[i]] && osp != tc_space_term(r->take[i].space))) goto fail;
    if (!umatch(pt, tc_term(take[i]), S)) goto fail;
  }
  bool can_run = k->kcode != UINT32_MAX;
  for (int i = 0; i < k->nkeep; i++) {
    if (!keep || !tc_alive(keep[i]) || Wmark[keep[i]]) goto fail;
    for (int j = 0; j < r->ntake; j++) if (take[j] == keep[i]) goto fail;
    Term osp = tc_occ_space(keep[i]), pt, psp; uint8_t pmk;
    unpack_pat(r->keep[i].t, &pt, &psp, &pmk);
    if (enforce_reach && !in_term_set(osp, reach_set, nreach)) goto fail;
    if (psp) {
      if (!umatch(psp, osp, S)) goto fail;
      can_run = false;
    } else if (Ws[keep[i]] != r->keep[i].space || (Wsp[keep[i]] && osp != tc_space_term(r->keep[i].space))) goto fail;
    can_run &= !has_meta(tc_term(keep[i]));
  }
  if (can_run) {
    int sp = 0;
    for (int i = k->nkeep - 1; i >= 0; i--) run_st[sp++] = tc_term(keep[i]);
    if (!run_stack(k->kcode, sp, S, false)) goto fail;
  } else {
    for (int i = 0; i < k->nkeep; i++) {
      Term pt, psp; uint8_t pmk; unpack_pat(r->keep[i].t, &pt, &psp, &pmk);
      if (!umatch(pt, tc_term(keep[i]), S)) goto fail;
    }
  }
  for (int i = 0; i < r->ntell; i++) {
    Term a = inst(r->tell[i][0], S, true), b = inst(r->tell[i][1], S, true);
    if (!a || !b || !unify(a, b)) goto fail;
  }
  for (int i = 0; i < r->nneq; i++) {
    Term a = inst(r->neq[i][0], S, true), b = inst(r->neq[i][1], S, true);
    if (!a || !b) goto fail;
    Term na = norm(a), nb = norm(b);
    if (!na || !nb || na == nb) goto fail;
    if (!has_meta(na) && !has_meta(nb)) continue;
    if (nne >= 65536) goto fail;
    NE[nne][0] = a; NE[nne][1] = b; nne++;
  }
  bool clean = !r->ntake && !r->ntell && !r->nneq;
  if (!k->pure) clean = false;
  for (int i = 0; clean && i < k->nkeep; i++) clean = !has_meta(tc_term(keep[i]));
  for (int h = 0; clean && h < k->n; h++) clean = !S[h] || !has_meta(S[h]);
  for (int h = 0; !clean && h < k->n; h++) if (S[h] && has_meta(S[h]) && !(S[h] = norm(S[h]))) goto fail;
  if ((nne && !diseqs_ok()) || !holes_ok(k, S, given, clean)) goto fail;
  cur_k = k;
  for (int i = 0; i < r->nabsent; i++) {
    Term pt, psp; uint8_t pmk; unpack_pat(r->absent[i].t, &pt, &psp, &pmk);
    if (!count_ok_at(pt, r->absent[i].space, psp, 0, S, k->n, reach_set, nreach, enforce_reach)) goto fail;
  }
  for (int i = 0; i < r->ncount; i++) {
    Term pt, psp; uint8_t pmk; unpack_pat(r->count[i].t, &pt, &psp, &pmk);
    if (!count_ok_at(pt, r->count[i].space, psp, r->count[i].n, S, k->n, reach_set, nreach, enforce_reach)) goto fail;
  }
  if (!k->pure) {
    for (int h = 0; h < k->n; h++) if (S[h] && !name_ok(S[h])) goto fail;
  }
  if (r->fresh >= 0) {                                /* EXTEND: a new name, defined from existing ones */
    for (int h = 0; h < k->n; h++) if (S[h] && has_meta(S[h])) goto fail;
    if (next_name >= UINT64_MAX - 1 || !(S[r->fresh] = tc_name(HOLE(k, r->fresh).sort, next_name))) goto fail;
    next_name++;
  }
  int nmake = 1 + r->nmake_extra;
  Term m_out[5], m_sp[5]; uint8_t m_raw_s[5], m_mark[5]; bool m_has_sp[5];
  for (int m = 0; m < nmake; m++) {
    const Pat *mp = (m == 0) ? &r->make : &r->make_extra[m - 1];
    Term pt, psp; uint8_t pmk; unpack_pat(mp->t, &pt, &psp, &pmk);
    Term out_t = inst(pt, S, false);
    if (!out_t || N[out_t].vm || (!clean && has_meta(out_t) && !(out_t = norm(out_t)))) goto fail;
    m_out[m] = out_t; m_raw_s[m] = mp->space; m_mark[m] = pmk; m_has_sp[m] = psp != 0;
    if (psp) {
      Term sp_t = inst(psp, S, false);
      if (!sp_t || N[sp_t].vm || (!clean && has_meta(sp_t) && !(sp_t = norm(sp_t)))) goto fail;
      m_sp[m] = sp_t;
    } else {
      m_sp[m] = (r->birth_law || enforce_reach || pmk) ? tc_space_term(mp->space) : 0;
    }
  }
  if (r->birth_law) {
    /* Births.fresh & Births.single */
    for (int m = 0; m < nmake; m++) if (m_mark[m]) {
      if (tc_space_born(m_sp[m])) goto fail;
      for (int m2 = m + 1; m2 < nmake; m2++) if (m_mark[m2] && m_sp[m] == m_sp[m2]) goto fail;
    }
    /* Births.located: every take, keep, and make lies in born(present) or a newly born space of this firing */
    for (int i = 0; i < r->ntake; i++) {
      Term sp = norm(tc_occ_space(take[i]));
      bool loc = tc_space_born(sp);
      for (int m = 0; !loc && m < nmake; m++) if (m_mark[m] && m_sp[m] == sp) loc = true;
      if (!loc) goto fail;
    }
    for (int i = 0; i < k->nkeep; i++) {
      Term sp = norm(tc_occ_space(keep[i]));
      bool loc = tc_space_born(sp);
      for (int m = 0; !loc && m < nmake; m++) if (m_mark[m] && m_sp[m] == sp) loc = true;
      if (!loc) goto fail;
    }
    for (int j = 0; j < nmake; j++) {
      Term sp = m_sp[j];
      bool loc = tc_space_born(sp);
      for (int m = 0; !loc && m < nmake; m++) if (m_mark[m] && m_sp[m] == sp) loc = true;
      if (!loc) goto fail;
    }
  }
  if (enforce_reach) {
    for (int j = 0; j < nmake; j++) {
      bool ok_r = in_term_set(m_sp[j], reach_set, nreach);
      for (int m = 0; !ok_r && m < nmake; m++) if (m_mark[m] && m_sp[m] == m_sp[j]) ok_r = true;
      if (!ok_r) goto fail;
    }
  }
  Occ o = (m_has_sp[0] || m_mark[0]) ? post_at_internal(m_sp[0], m_out[0], m_mark[0]) : post(m_raw_s[0], m_out[0]);
  if (!o) goto fail;
  memset(last_extra_occ, 0, sizeof last_extra_occ);
  for (int m = 1; m < nmake; m++) {
    Occ oe = (m_has_sp[m] || m_mark[m]) ? post_at_internal(m_sp[m], m_out[m], m_mark[m]) : post(m_raw_s[m], m_out[m]);
    if (!oe) { Wa[o] = 0; Wtag[o] = 0; for (int j = 1; j < m; j++) { Wa[last_extra_occ[j - 1]] = 0; Wtag[last_extra_occ[j - 1]] = 0; } goto fail; }
    last_extra_occ[m - 1] = oe;
  }
  for (int i = 0; i < r->ntake; i++) { Wa[take[i]] = 0; Wtag[take[i]] = 0; }
  return o;
fail:
  undo(mark); nne = nemark; next_name = nmark; nmeta = mmark;
  return 0;
}

Occ tc_fire(int rid, const Occ *take, const Occ *keep, const Term *in) {
  return fire_ex(rid, take, keep, in, NULL, 0, false);
}
Occ tc_fire_reach(int rid, const Occ *take, const Occ *keep, const Term *in,
                  const Term *seeds, int nseed) {
  return fire_ex(rid, take, keep, in, seeds, nseed, true);
}
static Occ search_reach_rec(int rid, const Rule *r, int nkeep, const Occ *cand, int ncand,
                            Occ *take_sel, Occ *keep_sel, int idx, const Term *seeds, int nseed) {
  int total = r->ntake + nkeep;
  if (idx == total)
    return tc_fire_reach(rid, r->ntake ? take_sel : NULL, nkeep ? keep_sel : NULL, NULL, seeds, nseed);
  for (int c = 0; c < ncand; c++) {
    Occ o = cand[c];
    bool dup = false;
    for (int j = 0; j < (idx < r->ntake ? idx : r->ntake); j++) if (take_sel[j] == o) { dup = true; break; }
    if (dup) continue;
    if (idx < r->ntake) take_sel[idx] = o;
    else keep_sel[idx - r->ntake] = o;
    Occ got = search_reach_rec(rid, r, nkeep, cand, ncand, take_sel, keep_sel, idx + 1, seeds, nseed);
    if (got) return got;
  }
  return 0;
}
Occ tc_search_reach(int rid, const Term *seeds, int nseed) {
  if (rid < 0 || rid >= nr) return 0;
  RuleK *k = &R[rid];
  const Rule *r = RULE(k);
  Term reach_set[512];
  int nreach = tc_reach(seeds, nseed, reach_set, 512);
  Occ cand[1024]; int ncand = 0;
  for (Occ o = Wlive; o && ncand < 1024; o = Wnext[o])
    if (Wa[o] && !Wmark[o] && in_term_set(tc_occ_space(o), reach_set, nreach))
      cand[ncand++] = o;
  Occ take_sel[4] = {0}, keep_sel[TC_HYPS] = {0};
  return search_reach_rec(rid, r, k->nkeep, cand, ncand, take_sel, keep_sel, 0, seeds, nseed);
}

Occ tc_convert(Occ p, const Conv *c, Term target) {
  nsteps++;
  Term pt = tc_term(p);
  if (!tc_alive(p) || !pt || !target || target >= nn || N[target].vm || !name_ok(target)
      || has_meta(pt) || has_meta(target) || !(conv(c, pt, target, 0) || conv(c, target, pt, 0))) return 0;
  return Wsp[p] ? post_at_internal(Wsp[p], target, Wmark[p]) : post(Ws[p], target);
}

/* ---- SHARE: a proof script checked once in its context, then one rule ---- */
static inline bool lemma_term(Term t, uint64_t ctx) {
  return ctx_ok(t) && !(N[t].flags & (F_META | F_BV)) && !(N[t].vm & ~ctx);
}
/* A lemma is checked step by step as its proof arrives: tc_lemma opens it over the first nb
   variables of the context, each step is checked against earlier ones and the hypotheses, and
   tc_lemma_end installs the conclusion of one of them as a rule. */
static Term *lres, lhyp[TC_HYPS]; static uint8_t *lsp; static uint32_t nlres, lcap, lmark;
static int lnb, nlhyp; static uint8_t lspace;
bool tc_lemma(int nb, uint8_t space) {
  lok = nb >= 0 && nb <= cn; lnb = nb; lspace = space; nlres = 0; nlhyp = 0; lmark = ntrail;
  return lok;
}
bool tc_lemma_hyp(Term h) {                               /* hypothesis k is referred to as -1-k */
  if (!lok || nlhyp >= TC_HYPS || !lemma_term(h, mask(lnb)) || !(sorts[N[h].sort] & SORT_PROVABLE)) return lok = false;
  lhyp[nlhyp++] = h;
  return true;
}
Term tc_lemma_term(int ref) { return !lok ? 0 : ref >= 0 ? (ref < (int)nlres ? lres[ref] : 0) : (-1 - ref < nlhyp ? lhyp[-1 - ref] : 0); }
static bool lemma_step(const Step *s) {
  static Term S[TC_VARS];
  uint64_t ctx = mask(cn);
  nsteps++;
  Term out; uint8_t space;
  if (__builtin_expect(s->kind == ST_CONV, 0)) {
    int q = s->prem[0];
    if (q >= (int)nlres || q < -nlhyp) return false;
    Term pt = q >= 0 ? lres[q] : lhyp[-1 - q];
    space = q >= 0 ? lsp[q] : lspace;
    if (!lemma_term(s->target, ctx) || !name_ok(s->target)
        || !(conv(s->conv, pt, s->target, 0) || conv(s->conv, s->target, pt, 0))) return false;
    out = s->target;
  } else {
    if ((unsigned)s->rule >= (unsigned)nr) return false;
    RuleK *k = &R[s->rule];
    if (!k->pure) return false;
    if (__builtin_expect(!k->prepped, 0)) prep_rule(k);
    if (s->inst) for (int h = 0; h < k->n; h++) S[h] = s->inst[h];
    else for (int h = 0; h < k->n; h++) S[h] = 0;
    int np = k->nkeep, sp = 0;
    if (s->target) {
      if (!lemma_term(s->target, ctx) || !name_ok(s->target)) return false;
      run_st[sp++] = s->target;
    }
    if (__builtin_expect(k->ks_zero, 1)) {
      for (int j = np - 1; j >= 0; j--) {
        int q = s->prem[j];
        if (q >= (int)nlres || q < -nlhyp || (q >= 0 ? lsp[q] : lspace)) return false;
        run_st[sp++] = q >= 0 ? lres[q] : lhyp[-1 - q];
      }
    } else {
      const Rule *r = RULE(k);
      for (int j = np - 1; j >= 0; j--) {
        int q = s->prem[j];
        if (q >= (int)nlres || q < -nlhyp || (q >= 0 ? lsp[q] : lspace) != r->keep[j].space) return false;
        run_st[sp++] = q >= 0 ? lres[q] : lhyp[-1 - q];
      }
    }
    uint64_t rem = mask(k->n) & ~(s->target ? k->mimplied : k->implied);
    if (__builtin_expect(k->mcode != UINT32_MAX, 1)) {
      if (!run_stack(k->kcode, sp, S, true)) return false;
    } else {
      rem = mask(k->n);
      for (int h = 0; h < k->n; h++) if (S[h] && !lemma_term(S[h], ctx)) return false;
      const Rule *r = RULE(k);
      for (int j = 0; j < np; j++) if (!umatch(r->keep[j].t, run_st[sp - 1 - j], S)) return false;
      if (s->target && !umatch(k->make, s->target, S)) return false;
    }
    if (__builtin_expect(rem != 0, 0)) {
      for (uint64_t m = rem; m; m &= m - 1) {
        int h = __builtin_ctzll(m);
        Term t = S[h];
        if (!t) continue;
        if (!lemma_term(t, ctx) || (HOLE(k, h).sort != TC_ANY && N[t].sort != HOLE(k, h).sort) || (HOLE(k, h).bound && !is_bvar(t))) return false;
      }
    }
    if (k->bounds) {
      for (uint64_t m = k->bounds; m; m &= m - 1) {
        int h = __builtin_ctzll(m);
        for (uint64_t a = S[h] ? HOLE(k, h).avoid : 0; a; a &= a - 1) {
          int j = __builtin_ctzll(a);
          if (S[j] && (N[S[h]].bm & N[S[j]].bm)) return false;
        }
      }
    }
    if (s->target) out = s->target;
    else if (!(out = inst(k->make, S, false)) || (N[out].vm & ~ctx) || has_meta(out)) return false;
    space = k->mspace;
  }
  if (nlres >= lcap) {
    uint32_t m = lcap ? 2 * lcap : 1024;
    Term *a = realloc(lres, m * sizeof *a); if (!a) return false; lres = a;
    uint8_t *b = realloc(lsp, m); if (!b) return false; lsp = b;
    lcap = m;
  }
  lres[nlres] = out; lsp[nlres++] = space;
  return true;
}
int tc_lemma_step(const Step *s) {                        /* the new step's index, or -1 */
  if (!lok || !s || !lemma_step(s)) { lok = false; undo(lmark); return -1; }
  return (int)nlres - 1;
}
int tc_lemma_end(int ref) {                               /* install the conclusion of ref as a rule */
  Term concl = tc_lemma_term(ref);
  uint8_t space = ref >= 0 ? lsp[ref] : lspace;
  bool ok = lok && concl && space == lspace && lemma_term(concl, mask(lnb)) && (sorts[N[concl].sort] & SORT_PROVABLE);
  for (int i = lnb; ok && i < cn; i++) ok = cbound[i] && !(sorts[csort[i]] & (SORT_STRICT | SORT_FREE));   /* dummies */
  lok = false;
  if (!ok) { tscope = bscope = false; return -1; }
  Rule L = { .nkeep = (uint8_t)nlhyp, .make = { concl, lspace }, .fresh = -1 };
  if (bscope) {
    for (int i = 0; i < nlhyp; i++) L.keep[i] = (Pat){ lhyp[i], lspace };
    int rid = add_rule(&L, lnb);
    if (rid >= 0) prep_rule(&R[rid]);
    release(NULL, 0);
    return rid;
  }
  Term *ts[TC_HYPS + 1] = { [0] = &L.make.t };
  for (int i = 0; i < nlhyp; i++) { L.keep[i] = (Pat){ lhyp[i], lspace }; ts[i + 1] = &L.keep[i].t; }
  release(ts, nlhyp + 1);
  return add_rule(&L, lnb);
}
int tc_promote(int nb, uint8_t space, int nhyp, const Term *hyps, Term concl, const Step *st, int ns) {
  if (nhyp < 0 || nhyp > TC_HYPS || ns <= 0 || (nhyp > 0 && !hyps) || !st || !tc_lemma(nb, space)) return -1;
  for (int i = 0; i < nhyp; i++) if (!tc_lemma_hyp(hyps[i])) return -1;
  for (int i = 0; i < ns; i++) if (tc_lemma_step(&st[i]) < 0) return -1;
  if (tc_lemma_term(ns - 1) != concl) { lok = false; return -1; }
  return tc_lemma_end(ns - 1);
}

/* ---- Row 6: ProgramReflection & ProgramBindersQuoted ---- */
void tc_set_quote_con(int quote_con, int activate_con, int lam_con, int app_con) {
  q_quote_con = quote_con; q_act_con = activate_con; q_lam_con = lam_con; q_app_con = app_con;
}
static Term subst_bv(Term body, Term bv, Term val, int d) {
  if (!body || body >= nn || d > 4096) return 0;
  if (body == bv) return val;
  if (N[body].kind != K_APP) return body;
  if ((int)N[body].head == q_lam_con && N[body].arity == 2 && argv(body)[0] == bv) return body;
  Term b[TC_ARGS]; bool chg = false;
  int ar = N[body].arity;
  for (int i = 0; i < ar; i++) {
    Term ai = argv(body)[i];
    if ((int)N[body].head == q_lam_con && i == 0) b[i] = ai;
    else {
      b[i] = subst_bv(ai, bv, val, d + 1);
      if (!b[i]) return 0;
      chg |= (b[i] != ai);
    }
  }
  return chg ? tc_app((int)N[body].head, b) : body;
}
Term tc_active_step(Term t) {
  if (!t || t >= nn) return 0;
  t = norm(t);
  if (!t || N[t].kind != K_APP || (int)N[t].head == q_quote_con) return 0;  /* quote is inert */
  int hd = (int)N[t].head, ar = N[t].arity;
  if (hd == q_app_con && ar == 2) {
    Term f = argv(t)[0], a = argv(t)[1];
    if (N[f].kind == K_APP && (int)N[f].head == q_lam_con && N[f].arity == 2)
      return subst_bv(argv(f)[1], argv(f)[0], a, 0);
    Term sf = tc_active_step(f);
    if (sf) return tc_app(q_app_con, (Term[2]){ sf, a });
    Term sa = tc_active_step(a);
    if (sa) return tc_app(q_app_con, (Term[2]){ f, sa });
    return 0;
  }
  if (hd == q_act_con && ar == 1) {
    Term c = argv(t)[0];
    if (N[c].kind == K_APP && (int)N[c].head == q_quote_con && N[c].arity == 1)
      return argv(c)[0];                                                     /* one layer of quotation removed */
    Term sc = tc_active_step(c);
    if (sc) return tc_app(q_act_con, &sc);
    return 0;
  }
  if (hd == q_lam_con && ar == 2) {
    Term x = argv(t)[0], body = argv(t)[1];
    Term sb = tc_active_step(body);
    if (sb) return tc_app(q_lam_con, (Term[2]){ x, sb });
    return 0;
  }
  return 0;
}
Term tc_active_norm(Term t, int max_steps) {
  if (!t || t >= nn || max_steps < 0) return 0;
  t = norm(t);
  for (int i = 0; i < max_steps; i++) {
    Term nxt = tc_active_step(t);
    if (!nxt) return t;
    t = nxt;
  }
  return tc_active_step(t) ? 0 : t;
}
Occ tc_active_step_occ(Occ o) {
  if (!tc_alive(o)) return 0;
  Term nxt = tc_active_step(tc_term(o));
  if (!nxt) return 0;
  nsteps++;
  return Wsp[o] ? post_at_internal(Wsp[o], nxt, Wmark[o]) : post(Ws[o], nxt);
}

/* ---- Row 7: RhoContinuation & ContextualCommunicationReflection ---- */
void tc_set_rho_con(int quote_con, int drop_con, bool allow_proc_drop) {
  rho_quote_con = quote_con; rho_drop_con = drop_con; rho_allow_drop = allow_proc_drop;
}
static Term rho_norm_rec(Term t, int d) {
  if (!t || t >= nn || d > 4096) return 0;
  t = norm(t);
  if (!t || N[t].kind != K_APP) return t;
  int hd = (int)N[t].head, ar = N[t].arity;
  Term b[TC_ARGS];
  for (int i = 0; i < ar; i++) {
    b[i] = rho_norm_rec(argv(t)[i], d + 1);
    if (!b[i]) return 0;
  }
  if (hd == rho_quote_con && ar == 1 && N[b[0]].kind == K_APP && (int)N[b[0]].head == rho_drop_con && N[b[0]].arity == 1)
    return argv(b[0])[0];                                                    /* Name-sort law: quote(drop(n)) = n */
  return tc_app(hd, ar ? b : NULL);
}
Term tc_rho_norm_name(Term t) { return rho_norm_rec(t, 0); }
Occ tc_rho_step_occ(Occ o) {
  if (!rho_allow_drop || !tc_alive(o)) return 0;
  Term t = norm(tc_term(o));
  if (!t || N[t].kind != K_APP || (int)N[t].head != rho_drop_con || N[t].arity != 1) return 0;
  Term inner = argv(t)[0];
  if (N[inner].kind != K_APP || (int)N[inner].head != rho_quote_con || N[inner].arity != 1) return 0;
  Term proc = argv(inner)[0];
  nsteps++;
  return Wsp[o] ? post_at_internal(Wsp[o], proc, Wmark[o]) : post(Ws[o], proc);
}
Term tc_rho_comm(Term ch_out, Term ch_in, Term payload_proc,
                 Term cont_pat, int var_name, int var_proc) {
  if (rho_quote_con < 0 || !ch_out || !ch_in || !payload_proc || !cont_pat) return 0;
  Term no = tc_rho_norm_name(ch_out), ni = tc_rho_norm_name(ch_in);
  if (!no || !ni || no != ni) return 0;
  Term q_pay = tc_app(rho_quote_con, &payload_proc);
  if (!q_pay) return 0;
  Term S[TC_VARS] = {0};
  if (var_name >= 0 && var_name < TC_VARS) S[var_name] = q_pay;
  if (var_proc >= 0 && var_proc < TC_VARS) S[var_proc] = payload_proc;
  return inst(cont_pat, S, false);
}

/* ---- Modular Prepared-Step & Cursor Interface (CeTTa <-> tcalc Bridge) ---- */
bool tc_commit_prepared(const TcPreparedStep *step, TcAdmissionReceipt *receipt) {
  if (receipt) memset(receipt, 0, sizeof(*receipt));
  if (!step || step->rule < 0 || step->rule >= nr) return false;
  Occ out = 0;
  if (step->dest && (tc_rule_fibre(step->rule) & FIBRE_FLAT) && !step->take && step->nseeds <= 0) {
    out = tc_flat_fire(step->rule, step->keep, step->inst, step->dest);
  } else if (step->nseeds > 0) {
    out = tc_fire_reach(step->rule, step->take, step->keep, step->inst, step->seeds, step->nseeds);
  } else {
    out = tc_fire(step->rule, step->take, step->keep, step->inst);
  }
  if (!out) return false;
  if (receipt) {
    receipt->admitted = true;
    receipt->rule = step->rule;
    receipt->out = out;
    receipt->out_term = Wt[out];
    for (int i = 0; i < 4; i++) {
      if (last_extra_occ[i]) {
        receipt->extra[receipt->nextra++] = last_extra_occ[i];
      }
    }
  }
  return true;
}

int tc_step_cursor(TcCandidateCursor *cursor, TcAdmissionReceipt *receipt) {
  if (receipt) memset(receipt, 0, sizeof(*receipt));
  if (!cursor || !cursor->next) return -1;
  TcPreparedStep cand;
  while (cursor->next(cursor->ctx, &cand)) {
    if (tc_commit_prepared(&cand, receipt)) return 1;
  }
  return 0;
}

