/* MM0 on tcalc: reads a .mmu proof file and drives the kernel.
   sort -> tc_sort, term -> tc_con, def -> tc_def, axiom -> tc_rule, theorem -> tc_promote.
   Proof expressions become kernel steps: assertion applications are rule steps with their
   substitutions, :conv is a conversion step, :let names a step. This reader is not trusted
   for derivability (the kernel checks every step); it also verifies public declarations
   against a required .mm0 specification (unless --proof-only is explicitly passed). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "tcalc.h"
#include "mm0_spec.h"

static double now_ms(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec * 1e3 + ts.tv_nsec * 1e-6; }

/* ---- s-expressions ---- */
typedef struct { int sym, kid, next; } SX;          /* sym >= 0: atom; sym < 0: list with first child kid */
static SX *X; static int nx, xcap;
static char **syms; static int *symlen; static int nsym, symcap; static int *symh; static int symhmask;
static int S_LOCAL, S_SORT, S_TERM, S_DEF, S_AXIOM, S_THM, S_INPUT, S_OUTPUT, S_LET, S_CONV, S_SYM, S_UNFOLD;

static int intern(const char *s, int len) {
  unsigned h = 2166136261u;
  for (int i = 0; i < len; i++) h = (h ^ (unsigned char)s[i]) * 16777619u;
  for (int i = h & symhmask;; i = (i + 1) & symhmask) {
    int k = symh[i];
    if (k < 0) {
      if (nsym >= symcap) { symcap *= 2; syms = realloc(syms, symcap * sizeof *syms); symlen = realloc(symlen, symcap * sizeof *symlen); }
      syms[nsym] = strndup(s, len); symlen[nsym] = len; symh[i] = nsym; return nsym++;
    }
    if (symlen[k] == len && !memcmp(syms[k], s, len)) return k;
  }
}
static int sx(int sym, int kid) {
  if (nx >= xcap) { xcap *= 2; X = realloc(X, xcap * sizeof *X); }
  X[nx] = (SX){ sym, kid, -1 }; return nx++;
}
static const char *src; static size_t pos, len;
static void skip(void) {                             /* whitespace is space and newline only */
  for (;;) {
    while (pos < len && (src[pos] == ' ' || src[pos] == '\n')) pos++;
    if (pos + 1 < len && src[pos] == '-' && src[pos + 1] == '-') { while (pos < len && src[pos] != '\n') pos++; continue; }
    return;
  }
}
static int parse(void) {                             /* -1 on end or error */
  skip();
  if (pos >= len) return -1;
  if (src[pos] == '(') {
    pos++;
    int l = sx(-1, -1), last = -1;
    for (;;) {
      skip();
      if (pos >= len) return -1;
      if (src[pos] == ')') { pos++; return l; }
      int c = parse();
      if (c < 0) return -1;
      if (last < 0) X[l].kid = c; else X[last].next = c;
      last = c;
    }
  }
  size_t s = pos;
  while (pos < len && (src[pos] == '_' || src[pos] == ':' || (src[pos] >= '0' && src[pos] <= '9')
         || (src[pos] >= 'a' && src[pos] <= 'z') || (src[pos] >= 'A' && src[pos] <= 'Z'))) pos++;
  if (pos == s) return -1;
  return sx(intern(src + s, (int)(pos - s)), -1);
}
static int nth(int l, int n) { if (l < 0 || X[l].sym >= 0) return -1; int c = X[l].kid; while (c >= 0 && n--) c = X[c].next; return c; }
static int count(int l) { if (l < 0 || X[l].sym >= 0) return -1; int n = 0; for (int c = X[l].kid; c >= 0; c = X[c].next) n++; return n; }
static bool atom(int x) { return x >= 0 && X[x].sym >= 0; }
static bool is(int x, const char *s) { return atom(x) && !strcmp(syms[X[x].sym], s); }
static bool is_sym(int x, int s) { return x >= 0 && X[x].sym == s; }

/* ---- environment ---- */
typedef struct { int sort, con, rule, nb, nh, var, ref; } Sym; /* var/ref: per statement, 1-based */
static Sym *E; static int ecap;
static Sym *env(int sym) {
  if (sym >= ecap) { int n = ecap; while (n <= sym) n *= 2; E = realloc(E, n * sizeof *E); memset(E + ecap, 0, (n - ecap) * sizeof *E); ecap = n; }
  return &E[sym];
}
static const char *where; static long thms, axioms, defs, terms;
static uint8_t sort_flags[256];
static void die(const char *msg) { fprintf(stderr, "FAIL at %s: %s\n", where ? where : "?", msg); exit(1); }

/* binders: list of (x s) or (x s (deps)); fills Binder[] and sets per-statement var indices */
static int vars_used[TC_VARS], nvars;
static void clear_vars(void) { for (int i = 0; i < nvars; i++) env(vars_used[i])->var = 0; nvars = 0; }
static int binders(int l, Binder *b, int base) {
  if (l < 0 || X[l].sym >= 0) die("bad binder list");
  int n = base;
  for (int c = X[l].kid; c >= 0; c = X[c].next, n++) {
    if (n >= TC_VARS) die("too many variables");
    int name = nth(c, 0), s = nth(c, 1), d = nth(c, 2);
    if (!atom(name) || !atom(s) || !env(X[s].sym)->sort || (d >= 0 && X[d].sym >= 0)) die("bad binder");
    b[n] = (Binder){ (uint16_t)env(X[s].sym)->sort, d < 0, 0 };
    for (int v = d >= 0 ? X[d].kid : -1; v >= 0; v = X[v].next) {
      int k = atom(v) ? env(X[v].sym)->var : 0;
      if (!k) die("unknown dependency");
      b[n].deps |= 1ull << (k - 1);
    }
    if (!is(name, "_")) {
      if (env(X[name].sym)->var) die("duplicate variable");
      env(X[name].sym)->var = n + 1; vars_used[nvars++] = X[name].sym;
    }
  }
  return n;
}
static uint64_t deplist(int l) {
  if (l < 0 || X[l].sym >= 0) die("bad dependency list");
  uint64_t m = 0;
  for (int v = X[l].kid; v >= 0; v = X[v].next) {
    int k = atom(v) ? env(X[v].sym)->var : 0;
    if (!k) die("unknown dependency");
    m |= 1ull << (k - 1);
  }
  return m;
}
static int def_nb, d_ndum;
static uint64_t def_dum_seen;
static Term d_terms[TC_VARS];
static uint16_t d_sorts[TC_VARS];
static const Binder *def_b;
static Term expr(int x) {
  if (x < 0) die("missing expression");
  if (atom(x)) {
    int k = env(X[x].sym)->var;
    if (!k) die("unknown variable");
    if (def_b && k - 1 >= def_nb && !(def_dum_seen & (1ull << (k - 1)))) {
      def_dum_seen |= 1ull << (k - 1);
      d_terms[d_ndum] = tc_v(k - 1);
      d_sorts[d_ndum] = def_b[k - 1].sort;
      d_ndum++;
    }
    return tc_v(k - 1);
  }
  int h = nth(x, 0);
  if (!atom(h) || !env(X[h].sym)->con) die("unknown term");
  Term a[TC_ARGS]; int n = 0;
  for (int c = X[h].next; c >= 0; c = X[c].next) { if (n >= TC_ARGS) die("arity"); a[n++] = expr(c); }
  Term t = tc_app(env(X[h].sym)->con - 1, a);
  if (!t) die("ill-formed expression");
  return t;
}

/* ---- proofs ---- */
static Step *st; static int nst, stcap;
static void *arena; static size_t used, acap;
static void *alloc(size_t n) {
  n = (n + 15) & ~(size_t)15;
  if (used + n > acap) die("proof arena exhausted");
  void *p = (char *)arena + used; used += n; memset(p, 0, n); return p;
}
static int let_used[4096], nlet;
static Conv *conv_of(int x, Conv *c);
static Conv *conv_new(int x) { return conv_of(x, alloc(sizeof(Conv))); }
static Conv *conv_of(int x, Conv *c) {
  if (x < 0) die("missing conversion");
  if (atom(x)) { c->kind = CV_REFL; c->t = expr(x); return c; }
  int h = nth(x, 0);
  if (is_sym(h, S_SYM)) { c->kind = CV_SYM; c->kid = conv_new(nth(x, 1)); return c; }
  if (is_sym(h, S_UNFOLD)) {
    int t = nth(x, 1), es = nth(x, 2), ds = nth(x, 3);
    if (!atom(t) || !env(X[t].sym)->con || es < 0 || X[es].sym >= 0 || ds < 0 || X[ds].sym >= 0) die("unfold of unknown term");
    c->kind = CV_UNFOLD; c->con = env(X[t].sym)->con - 1;
    Term *a = alloc(TC_ARGS * sizeof *a), *d = alloc(TC_VARS * sizeof *d);
    int n = 0; for (int e = X[es].kid; e >= 0; e = X[e].next) { if (n >= TC_ARGS) die("arity"); a[n++] = expr(e); }
    n = 0; for (int e = X[ds].kid; e >= 0; e = X[e].next) { if (n >= TC_VARS) die("dummies"); d[n++] = expr(e); }
    c->args = a; c->dummies = d; c->kid = conv_new(nth(x, 4));
    return c;
  }
  if (!atom(h) || !env(X[h].sym)->con) die("conversion over unknown term");
  c->kind = CV_CONG; c->con = env(X[h].sym)->con - 1; c->n = count(x) - 1;
  Conv *k = alloc((size_t)(c->n ? c->n : 1) * sizeof *k);
  int i = 0; for (int e = X[h].next; e >= 0; e = X[e].next) conv_of(e, &k[i++]);
  c->kid = k;
  return c;
}
static int push(Step s) {
  if (nst >= stcap) { stcap *= 2; st = realloc(st, stcap * sizeof *st); }
  st[nst] = s; return nst++;
}
static int proof(int x) {                            /* returns a step index, or -1-k for hypothesis k */
  if (x < 0) die("missing proof");
  if (atom(x)) { int r = env(X[x].sym)->ref; if (!r) die("unknown hypothesis"); return r > 0 ? r - 1 : r; }
  int h = nth(x, 0);
  if (is_sym(h, S_LET)) {
    int name = nth(x, 1), r = proof(nth(x, 2));
    if (!atom(name)) die("bad let name");
    Sym *e = env(X[name].sym); int old = e->ref;
    e->ref = r >= 0 ? r + 1 : r;
    if (nlet < 4096) let_used[nlet++] = X[name].sym;
    int out = proof(nth(x, 3));
    e->ref = old;
    return out;
  }
  if (is_sym(h, S_CONV)) {
    Step s = { .kind = ST_CONV };
    s.target = expr(nth(x, 1)); s.conv = conv_new(nth(x, 2)); s.prem[0] = proof(nth(x, 3));
    return push(s);
  }
  if (!atom(h) || !env(X[h].sym)->rule) die("unknown assertion");
  Sym *a = env(X[h].sym);
  Step s = { .kind = ST_RULE, .rule = a->rule - 1 };
  int es = nth(x, 1);
  if (es < 0 || X[es].sym >= 0 || count(es) != a->nb) die("wrong number of substitutions");
  Term *in = alloc(TC_VARS * sizeof *in);
  int i = 0; for (int e = X[es].kid; e >= 0; e = X[e].next) in[i++] = expr(e);
  s.inst = in;
  i = 0; for (int p = X[es].next; p >= 0; p = X[p].next) { if (i >= TC_HYPS) die("too many hypotheses"); s.prem[i++] = proof(p); }
  if (i != a->nh) die("wrong number of hypotheses");
  return push(s);
}

static bool ident(int x) {                           /* [a-zA-Z_][a-zA-Z0-9_]*, not "_" */
  if (!atom(x)) return false;
  const char *s = syms[X[x].sym];
  if ((s[0] >= '0' && s[0] <= '9') || !strcmp(s, "_")) return false;
  for (; *s; s++) if (*s == ':') return false;
  return true;
}

static void directive(int d) {
  if (d < 0 || X[d].sym >= 0) die("bad directive");
  int k = nth(d, 0), off = is_sym(k, S_LOCAL);
  if (off) {
    k = nth(d, 1);
    if (!is_sym(k, S_DEF) && !is_sym(k, S_THM)) die("local only on def or theorem");
  }
  int name = nth(d, 1 + off);
  where = atom(name) ? syms[X[name].sym] : "?";
  if (!ident(name)) die("bad identifier");
  Binder b[TC_VARS];
  if (is_sym(k, S_SORT)) {
    if (env(X[name].sym)->sort) die("duplicate sort");
    uint8_t f = 0; int last = -1;                    /* modifiers: pure strict provable free, in order */
    static const char *mods[4] = { "pure", "strict", "provable", "free" };
    for (int c = X[name].next; c >= 0; c = X[c].next) {
      int m = 0; while (m < 4 && !is(c, mods[m])) m++;
      if (m == 4 || m <= last) die("bad sort modifier");
      last = m; f |= (uint8_t)(1u << m);
    }
    f = (uint8_t)((f & 1 ? SORT_PURE : 0) | (f & 2 ? SORT_STRICT : 0) | (f & 4 ? SORT_PROVABLE : 0) | (f & 8 ? SORT_FREE : 0));
    int s = tc_sort(f);
    if (s < 0) die("sort");
    env(X[name].sym)->sort = s; sort_flags[s] = f;
    if (!off) sp_check_sort(f);
  } else if (is_sym(k, S_TERM) || is_sym(k, S_DEF)) {
    if (env(X[name].sym)->con) die("duplicate term");
    bool def = is_sym(k, S_DEF);
    int nb = binders(nth(d, 2 + off), b, 0), ret = nth(d, 3 + off);
    int rs = atom(nth(ret, 0)) ? env(X[nth(ret, 0)].sym)->sort : 0;
    if (!rs) die("bad return sort");
    uint64_t rd = deplist(nth(ret, 1));
    int id, nd = nb;
    Term body = 0;
    if (def) {
      nd = binders(nth(d, 4 + off), b, nb);
      for (int i = nb; i < nd; i++) if (!b[i].bound) die("dummy must be bound");
      if (!tc_ctx(nd, b)) die("bad context");
      def_nb = nb; def_dum_seen = 0; d_ndum = 0; def_b = b;
      body = expr(nth(d, 5 + off));
      def_b = NULL;
      id = tc_def((uint16_t)rs, rd, nb, nd - nb, body);
      defs++;
    } else {
      id = tc_con((uint16_t)rs, rd, nb, b);
      terms++;
    }
    if (id < 0) die(def ? "definition refused" : "term refused");
    env(X[name].sym)->con = id + 1;
    if (!off) sp_check_term_or_def(def, (uint32_t)(terms + defs - 1), id, (uint16_t)nb, b, (uint16_t)rs, rd, body, d_ndum, d_terms, d_sorts);
  } else if (is_sym(k, S_AXIOM)) {
    if (env(X[name].sym)->rule) die("duplicate assertion");
    int nb = binders(nth(d, 2 + off), b, 0), hl = nth(d, 3 + off);
    if (hl < 0 || X[hl].sym >= 0 || !tc_ctx(nb, b)) die("bad context");
    tc_transient();                                    /* the kernel call below releases this statement's terms */
    Rule r = { .fresh = -1 };
    Term a_hyps[TC_HYPS];
    for (int c = X[hl].kid; c >= 0; c = X[c].next) {
      if (r.nkeep >= TC_HYPS) die("too many hypotheses");
      a_hyps[r.nkeep] = expr(c);
      r.keep[r.nkeep] = (Pat){ a_hyps[r.nkeep], 0 };
      r.nkeep++;
    }
    r.make = (Pat){ expr(nth(d, 4 + off)), 0 };
    for (int i = 0; i <= r.nkeep; i++)                 /* axiom statements have provable sorts */
      if (!(sort_flags[tc_sort_of(i < r.nkeep ? r.keep[i].t : r.make.t)] & SORT_PROVABLE)) die("statement of unprovable sort");
    if (!off) sp_check_ax_or_thm(false, (uint32_t)(axioms + thms), (uint16_t)nb, b, r.nkeep, a_hyps, r.make.t);
    int id = tc_rule(&r);
    if (id < 0) die("axiom refused");
    env(X[name].sym)->rule = id + 1; env(X[name].sym)->nb = nb; env(X[name].sym)->nh = r.nkeep; axioms++;
  } else if (is_sym(k, S_THM)) {
    if (env(X[name].sym)->rule) die("duplicate assertion");
    int nb = binders(nth(d, 2 + off), b, 0), hl = nth(d, 3 + off);
    int nd = binders(nth(d, 5 + off), b, nb);
    for (int i = nb; i < nd; i++) if (!b[i].bound) die("dummy must be bound");
    if (hl < 0 || X[hl].sym >= 0 || !tc_ctx(nd, b)) die("bad context");
    tc_transient();
    Term hyps[TC_HYPS]; int nh = 0, hs[TC_HYPS];
    for (int c = X[hl].kid; c >= 0; c = X[c].next) {
      if (nh >= TC_HYPS) die("too many hypotheses");
      int hn = nth(c, 0);
      if (!atom(hn)) die("bad hypothesis name");
      hyps[nh] = expr(nth(c, 1));
      if (!is(hn, "_")) {
        if (env(X[hn].sym)->ref) die("duplicate hypothesis name");
        hs[nh] = X[hn].sym; env(hs[nh])->ref = -1 - nh;
      } else hs[nh] = 0;
      nh++;
    }
    Term concl = expr(nth(d, 4 + off));
    used = 0; nst = 0; nlet = 0;
    int root = proof(nth(d, 6 + off));
    if (nst == 0 || root != nst - 1) {
      Conv *rc = alloc(sizeof(Conv));
      *rc = (Conv){ .kind = CV_REFL, .t = concl };
      push((Step){ .kind = ST_CONV, .prem = { root }, .target = concl, .conv = rc });
    }
    for (int i = 0; i < nh; i++) if (hs[i]) env(hs[i])->ref = 0;
    for (int i = 0; i < nlet; i++) env(let_used[i])->ref = 0;
    if (!off) sp_check_ax_or_thm(true, (uint32_t)(axioms + thms), (uint16_t)nb, b, nh, hyps, concl);
    int id = tc_promote(nb, 0, nh, hyps, concl, st, nst);
    if (id < 0) die("proof refused");
    env(X[name].sym)->rule = id + 1; env(X[name].sym)->nb = nb; env(X[name].sym)->nh = nh; thms++;
  } else if (!is_sym(k, S_INPUT) && !is_sym(k, S_OUTPUT)) die("unknown directive");
  clear_vars();
}

int main(int argc, char **argv) {
  double t_start = now_ms();
  sp_auto_init(argc, argv);
  FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 2; }
  fseek(f, 0, SEEK_END); len = (size_t)ftell(f); fseek(f, 0, SEEK_SET);
  char *buf = malloc(len + 1); if (fread(buf, 1, len, f) != len) return 2; fclose(f); src = buf;
  xcap = 1 << 16; X = malloc(xcap * sizeof *X);
  symcap = 1 << 13; syms = malloc(symcap * sizeof *syms); symlen = malloc(symcap * sizeof *symlen);
  symhmask = (1 << 15) - 1; symh = malloc((symhmask + 1) * sizeof *symh); memset(symh, -1, (symhmask + 1) * sizeof *symh);
  ecap = 1 << 13; E = calloc(ecap, sizeof *E); stcap = 1 << 12; st = malloc(stcap * sizeof *st);
  acap = 4u << 20; arena = malloc(acap);
  if (!tc_init(1u << 12, 1u << 10)) { fprintf(stderr, "init failed\n"); return 2; }
  S_LOCAL = intern("local", 5); S_SORT = intern("sort", 4); S_TERM = intern("term", 4); S_DEF = intern("def", 3);
  S_AXIOM = intern("axiom", 5); S_THM = intern("theorem", 7); S_INPUT = intern("input", 5); S_OUTPUT = intern("output", 6);
  S_LET = intern(":let", 4); S_CONV = intern(":conv", 5); S_SYM = intern(":sym", 4); S_UNFOLD = intern(":unfold", 7);
  for (int d; (d = (nx = 0, parse())) >= 0;) directive(d);
  skip(); if (pos < len) { where = "end"; die("syntax error"); }
  sp_finish();
  double t_total = now_ms() - t_start;
  printf("verified %s: %ld theorems (%llu steps), %ld axioms, %ld definitions, %ld terms%s [total %.2f ms]\n",
         argv[1], thms, (unsigned long long)tc_steps(), axioms, defs, terms,
         sp_proof_only ? " [NOT CHECKED AGAINST A SPEC]" : "", t_total);
  return 0;
}
