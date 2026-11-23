/* MM0 binary (.mmb) verifier on tcalc.
   Drives the same tcalc kernel (tc_sort, tc_con, tc_def, tc_rule, tc_promote)
   directly from the binary MM0B proof stream without S-expression text parsing. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "tcalc.h"
#include "mm0_spec.h"

static double now_ms(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec * 1e3 + ts.tv_nsec * 1e-6; }

enum {
  CMD_END = 0x00, CMD_STMT_AXIOM = 0x02, CMD_STMT_SORT = 0x04, CMD_STMT_DEF = 0x05,
  CMD_STMT_THM = 0x06, CMD_STMT_LOCAL_DEF = 0x0D, CMD_STMT_LOCAL_THM = 0x0E,
  CMD_PROOF_TERM = 0x10, CMD_PROOF_TERM_SAVE = 0x11, CMD_PROOF_REF = 0x12, CMD_PROOF_DUMMY = 0x13,
  CMD_PROOF_THM = 0x14, CMD_PROOF_THM_SAVE = 0x15, CMD_PROOF_HYP = 0x16, CMD_PROOF_CONV = 0x17,
  CMD_PROOF_REFL = 0x18, CMD_PROOF_SYMM = 0x19, CMD_PROOF_CONG = 0x1A, CMD_PROOF_UNFOLD = 0x1B,
  CMD_PROOF_CONV_CUT = 0x1C, CMD_PROOF_CONV_SAVE = 0x1E, CMD_PROOF_SAVE = 0x1F, CMD_PROOF_SORRY = 0x20,
  CMD_UNIFY_TERM = 0x30, CMD_UNIFY_TERM_SAVE = 0x31, CMD_UNIFY_REF = 0x32, CMD_UNIFY_DUMMY = 0x33, CMD_UNIFY_HYP = 0x36,
  SL_EXPR = 0, SL_PROOF = 1, SL_CONV = 2, SL_COCONV = 3
};
#define DEPS_MASK  (((uint64_t)1 << 55) - 1)
#define RSVD_BIT   ((uint64_t)1 << 55)
#define BOUND_BIT  ((uint64_t)1 << 63)
#define TYPE_SORT(ty) (((ty) >> 56) & 0x7Fu)
#define USAVED     (1u << 31)

static const uint8_t *file, *fend; static size_t flen;
static uint32_t num_sorts, num_terms, num_thms, p_terms, p_thms, p_proof;
static uint32_t nsorts, nterms, nthms;
static const uint8_t *sorts;
static int term_con[8192], thm_rule[16384];
static uint8_t term_arity[8192], def_ndum[8192], def_dmap[8192][TC_VARS], thm_nvar[16384], thm_nhyp[16384];

static uint16_t le16(const uint8_t *p) { uint16_t v; memcpy(&v, p, 2); return v; }
static uint32_t le32(const uint8_t *p) { uint32_t v; memcpy(&v, p, 4); return v; }
static uint64_t le64(const uint8_t *p) { uint64_t v; memcpy(&v, p, 8); return v; }
static void die(const char *msg) { fprintf(stderr, "FAIL (sorts=%u terms=%u thms=%u): %s\n", nsorts, nterms, nthms, msg); exit(1); }
#define ENSURE(c, m) do { if (__builtin_expect(!(c), 0)) die(m); } while (0)

typedef struct { uint32_t e1; int32_t e2; uint32_t conv; uint8_t tag; } Slot;
enum { MAX_STACK = 1u << 15, MAX_CONVS = 1u << 14, MAX_TP = 1u << 15 };
static Term se1[MAX_STACK]; static int32_t se2[MAX_STACK]; static uint32_t sconv[MAX_STACK];
static Slot heap[MAX_STACK]; static uint32_t sp, hp;
static uint32_t hyps[64], hstack[64], ustack[MAX_STACK], uheap[MAX_STACK];
static int nhyp, hsp, usp, uhp;
static Conv convs[MAX_CONVS]; static int nconv = 1;
static Term tpool[MAX_TP]; static int ntp;
static Step gst;

static uint32_t alloc_conv(int n) { ENSURE(nconv + n <= MAX_CONVS, "conv arena"); uint32_t c = (uint32_t)nconv; memset(&convs[c], 0, (size_t)n * sizeof(Conv)); nconv += n; return c; }
static Term *alloc_tp(int n) { ENSURE(ntp + n <= MAX_TP, "term pool"); Term *p = &tpool[ntp]; ntp += n; return p; }
static inline void push(Slot s) {
  ENSURE(sp < MAX_STACK, "stack overflow");
  se1[sp] = s.e1 | ((uint32_t)s.tag << 30); se2[sp] = s.e2; sconv[sp] = s.conv; sp++;
}
static inline void push_expr(Term t) {
  ENSURE(sp < MAX_STACK, "stack overflow");
  se1[sp++] = t;
}
static inline void push_h(Slot s) { ENSURE(hp < MAX_STACK, "heap overflow"); heap[hp++] = s; }
static inline Slot pop(uint8_t tag) {
  ENSURE(sp > 0 && (se1[sp - 1] >> 30) == tag, "bad stack slot");
  --sp; return (Slot){ se1[sp] & 0x3FFFFFFFu, se2[sp], sconv[sp], tag };
}
static void realize_proof(Slot *s) {
  if (s->conv) {
    Step st; st.kind = ST_CONV; st.prem[0] = s->e2; st.target = s->e1; st.conv = &convs[s->conv];
    s->e2 = tc_lemma_step(&st);
    ENSURE(s->e2 >= 0, "tc_lemma_step conv");
    s->conv = 0;
  }
}
static Slot pop_proof(void) { Slot s = pop(SL_PROOF); realize_proof(&s); return s; }

static void unpack(const uint8_t *cmd, uint32_t *sz, uint32_t *data) {
  ENSURE((size_t)(fend - cmd) >= 5, "command out of range");
  switch (*cmd & 0xC0) {
    case 0x00: *sz = 1; *data = 0; return;
    case 0x40: *sz = 2; *data = cmd[1]; return;
    case 0x80: *sz = 3; *data = le16(cmd + 1); return;
    default:   *sz = 5; *data = le32(cmd + 1); return;
  }
}
static uint64_t arg_at(uint32_t p_args, size_t i) { return le64(file + p_args + 8 * i); }

static int bpos[64], nbv, next_var;
static void load_binders(uint32_t p_args, uint32_t n, bool has_ret, Binder *b, uint64_t *ret_out) {
  size_t total = (size_t)n + (has_ret ? 1 : 0);
  ENSURE(p_args <= flen && total <= (flen - p_args) / 8 && n <= TC_VARS, "bad args pointer");
  hp = 0; sp = 0; nhyp = 0; hsp = 0; nconv = 1; ntp = 0; nbv = 0;
  for (uint32_t i = 0; i < n; i++) {
    uint64_t ty = arg_at(p_args, i), deps = ty & DEPS_MASK;
    uint32_t s = TYPE_SORT(ty);
    ENSURE(!(ty & RSVD_BIT) && s < nsorts, "bad binder");
    if (ty & BOUND_BIT) {
      ENSURE(!(sorts[s] & SORT_STRICT) && nbv < 55 && deps == (1ull << nbv), "bad bound binder");
      bpos[nbv++] = (int)i;
      b[i] = (Binder){ (uint16_t)(1 + s), 1, 0 };
    } else {
      ENSURE((deps >> nbv) == 0, "bad regular binder deps");
      uint64_t td = 0;
      for (int k = 0; k < nbv; k++) if (deps >> k & 1) td |= 1ull << bpos[k];
      b[i] = (Binder){ (uint16_t)(1 + s), 0, td };
    }
  }
  if (has_ret) {
    uint64_t ret = arg_at(p_args, n), rdeps = ret & DEPS_MASK;
    ENSURE(!(ret & RSVD_BIT) && !(ret & BOUND_BIT) && (rdeps >> nbv) == 0, "bad return type");
    uint64_t td = 0;
    for (int k = 0; k < nbv; k++) if (rdeps >> k & 1) td |= 1ull << bpos[k];
    *ret_out = td;
  }
  ENSURE(tc_ctx((int)n, b), "tc_ctx rejected binders");   /* dummies are pushed as the proof meets them */
  tc_birth();                                       /* this statement's terms are birth-named occurrences */
  for (uint32_t i = 0; i < n; i++) push_h((Slot){ .tag = SL_EXPR, .e1 = tc_v((int)i) });
  next_var = (int)n;
}

enum { U_DEF, U_THM_END };
static void run_unify(int mode, uint32_t tid, const uint8_t *cmd, uint32_t tgt, Term *dum_out) {
  usp = 0; ustack[usp++] = tgt;
  int hcount = 0, dcount = 0;
  for (;;) {
    uint32_t sz, data; unpack(cmd, &sz, &data);
    switch (*cmd & 0x3F) {
      case CMD_END:
        if (mode == U_THM_END) { ENSURE(hsp == 0, "unfinished hstack"); thm_nhyp[tid] = (uint8_t)hcount; }
        ENSURE(usp == 0, "unfinished ustack");
        return;
      case CMD_UNIFY_REF: {
        ENSURE(data < (uint32_t)uhp && usp > 0, "bad URef");
        uint32_t e = ustack[--usp];
        ENSURE((uheap[data] & ~USAVED) == e, "URef mismatch");
        break;
      }
      case CMD_UNIFY_TERM:
      case CMD_UNIFY_TERM_SAVE: {
        ENSURE(usp > 0, "ustack underflow");
        Term e = ustack[--usp]; uint8_t k; uint32_t head; int ar; const Term *a;
        tc_node(e, &k, &head, &ar, &a);
        ENSURE(k == K_APP && data < nterms && head == (uint32_t)term_con[data] && usp + ar <= MAX_STACK, "UTerm mismatch");
        for (int i = ar - 1; i >= 0; i--) ustack[usp++] = a[i];
        if (*cmd & 1) { ENSURE(uhp < MAX_STACK, "uheap overflow"); uheap[uhp++] = e | USAVED; }
        break;
      }
      case CMD_UNIFY_DUMMY: {
        ENSURE(mode == U_DEF && usp > 0, "bad UDummy");
        Term x = ustack[--usp]; uint8_t k; uint32_t head; int ar; const Term *a;
        tc_node(x, &k, &head, &ar, &a);
        ENSURE(k == K_VAR && dcount < def_ndum[tid], "UDummy mismatch");
        if (dum_out) dum_out[def_dmap[tid][dcount]] = x;
        else {
          uint16_t n = le16(file + p_terms + 8 * (size_t)tid);
          ENSURE(head >= n && tc_sort_of(x) == (uint16_t)(1 + data), "UDummy type mismatch");
          for (int i = n; i < uhp; i++) ENSURE(uheap[i] != x, "UDummy disjoint violation");
          def_dmap[tid][dcount] = (uint8_t)(head - n);
        }
        dcount++;
        ENSURE(uhp < MAX_STACK, "uheap overflow");
        uheap[uhp++] = x;
        break;
      }
      case CMD_UNIFY_HYP:
        ENSURE(mode == U_THM_END && usp == 0 && hsp > 0, "bad UHypEnd");
        ustack[usp++] = hstack[--hsp];
        hcount++;
        break;
      default: die("unknown unify opcode");
    }
    cmd += sz;
  }
}

enum { P_DEF = 0, P_AX = 1, P_THM = 2 };
static const uint8_t *run_proof(int mode, const uint8_t *cmd) {
  bool is_def = (mode == P_DEF);
  for (;;) {
    uint32_t sz, data; unpack(cmd, &sz, &data);
    switch (*cmd & 0x3F) {
      case CMD_END: return cmd + sz;
      case CMD_PROOF_REF: {
        ENSURE(data < hp, "bad PRef");
        Slot s = heap[data];
        if (__builtin_expect(s.tag == SL_CONV, 0)) {
          Slot q = pop(SL_COCONV);
          ENSURE(q.e1 == s.e1 && (uint32_t)q.e2 == (uint32_t)s.e2, "ConvRef mismatch");
          convs[q.conv] = convs[s.conv];
        } else push(s);
        break;
      }
      case CMD_PROOF_DUMMY: {
        ENSURE(data < nsorts && !(sorts[data] & (SORT_STRICT | SORT_FREE)) && nbv < 55
               && tc_ctx_push((Binder){ (uint16_t)(1 + data), 1, 0 }), "bad PDummy");
        int v = next_var++;
        Term t = tc_v(v);
        nbv++;
        push_expr(t); push_h((Slot){ .tag = SL_EXPR, .e1 = t });
        break;
      }
      case CMD_PROOF_TERM:
      case CMD_PROOF_TERM_SAVE: {
        ENSURE(data < nterms, "bad PTerm");
        uint8_t n = term_arity[data];
        ENSURE(sp >= n, "PTerm arity/stack");
        sp -= n;
        Term t = tc_app(term_con[data], &se1[sp]);
        ENSURE(t != 0, "tc_app rejected PTerm");
        push_expr(t);
        if (*cmd & 1) push_h((Slot){ .tag = SL_EXPR, .e1 = t });
        break;
      }
      case CMD_PROOF_THM:
      case CMD_PROOF_THM_SAVE: {
        ENSURE(mode == P_THM && data < nthms, "bad PThm");
        uint8_t n = thm_nvar[data];
        ENSURE(sp > n, "PThm stack underflow");
        Term concl = se1[--sp];
        uint32_t ap = sp -= n, hi = concl;
        for (uint8_t i = 0; i < n; i++) hi |= se1[ap + i];
        ENSURE(!(hi >> 30), "PThm arg slot");
        /* The kernel checks sort/bound/disjointness, matches the premises against the theorem's
           hypotheses, and checks the conclusion itself, so the unify stream is not replayed here. */
        gst.kind = ST_RULE; gst.rule = thm_rule[data]; gst.inst = n ? &se1[ap] : NULL; gst.target = concl;
        for (int j = (int)thm_nhyp[data] - 1; j >= 0; j--) gst.prem[j] = pop_proof().e2;
        int step = tc_lemma_step(&gst);
        ENSURE(step >= 0, "tc_lemma_step thm");
        Slot s = { .tag = SL_PROOF, .e1 = concl, .e2 = step };
        push(s);
        if (*cmd & 1) push_h(s);
        break;
      }
      case CMD_PROOF_HYP: {
        ENSURE(!is_def && nhyp < TC_HYPS && hsp < 64, "bad PHyp");
        Slot e = pop(SL_EXPR);
        ENSURE(sorts[tc_sort_of(e.e1) - 1] & SORT_PROVABLE, "PHyp not provable");
        if (mode == P_THM) ENSURE(tc_lemma_hyp(e.e1), "tc_lemma_hyp");
        hyps[nhyp] = e.e1;
        hstack[hsp++] = e.e1;
        push_h((Slot){ .tag = SL_PROOF, .e1 = e.e1, .e2 = -1 - nhyp++ });
        break;
      }
      case CMD_PROOF_CONV: {
        ENSURE(mode == P_THM, "bad PConv");
        Slot p2 = pop_proof(), e1 = pop(SL_EXPR);
        uint32_t c = alloc_conv(1);
        push((Slot){ .tag = SL_PROOF, .e1 = e1.e1, .e2 = p2.e2, .conv = c });
        push((Slot){ .tag = SL_COCONV, .e1 = e1.e1, .e2 = (int32_t)p2.e1, .conv = c });
        break;
      }
      case CMD_PROOF_REFL: {
        Slot q = pop(SL_COCONV);
        ENSURE(q.e1 == (uint32_t)q.e2, "Refl mismatch");
        convs[q.conv] = (Conv){ .kind = CV_REFL, .t = q.e1 };
        break;
      }
      case CMD_PROOF_SYMM: {
        Slot q = pop(SL_COCONV);
        uint32_t k = alloc_conv(1);
        convs[q.conv] = (Conv){ .kind = CV_SYM, .kid = &convs[k] };
        push((Slot){ .tag = SL_COCONV, .e1 = (uint32_t)q.e2, .e2 = (int32_t)q.e1, .conv = k });
        break;
      }
      case CMD_PROOF_CONG: {
        Slot q = pop(SL_COCONV);
        uint8_t k1, k2; uint32_t h1, h2; int n, n2; const Term *a1, *a2;
        tc_node(q.e1, &k1, &h1, &n, &a1);
        tc_node((Term)q.e2, &k2, &h2, &n2, &a2);
        ENSURE(k1 == K_APP && k2 == K_APP && h1 == h2 && n == n2, "Cong mismatch");
        uint32_t kids = n ? alloc_conv(n) : 0;
        convs[q.conv] = (Conv){ .kind = CV_CONG, .con = (int)h1, .n = n, .kid = n ? &convs[kids] : NULL };
        for (int i = n - 1; i >= 0; i--)
          push((Slot){ .tag = SL_COCONV, .e1 = a1[i], .e2 = (int32_t)a2[i], .conv = kids + (uint32_t)i });
        break;
      }
      case CMD_PROOF_UNFOLD: {
        Slot e = pop(SL_EXPR), q = pop(SL_COCONV);
        uint8_t k1; uint32_t tid; int n; const Term *a1;
        tc_node(q.e1, &k1, &tid, &n, &a1);
        ENSURE(k1 == K_APP && tid < nterms, "Unfold not app");
        const uint8_t *tp = file + p_terms + 8 * (size_t)tid;
        uint32_t pa = le32(tp + 4);
        ENSURE((tp[2] & 0x80) != 0, "Unfold not def");
        uhp = n;
        Term *args = n ? alloc_tp(n) : NULL;
        Term *dums = def_ndum[tid] ? alloc_tp(def_ndum[tid]) : NULL;
        if (dums) memset(dums, 0, (size_t)def_ndum[tid] * sizeof(Term));
        for (int i = 0; i < n; i++) uheap[i] = args[i] = a1[i];
        run_unify(U_DEF, tid, file + pa + 8 * ((size_t)n + 1), e.e1, dums);
        uint32_t k = alloc_conv(1);
        convs[q.conv] = (Conv){ .kind = CV_UNFOLD, .con = (int)tid, .t = e.e1, .args = args, .dummies = dums, .kid = &convs[k] };
        push((Slot){ .tag = SL_COCONV, .e1 = e.e1, .e2 = q.e2, .conv = k });
        break;
      }
      case CMD_PROOF_CONV_CUT: {
        Slot q = pop(SL_COCONV);
        push((Slot){ .tag = SL_CONV, .e1 = q.e1, .e2 = q.e2, .conv = q.conv });
        push(q);
        break;
      }
      case CMD_PROOF_CONV_SAVE:
        push_h(pop(SL_CONV));
        break;
      case CMD_PROOF_SAVE: {
        uint8_t tag = (uint8_t)(se1[sp - 1] >> 30);
        ENSURE(sp > 0 && tag != SL_COCONV, "bad PSave");
        Slot top = { se1[sp - 1] & 0x3FFFFFFFu, se2[sp - 1], sconv[sp - 1], tag };
        if (tag == SL_PROOF) { realize_proof(&top); se2[sp - 1] = top.e2; sconv[sp - 1] = 0; }
        push_h(top);
        break;
      }
      case CMD_PROOF_SORRY: die("proof uses sorry"); break;
      default: die("unknown proof opcode");
    }
    cmd += sz;
  }
}

int main(int argc, char **argv) {
  double t_start = now_ms();
  sp_auto_init(argc, argv);
  FILE *f = fopen(argv[1], "rb");
  if (!f) { perror(argv[1]); return 2; }
  fseek(f, 0, SEEK_END); flen = (size_t)ftell(f); fseek(f, 0, SEEK_SET);
  uint8_t *buf = malloc(flen + 8);
  ENSURE(buf && fread(buf, 1, flen, f) == flen, "read failed");
  fclose(f);
  file = buf; fend = buf + flen;

  ENSURE(flen >= 40 && le32(file) == 0x42304D4Du && file[4] == 1, "bad MM0B header");
  num_sorts = file[5]; num_terms = le32(file + 8); num_thms = le32(file + 12);
  p_terms = le32(file + 16); p_thms = le32(file + 20); p_proof = le32(file + 24);
  ENSURE(num_sorts <= 128 && num_terms <= 8192 && num_thms <= 16384 && flen >= 40 + (size_t)num_sorts, "bad sorts header");
  ENSURE(flen >= p_terms + (uint64_t)num_terms * 8 && flen >= p_thms + (uint64_t)num_thms * 8 && flen > p_proof, "table out of range");
  sorts = file + 40;

  ENSURE(tc_init(1u << 13, 2), "tc_init");

  long n_ax = 0, n_def = 0, n_trm = 0, n_thm = 0;
  const uint8_t *stmt = file + p_proof;
  while (*stmt != CMD_END) {
    uint32_t sz, data; unpack(stmt, &sz, &data);
    size_t off = (size_t)(stmt - file);
    ENSURE(data <= flen - off && flen - off - data >= 5, "stmt out of range");
    const uint8_t *next = stmt + data;
    uint8_t op = *stmt & 0x3F;
    Binder b[TC_VARS];
    switch (op) {
      case CMD_STMT_SORT:
        ENSURE(data == sz && nsorts < num_sorts, "bad sort stmt");
        ENSURE(tc_sort(sorts[nsorts]) == (int)(1 + nsorts), "tc_sort");
        sp_check_sort(sorts[nsorts]);
        nsorts++;
        break;
      case CMD_STMT_DEF:
      case CMD_STMT_LOCAL_DEF: {
        ENSURE(nterms < num_terms, "term overflow");
        const uint8_t *tp = file + p_terms + 8 * (size_t)nterms;
        uint16_t n = le16(tp); uint8_t s = tp[2] & 0x7F; uint32_t pa = le32(tp + 4);
        ENSURE(s < nsorts && !(sorts[s] & SORT_PURE), "bad term sort");
        uint64_t retdeps = 0; uint8_t ndum = 0;
        load_binders(pa, n, true, b, &retdeps);
        ENSURE((arg_at(pa, n) >> 56) == s, "bad return sort");
        def_ndum[nterms] = 0;
        Term d_body = 0, u_dums[TC_VARS];
        uint16_t u_dsorts[TC_VARS];
        if (tp[2] & 0x80) {
          const uint8_t *end = run_proof(P_DEF, stmt + sz);
          ENSURE(end == next && sp == 1 && !(se1[0] >> 30), "bad def proof");
          def_ndum[nterms] = ndum = (uint8_t)(next_var - (int)n);
          uint32_t val = se1[0];
          uhp = (int)n;
          for (uint16_t i = 0; i < n; i++) uheap[i] = heap[i].e1;
          run_unify(U_DEF, nterms, file + pa + 8 * ((size_t)n + 1), val, NULL);
          d_body = val;
          term_con[nterms] = tc_def((uint16_t)(1 + s), retdeps, n, ndum, d_body);
          ENSURE(term_con[nterms] >= 0, "tc_def rejected");
          for (int k = 0; k < ndum; k++) {
            uint8_t di = def_dmap[nterms][k];
            u_dums[k] = tc_v((int)n + di);
            u_dsorts[k] = tc_sort_of(u_dums[k]);
          }
          n_def++;
        } else {
          ENSURE(op != CMD_STMT_LOCAL_DEF && data == sz, "bad prim term stmt");
          term_con[nterms] = tc_con((uint16_t)(1 + s), retdeps, n, b);
          ENSURE(term_con[nterms] >= 0, "tc_con rejected");
          n_trm++;
        }
        term_arity[nterms] = (uint8_t)n;
        if (op != CMD_STMT_LOCAL_DEF)
          sp_check_term_or_def((tp[2] & 0x80) != 0, nterms, term_con[nterms], n, b, (uint16_t)(1 + s), retdeps, d_body, ndum, u_dums, u_dsorts);
        nterms++;
        break;
      }
      case CMD_STMT_AXIOM:
      case CMD_STMT_THM:
      case CMD_STMT_LOCAL_THM: {
        ENSURE(nthms < num_thms, "thm overflow");
        const uint8_t *tp = file + p_thms + 8 * (size_t)nthms;
        uint16_t n = le16(tp); uint32_t pa = le32(tp + 4);
        bool is_thm = (op & 0x37) == CMD_STMT_THM;
        load_binders(pa, n, false, b, NULL);
        if (is_thm) ENSURE(tc_lemma(n, 0), "tc_lemma");
        const uint8_t *end = run_proof(is_thm ? P_THM : P_AX, stmt + sz);
        ENSURE(end == next && sp == 1 && (se1[0] >> 30) == (is_thm ? SL_PROOF : SL_EXPR), "bad thm proof");
        Slot top = { se1[0] & 0x3FFFFFFFu, se2[0], sconv[0], (uint8_t)(se1[0] >> 30) };
        if (is_thm) realize_proof(&top);
        uint32_t val = top.e1;
        ENSURE(sorts[tc_sort_of(val) - 1] & SORT_PROVABLE, "concl not provable");
        uhp = (int)n;
        for (uint16_t i = 0; i < n; i++) uheap[i] = heap[i].e1;
        run_unify(U_THM_END, nthms, file + pa + 8 * (size_t)n, val, NULL);
        if (op != CMD_STMT_LOCAL_THM)               /* before the kernel call, which releases these terms */
          sp_check_ax_or_thm(is_thm, nthms, n, b, nhyp, hyps, val);
        if (!is_thm) {
          Rule r = { .nkeep = (uint8_t)nhyp, .make = { val, 0 }, .fresh = -1 };
          for (int i = 0; i < nhyp; i++) r.keep[i] = (Pat){ hyps[i], 0 };
          thm_rule[nthms] = tc_rule(&r);
          ENSURE(thm_rule[nthms] >= 0, "tc_rule rejected axiom");
          n_ax++;
        } else {
          ENSURE(tc_lemma_term(top.e2) == val, "thm concl mismatch");
          thm_rule[nthms] = tc_lemma_end(top.e2);
          ENSURE(thm_rule[nthms] >= 0, "tc_lemma_end rejected theorem");
          n_thm++;
        }
        thm_nvar[nthms] = (uint8_t)n;
        nthms++;
        break;
      }
      default: die("bad statement opcode");
    }
    stmt = next;
  }
  ENSURE(nsorts == num_sorts && nterms == num_terms && nthms == num_thms, "incomplete declarations");
  sp_finish();
  double t_total = now_ms() - t_start;
  printf("%s: %u sorts, %ld terms, %ld defs, %ld axioms, %ld theorems (%llu kernel steps) ok%s  [total %.2f ms]\n",
         argv[1], nsorts, n_trm, n_def, n_ax, n_thm, (unsigned long long)tc_steps(),
         sp_proof_only ? " [NOT CHECKED AGAINST A SPEC]" : "", t_total);
  free(buf);
  return 0;
}
