/* mm0_spec.h: Optional .mm0 specification parser and checker for mm0_tcalc and mmb_tcalc.
   Parses .mm0 surface syntax (sorts, terms, defs, axioms, theorems, delimiters, prefix/infix/
   general notations, and coercions), lowers parsed math expressions directly into tcalc's
   hash-consed Term arena, and checks every non-local declaration against the proof file. */
#pragma once
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "tcalc.h"

#define SP_ENSURE(msg, cond) do { if (!(cond)) { fprintf(stderr, "FAIL spec: %s\n", (msg)); exit(1); } } while (0)

enum {
  SP_KW_AXIOM = 1, SP_KW_COERCION, SP_KW_DEF, SP_KW_DELIMITER, SP_KW_FREE,
  SP_KW_INFIXL, SP_KW_INFIXR, SP_KW_MAX, SP_KW_NOTATION, SP_KW_PREC,
  SP_KW_PREFIX, SP_KW_PROVABLE, SP_KW_PURE, SP_KW_SORT, SP_KW_STRICT,
  SP_KW_TERM, SP_KW_THEOREM
};
enum { SP_STMT_END = 0, SP_STMT_AXIOM = 2, SP_STMT_SORT = 4, SP_STMT_DEF = 5, SP_STMT_THM = 6 };
enum { SP_SORT_PURE = 1, SP_SORT_STRICT = 2, SP_SORT_PROVABLE = 4, SP_SORT_FREE = 8 };
enum { SP_DELIM_SPACE = 1, SP_DELIM_LEFT = 2, SP_DELIM_RIGHT = 4 };
enum { SP_COE_EMPTY = 0, SP_COE_ONE, SP_COE_TRANS, SP_COE_PROV };
enum { SP_EXPR_VAR = 0, SP_EXPR_TERM = 1 };

typedef struct { uint32_t next[16]; uint32_t data; } SpTrie;
typedef struct { uint8_t tag; union { uint32_t termid; uint8_t trans; }; } SpCoe;
typedef struct { uint16_t prec; bool prec_set; uint32_t prefix; uint32_t infix; } SpTokenInfo;
typedef struct { uint32_t tag; union { struct { uint32_t token; } cnst; struct { uint16_t var, prec; } var; }; } SpLit;
typedef struct { uint32_t termid; uint16_t num_args, num_lits; SpLit lits[]; } SpPrefixInfo;
typedef struct { uint32_t termid; uint8_t rassoc; } SpInfixInfo;
typedef struct { uint8_t tag; uint16_t num_args; uint32_t termid; uint32_t args[]; } SpParseTerm;
typedef struct { uint8_t tag; uint16_t var; } SpParseVar;
typedef struct { uint32_t hd, tl; } SpExprList;

typedef struct {
  uint16_t num_args;
  uint16_t ret_sort; /* 1-based tcalc sort */
  uint64_t ret_deps;
  int con_id;
  bool is_def;
  Binder b[TC_ARGS];
} SpTermMeta;

static bool sp_active;
static bool sp_proof_only;
static int sp_depth;
static uint8_t *sp_buf, *sp_cur, *sp_end;
static SpTrie sp_t_sorts[1024], *sp_t_sorts_end;
static SpTrie sp_t_terms[32768], *sp_t_terms_end;
static SpTrie sp_t_thms[65536], *sp_t_thms_end;
static SpTrie sp_t_tokens[16384], *sp_t_tokens_end;
static SpTrie *sp_open_paren, *sp_close_paren;
static uint8_t sp_delims[256];
static SpCoe sp_coes[128][129];
static uint32_t sp_arena[65536], sp_arena_sz;
static uint32_t sp_store[262144], sp_store_sz;
static struct { uint16_t prec; uint8_t rassoc; } sp_prec_assoc[1024];
static int sp_prec_assoc_sz;
static struct { uint32_t trie, var; } sp_var_nodes[256];
static uint8_t sp_var_sorts[256]; /* 0-based sort */
static int sp_num_vars;
static uint8_t sp_sorts[128], sp_coe_uf[128];
static uint32_t sp_num_sorts;
static SpTermMeta sp_terms[8192];

#define SP_PROV 128
#define SP_PALLOC(val, sz) ({ \
  typeof(val) _v = (val); \
  uint32_t _w = ((uint32_t)(sz) + 3u) / 4u; \
  SP_ENSURE("parser arena overflow", sp_arena_sz + _w <= 65536); \
  uint32_t _p = sp_arena_sz; \
  memcpy(&sp_arena[_p], &_v, sizeof(_v)); \
  sp_arena_sz += _w; \
  _p; \
})
#define SP_SALLOC(val, sz) ({ \
  typeof(val) _v = (val); \
  uint32_t _w = ((uint32_t)(sz) + 3u) / 4u; \
  SP_ENSURE("parser store overflow", sp_store_sz + _w <= 262144); \
  uint32_t _p = sp_store_sz; \
  memcpy(&sp_store[_p], &_v, sizeof(_v)); \
  sp_store_sz += _w; \
  _p; \
})

static inline bool sp_is_ws(uint8_t c) { return c == ' ' || c == '\n'; }
static inline bool sp_ident_start(uint8_t c) { return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_'; }
static inline bool sp_ident_rest(uint8_t c) { return sp_ident_start(c) || (c >= '0' && c <= '9'); }

static void sp_ws(void) {
  for (;;) {
    if (sp_cur >= sp_end || *sp_cur == 0) return;
    if (sp_cur + 1 < sp_end && sp_cur[0] == '-' && sp_cur[1] == '-') {
      sp_cur += 2;
      while (sp_cur < sp_end && *sp_cur && *sp_cur != '\n') sp_cur++;
    } else if (sp_is_ws(*sp_cur)) {
      sp_cur++;
    } else return;
  }
}

#define SP_CHK_KW(str, val) do { \
  size_t _l = sizeof(str) - 1; \
  if ((size_t)(sp_end - sp_cur) >= _l && memcmp(str, sp_cur, _l) == 0 && !sp_ident_rest(sp_cur[_l])) { \
    sp_cur += _l; sp_ws(); return (val); \
  } else return 0; \
} while (0)

static int sp_kw(void) {
  switch (*sp_cur) {
    case 'a': SP_CHK_KW("axiom", SP_KW_AXIOM);
    case 'c': SP_CHK_KW("coercion", SP_KW_COERCION);
    case 'd':
      if (sp_cur[1] == 'e' && sp_cur[2] == 'f') SP_CHK_KW("def", SP_KW_DEF);
      if (sp_cur[1] == 'e' && sp_cur[2] == 'l') SP_CHK_KW("delimiter", SP_KW_DELIMITER);
      return 0;
    case 'f': SP_CHK_KW("free", SP_KW_FREE);
    case 'i':
      if (sp_cur[1] == 'n' && sp_cur[2] == 'f' && sp_cur[3] == 'i' && sp_cur[4] == 'x') {
        if (sp_cur[5] == 'l') SP_CHK_KW("infixl", SP_KW_INFIXL);
        if (sp_cur[5] == 'r') SP_CHK_KW("infixr", SP_KW_INFIXR);
      }
      return 0;
    case 'm': SP_CHK_KW("max", SP_KW_MAX);
    case 'n': SP_CHK_KW("notation", SP_KW_NOTATION);
    case 'p':
      if (sp_cur[1] == 'r' && sp_cur[2] == 'e' && sp_cur[3] == 'c') SP_CHK_KW("prec", SP_KW_PREC);
      if (sp_cur[1] == 'r' && sp_cur[2] == 'e' && sp_cur[3] == 'f') SP_CHK_KW("prefix", SP_KW_PREFIX);
      if (sp_cur[1] == 'r' && sp_cur[2] == 'o' && sp_cur[3] == 'v') SP_CHK_KW("provable", SP_KW_PROVABLE);
      if (sp_cur[1] == 'u' && sp_cur[2] == 'r' && sp_cur[3] == 'e') SP_CHK_KW("pure", SP_KW_PURE);
      return 0;
    case 's':
      if (sp_cur[1] == 'o') SP_CHK_KW("sort", SP_KW_SORT);
      if (sp_cur[1] == 't') SP_CHK_KW("strict", SP_KW_STRICT);
      return 0;
    case 't':
      if (sp_cur[1] == 'e') SP_CHK_KW("term", SP_KW_TERM);
      if (sp_cur[1] == 'h') SP_CHK_KW("theorem", SP_KW_THEOREM);
      return 0;
    default: return 0;
  }
}

static bool sp_ch(uint8_t c) {
  if (*sp_cur == c) { sp_cur++; sp_ws(); return true; }
  return false;
}

static uint16_t sp_prec(void) {
  uint8_t c = *sp_cur;
  if (c < '0' || c > '9') {
    SP_ENSURE("expected number or 'max'", sp_kw() == SP_KW_MAX);
    return 0xFFFF;
  }
  if (c == '0') {
    sp_cur++;
    SP_ENSURE("leading zero in prec", (*sp_cur < '0' || *sp_cur > '9') && !sp_ident_rest(*sp_cur));
    sp_ws();
    return 0;
  }
  uint32_t val = 0;
  while (*sp_cur >= '0' && *sp_cur <= '9') {
    val = val * 10 + (uint32_t)(*sp_cur - '0');
    SP_ENSURE("prec out of range", val < 0xFFFF);
    sp_cur++;
  }
  SP_ENSURE("invalid number", !sp_ident_rest(*sp_cur));
  sp_ws();
  return (uint16_t)val;
}

static SpTrie *sp_extend(SpTrie *T, uint32_t *tgt, SpTrie **end, uint32_t lim) {
  if (*tgt) return T + *tgt;
  SP_ENSURE("trie overflow", (uint32_t)(*end - T) < lim);
  SpTrie *res = (*end)++;
  *tgt = (uint32_t)(res - T);
  return res;
}

typedef struct { int blank; SpTrie *x; } SpIdentBlank;

static SpIdentBlank sp_lookup_ident_(SpTrie *T) {
  uint8_t c = *sp_cur;
  if (!sp_ident_start(c)) return (SpIdentBlank){ 0, T };
  SpIdentBlank res = { c == '_' && !sp_ident_rest(sp_cur[1]), T + 1 };
  do {
    res.x = T + T[res.x->next[c & 0xF]].next[(c >> 4) & 0xF];
    sp_cur++;
    c = *sp_cur;
  } while (sp_ident_rest(c));
  sp_ws();
  return res;
}

static SpTrie *sp_lookup_ident(SpTrie *T) {
  SpIdentBlank res = sp_lookup_ident_(T);
  SP_ENSURE("expecting identifier, not '_'", !res.blank);
  return res.x;
}

static uint32_t sp_lookup_var(void) {
  return ~sp_t_terms[sp_lookup_ident(sp_t_terms)->next[0]].data;
}

static SpIdentBlank sp_parse_new_ident_(SpTrie *T, SpTrie **end, uint32_t lim) {
  uint8_t c = *sp_cur;
  SP_ENSURE("expecting identifier", sp_ident_start(c));
  SpIdentBlank res = { c == '_' && !sp_ident_rest(sp_cur[1]), T + 1 };
  do {
    res.x = sp_extend(T, &res.x->next[c & 0xF], end, lim);
    res.x = sp_extend(T, &res.x->next[(c >> 4) & 0xF], end, lim);
    sp_cur++;
    c = *sp_cur;
  } while (sp_ident_rest(c));
  sp_ws();
  return res;
}

static SpTrie *sp_parse_new_ident(SpTrie *T, SpTrie **end, uint32_t lim) {
  SpIdentBlank res = sp_parse_new_ident_(T, end, lim);
  SP_ENSURE("expecting identifier, not '_'", !res.blank);
  return res.x;
}

static uint32_t sp_parse_new_token(void) {
  SP_ENSURE("expecting '$'", *sp_cur == '$');
  do { sp_cur++; } while (sp_is_ws(*sp_cur));
  uint8_t c = *sp_cur;
  SP_ENSURE("expecting token char", c != '$' && c != 0);
  SpTrie *p = sp_t_tokens + 1;
  do {
    p = sp_extend(sp_t_tokens, &p->next[c & 0xF], &sp_t_tokens_end, 16384);
    p = sp_extend(sp_t_tokens, &p->next[(c >> 4) & 0xF], &sp_t_tokens_end, 16384);
    sp_cur++;
    c = *sp_cur;
  } while (!sp_is_ws(c) && c != '$' && c != 0);
  while (sp_is_ws(*sp_cur)) sp_cur++;
  SP_ENSURE("expecting '$'", sp_ch('$'));
  SP_ENSURE("parens are not valid tokens", p != sp_open_paren && p != sp_close_paren);
  return p->data ? p->data : (p->data = SP_PALLOC(((SpTokenInfo){0}), sizeof(SpTokenInfo)));
}

typedef struct { SpTrie *var, *tk; } SpTokenRes;
static SpTokenRes sp_token(void) {
  SpTrie *var = sp_t_terms + 1, *tk = sp_t_tokens + 1;
  uint8_t c = *sp_cur;
  SP_ENSURE("expecting token", c != '$' && c != 0);
  do {
    var = sp_t_terms + sp_t_terms[var->next[c & 0xF]].next[(c >> 4) & 0xF];
    tk = sp_t_tokens + sp_t_tokens[tk->next[c & 0xF]].next[(c >> 4) & 0xF];
    sp_cur++;
    if (sp_delims[c] & SP_DELIM_LEFT) break;
    c = *sp_cur;
  } while (!(sp_delims[c] & SP_DELIM_RIGHT) && c != 0);
  while (sp_is_ws(*sp_cur)) sp_cur++;
  return (SpTokenRes){ var, tk };
}

typedef struct { uint32_t expr; uint8_t sort; } SpExprSort;
static uint32_t sp_coerce(SpExprSort es, uint8_t tgt) {
  if (es.sort == tgt) return es.expr;
  SpCoe *c = &sp_coes[es.sort][tgt];
  switch (c->tag) {
    case SP_COE_ONE: {
      uint32_t e = SP_SALLOC(((SpParseTerm){ SP_EXPR_TERM, 1, c->termid }), sizeof(SpParseTerm) + sizeof(uint32_t));
      ((SpParseTerm *)&sp_store[e])->args[0] = es.expr;
      return e;
    }
    case SP_COE_TRANS:
      return sp_coerce((SpExprSort){ sp_coerce(es, c->trans), c->trans }, tgt);
    case SP_COE_PROV:
      return es.expr;
    default:
      SP_ENSURE("type mismatch in coercion", false);
      return 0;
  }
}

static SpExprSort sp_expr(uint16_t prec);
#define SP_APP_PREC 1024

static SpExprSort sp_prefix_expr(uint16_t prec) {
  SpTokenRes t = sp_token();
  if (t.tk == sp_open_paren) {
    SpExprSort e = sp_expr(0);
    SP_ENSURE("expecting ')'", sp_token().tk == sp_close_paren);
    return e;
  }
  uint32_t tk = t.tk->data;
  if (tk) {
    SpTokenInfo *info = (SpTokenInfo *)&sp_arena[tk];
    if (info->prefix) {
      SP_ENSURE("prefix prec mismatch", info->prec >= prec);
      SpPrefixInfo *pfx = (SpPrefixInfo *)&sp_arena[info->prefix];
      uint16_t nargs = pfx->num_args;
      uint32_t e = SP_SALLOC(((SpParseTerm){ SP_EXPR_TERM, nargs, pfx->termid }), sizeof(SpParseTerm) + nargs * sizeof(uint32_t));
      uint32_t *args = ((SpParseTerm *)&sp_store[e])->args;
      SpTermMeta *tm = &sp_terms[pfx->termid];
      for (int i = 0; i < pfx->num_lits; i++) {
        SpLit *lit = &pfx->lits[i];
        if (lit->tag == 0) {
          SP_ENSURE("expecting notation token", sp_token().tk->data == lit->cnst.token);
        } else {
          args[lit->var.var] = sp_coerce(sp_expr(lit->var.prec), (uint8_t)(tm->b[lit->var.var].sort - 1));
        }
      }
      return (SpExprSort){ e, (uint8_t)(tm->ret_sort - 1) };
    }
  }
  uint32_t var = sp_t_terms[t.var->next[0]].data;
  if (var) return (SpExprSort){ sp_var_nodes[~var].var, sp_var_sorts[~var] };
  SP_ENSURE("unrecognized token in prefix_expr", t.var->data != 0);
  uint32_t termid = ~t.var->data;
  SpTermMeta *tm = &sp_terms[termid];
  uint16_t nargs = tm->num_args;
  uint32_t e = SP_SALLOC(((SpParseTerm){ SP_EXPR_TERM, nargs, termid }), sizeof(SpParseTerm) + nargs * sizeof(uint32_t));
  if (nargs > 0) {
    SP_ENSURE("unexpected application at this prec", prec <= SP_APP_PREC);
    uint32_t *args = ((SpParseTerm *)&sp_store[e])->args;
    for (int i = 0; i < nargs; i++)
      args[i] = sp_coerce(sp_expr(0xFFFF), (uint8_t)(tm->b[i].sort - 1));
  }
  return (SpExprSort){ e, (uint8_t)(tm->ret_sort - 1) };
}

static SpExprSort sp_lhs_expr(uint16_t prec, SpExprSort lhs) {
  while (*sp_cur != '$' && *sp_cur != 0) {
    uint8_t *start = sp_cur;
    SpTokenRes t = sp_token();
    if (!t.tk->data) { sp_cur = start; break; }
    SpTokenInfo *info = (SpTokenInfo *)&sp_arena[t.tk->data];
    uint16_t p1 = info->prec;
    if (!info->infix || p1 < prec) { sp_cur = start; break; }
    SpInfixInfo ifx = *(SpInfixInfo *)&sp_arena[info->infix];
    uint16_t p2 = ifx.rassoc ? p1 : (uint16_t)(p1 + 1);
    SpExprSort rhs = sp_prefix_expr(p2);
    start = sp_cur;
    while (*sp_cur != '$' && *sp_cur != 0) {
      SpTokenRes t2 = sp_token();
      sp_cur = start;
      if (!t2.tk->data) break;
      SpTokenInfo *info2 = (SpTokenInfo *)&sp_arena[t2.tk->data];
      if (!info2->infix || info2->prec < p2) break;
      rhs = sp_lhs_expr(info2->prec, rhs);
      start = sp_cur;
    }
    uint32_t e = SP_SALLOC(((SpParseTerm){ SP_EXPR_TERM, 2, ifx.termid }), sizeof(SpParseTerm) + 2 * sizeof(uint32_t));
    uint32_t *args = ((SpParseTerm *)&sp_store[e])->args;
    SpTermMeta *tm = &sp_terms[ifx.termid];
    args[0] = sp_coerce(lhs, (uint8_t)(tm->b[0].sort - 1));
    args[1] = sp_coerce(rhs, (uint8_t)(tm->b[1].sort - 1));
    lhs = (SpExprSort){ e, (uint8_t)(tm->ret_sort - 1) };
  }
  return lhs;
}

static SpExprSort sp_expr(uint16_t prec) {
  SP_ENSURE("spec expression depth exceeded", ++sp_depth <= 4096);
  SpExprSort r = sp_lhs_expr(prec, sp_prefix_expr(prec));
  sp_depth--;
  return r;
}

static void sp_pop_vars(void) {
  for (int i = 0; i < sp_num_vars; i++)
    if (sp_var_nodes[i].trie) sp_t_terms[sp_var_nodes[i].trie].data = 0;
  sp_num_vars = 0;
}

static uint32_t sp_binders(int kind, uint16_t num_args, const Binder *b, uint16_t ret_sort, uint64_t ret_deps) {
  sp_store_sz = 0;
  memset(sp_var_nodes, 0, sizeof(sp_var_nodes));
  sp_num_vars = num_args;
  int arg_idx = 0;
  uint32_t p_hyps = 0xFFFFFFFFu;
  while (!sp_ch(':')) {
    int curly = sp_ch('{');
    SP_ENSURE("expecting argument binder", curly || sp_ch('('));
    uint8_t close = curly ? '}' : ')';
    int var_group_start = arg_idx;
    int dummy_group_start = sp_num_vars;

    uint8_t *start = sp_cur;
    while (!sp_ch(':')) {
      sp_ch('.');
      sp_parse_new_ident_(sp_t_terms, &sp_t_terms_end, 65536);
    }
    int is_hyp = (*sp_cur == '$');
    sp_cur = start;

    while (!sp_ch(':')) {
      int dummy = sp_ch('.');
      int i;
      if (dummy) {
        SP_ENSURE("variable overflow", sp_num_vars < 256);
        i = sp_num_vars++;
        SP_ENSURE("dummies only allowed in defs", kind == SP_KW_DEF);
      } else {
        if (!is_hyp) SP_ENSURE("too many arguments", arg_idx < num_args && arg_idx < TC_VARS);
        else SP_ENSURE("too many hypotheses", arg_idx - var_group_start < 64);
        i = arg_idx++;
      }
      SpIdentBlank x = sp_parse_new_ident_(sp_t_terms, &sp_t_terms_end, 65536);
      if (!is_hyp) {
        SP_ENSURE("hypotheses must follow variables", p_hyps == 0xFFFFFFFFu);
        if (x.blank) {
          sp_var_nodes[i].trie = 0;
        } else {
          uint32_t *p = &x.x->next[0];
          uint32_t *dat = &sp_extend(sp_t_terms, p, &sp_t_terms_end, 32768)->data;
          SP_ENSURE("variable shadowing", *dat == 0);
          *dat = ~(uint32_t)i;
          sp_var_nodes[i].trie = *p;
        }
        sp_var_nodes[i].var = SP_SALLOC(((SpParseVar){ SP_EXPR_VAR, (uint16_t)i }), sizeof(SpParseVar));
      }
    }
    if (*sp_cur == '$') {
      do { sp_cur++; } while (sp_is_ws(*sp_cur));
      SP_ENSURE("hypotheses only in axioms/theorems", kind == SP_KW_THEOREM && !curly);
      uint32_t e = sp_coerce(sp_expr(0), SP_PROV);
      SP_ENSURE("expecting '$)'", sp_ch('$') && sp_ch(')'));
      for (; arg_idx > var_group_start; arg_idx--)
        p_hyps = SP_SALLOC(((SpExprList){ e, p_hyps }), sizeof(SpExprList));
    } else {
      SP_ENSURE("too many arguments", arg_idx <= num_args);
      SpTrie *x = sp_lookup_ident(sp_t_sorts);
      SP_ENSURE("expecting sort", x->data != 0);
      uint8_t sort = (uint8_t)~x->data;
      uint64_t deps = 0;
      if (!sp_ch(close)) {
        SP_ENSURE("bound/dummy variables cannot have dependencies", !curly && dummy_group_start == sp_num_vars);
        do {
          uint32_t var = sp_lookup_var();
          SP_ENSURE("expecting prior bound variable", var < (uint32_t)var_group_start && b[var].bound);
          deps |= 1ull << var;
        } while (!sp_ch(close));
      }
      for (; var_group_start < arg_idx; var_group_start++) {
        const Binder *bi = &b[var_group_start];
        SP_ENSURE("variable type does not match theorem",
                  bi->sort == (uint16_t)(1 + sort) && bi->bound == (bool)curly && bi->deps == (curly ? 0 : deps));
        sp_var_sorts[var_group_start] = sort;
      }
      while (dummy_group_start < sp_num_vars) {
        SP_ENSURE("dummy sort cannot be strict or free", !(sp_sorts[sort] & (SP_SORT_STRICT | SP_SORT_FREE)));
        sp_var_sorts[dummy_group_start++] = sort;
      }
    }
  }

  for (;;) {
    if (*sp_cur == '$') {
      do { sp_cur++; } while (sp_is_ws(*sp_cur));
      SP_ENSURE("hypotheses only in axioms/theorems", kind == SP_KW_THEOREM);
      uint32_t e = sp_coerce(sp_expr(0), SP_PROV);
      SP_ENSURE("expecting '$'", sp_ch('$'));
      p_hyps = SP_SALLOC(((SpExprList){ e, p_hyps }), sizeof(SpExprList));
      if (!sp_ch('>')) break;
    } else {
      SP_ENSURE("hypotheses must follow variables", p_hyps == 0xFFFFFFFFu);
      SpTrie *x = sp_lookup_ident(sp_t_sorts);
      SP_ENSURE("expecting sort", x->data != 0);
      uint8_t sort = (uint8_t)~x->data;
      uint64_t deps = 0;
      while (sp_ident_start(*sp_cur)) {
        uint32_t var = sp_lookup_var();
        SP_ENSURE("expecting prior bound variable", var < (uint32_t)arg_idx && b[var].bound);
        deps |= 1ull << var;
      }
      if (sp_ch('>')) {
        SP_ENSURE("too many arguments", arg_idx < num_args);
        const Binder *bi = &b[arg_idx++];
        SP_ENSURE("variable type does not match theorem",
                  bi->sort == (uint16_t)(1 + sort) && !bi->bound && bi->deps == deps);
      } else {
        SP_ENSURE("theorem return must be statement", kind != SP_KW_THEOREM);
        SP_ENSURE("return type does not match", ret_sort == (uint16_t)(1 + sort) && ret_deps == deps);
        break;
      }
    }
  }
  SP_ENSURE("incorrect number of arguments", arg_idx == num_args);
  return p_hyps;
}

static bool sp_match_expr(uint32_t e, Term t, uint16_t num_args, int *dum_map, int *next_dum, int ndum, const Term *dum_terms, const uint16_t *dum_sorts) {
  SP_ENSURE("spec expression depth exceeded", ++sp_depth <= 4096);
  uint8_t tag = *(uint8_t *)&sp_store[e];
  if (tag == SP_EXPR_VAR) {
    SpParseVar *pv = (SpParseVar *)&sp_store[e];
    if (pv->var < num_args) { sp_depth--; return t == tc_v((int)pv->var); }
    int d = pv->var - num_args;
    SP_ENSURE("dummy index out of range", d >= 0 && d < 256);
    if (dum_map[d] < 0) {
      SP_ENSURE("too many dummies in spec body", *next_dum < ndum);
      int k = (*next_dum)++;
      SP_ENSURE("dummy sort mismatch", (uint16_t)(1 + sp_var_sorts[pv->var]) == dum_sorts[k]);
      dum_map[d] = k;
    }
    sp_depth--;
    return t == dum_terms[dum_map[d]];
  } else {
    SpParseTerm *pt = (SpParseTerm *)&sp_store[e];
    uint8_t k; uint32_t head; int ar; const Term *a;
    tc_node(t, &k, &head, &ar, &a);
    if (k != K_APP || head != (uint32_t)sp_terms[pt->termid].con_id || ar != pt->num_args) {
      sp_depth--;
      return false;
    }
    for (uint16_t i = 0; i < pt->num_args; i++)
      if (!sp_match_expr(pt->args[i], a[i], num_args, dum_map, next_dum, ndum, dum_terms, dum_sorts)) {
        sp_depth--;
        return false;
      }
    sp_depth--;
    return true;
  }
}

static void sp_set_prec(SpTokenInfo *tk, uint16_t pr) {
  if (tk->prec_set) SP_ENSURE("precedence mismatch", tk->prec == pr);
  else { tk->prec_set = true; tk->prec = pr; }
}

static void sp_insert_prec_assoc(uint16_t prec, uint8_t rassoc) {
  for (int i = 0; i < sp_prec_assoc_sz; i++) {
    if (sp_prec_assoc[i].prec == prec) {
      SP_ENSURE("prec level both left and right assoc", sp_prec_assoc[i].rassoc == rassoc);
      return;
    }
  }
  SP_ENSURE("prec assoc overflow", sp_prec_assoc_sz < 1024);
  sp_prec_assoc[sp_prec_assoc_sz++] = (typeof(sp_prec_assoc[0])){ prec, rassoc };
}

static int sp_scan_non_decl(void) {
  int mods = 0;
  for (;;) {
    int k = sp_kw();
    if (k == SP_KW_PURE || k == SP_KW_STRICT || k == SP_KW_PROVABLE || k == SP_KW_FREE) {
      int m = (k == SP_KW_PURE) ? SP_SORT_PURE : (k == SP_KW_STRICT) ? SP_SORT_STRICT :
              (k == SP_KW_PROVABLE) ? SP_SORT_PROVABLE : SP_SORT_FREE;
      SP_ENSURE("bad sort modifier order", mods < m);
      mods |= m;
      continue;
    }
    if (k == SP_KW_SORT) return SP_KW_SORT | (mods << 8);
    SP_ENSURE("modifiers only allowed before sort", mods == 0);
    if (k == SP_KW_TERM || k == SP_KW_DEF || k == SP_KW_AXIOM || k == SP_KW_THEOREM || k == 0)
      return k;
    if (k == SP_KW_DELIMITER) {
      SP_ENSURE("expecting '$'", *sp_cur == '$');
      do { sp_cur++; } while (sp_is_ws(*sp_cur));
      uint8_t *start = sp_cur;
      while (!sp_ch('$')) {
        uint8_t c = *sp_cur++;
        SP_ENSURE("bad delimiter char", c != 0 && !sp_is_ws(c) && !sp_ident_rest(c));
        sp_delims[c] |= SP_DELIM_LEFT;
        uint8_t w = *sp_cur;
        SP_ENSURE("multi-char delimiter", sp_is_ws(w) || w == '$');
        while (sp_is_ws(*sp_cur)) sp_cur++;
      }
      if (*sp_cur == ';') {
        sp_cur = start;
      } else {
        SP_ENSURE("expecting '$' or ';'", *sp_cur == '$');
        do { sp_cur++; } while (sp_is_ws(*sp_cur));
      }
      while (!sp_ch('$')) {
        uint8_t c = *sp_cur++;
        SP_ENSURE("bad delimiter char", c != 0 && !sp_is_ws(c) && !sp_ident_rest(c));
        sp_delims[c] |= SP_DELIM_RIGHT;
        uint8_t w = *sp_cur;
        SP_ENSURE("multi-char delimiter", sp_is_ws(w) || w == '$');
        while (sp_is_ws(*sp_cur)) sp_cur++;
      }
      SP_ENSURE("expecting ';'", sp_ch(';'));
    } else if (k == SP_KW_PREFIX || k == SP_KW_INFIXL || k == SP_KW_INFIXR) {
      uint32_t x = sp_lookup_ident(sp_t_terms)->data;
      SP_ENSURE("unknown term in notation", x != 0);
      uint32_t termid = ~x;
      SP_ENSURE("expecting ':'", sp_ch(':'));
      SpTokenInfo *tk = (SpTokenInfo *)&sp_arena[sp_parse_new_token()];
      SP_ENSURE("expecting 'prec'", sp_kw() == SP_KW_PREC);
      uint16_t pr = sp_prec();
      sp_set_prec(tk, pr);
      if (k == SP_KW_PREFIX) {
        SP_ENSURE("duplicate prefix/notation token", tk->prefix == 0);
        uint16_t nargs = sp_terms[termid].num_args;
        tk->prefix = SP_PALLOC(((SpPrefixInfo){ termid, nargs, nargs }), sizeof(SpPrefixInfo) + nargs * sizeof(SpLit));
        if (nargs > 0) {
          SpLit *lits = ((SpPrefixInfo *)&sp_arena[tk->prefix])->lits;
          for (uint16_t i = 0; i < nargs; i++) {
            lits[i].tag = 1;
            lits[i].var.var = i;
            lits[i].var.prec = (i + 1 < nargs) ? 0xFFFF : pr;
          }
          sp_insert_prec_assoc(pr, 1);
        }
      } else {
        SP_ENSURE("duplicate infix token", tk->infix == 0);
        SP_ENSURE("expected binary operator", sp_terms[termid].num_args == 2);
        SP_ENSURE("prec out of range", pr < 0xFFFE);
        uint8_t rassoc = (k == SP_KW_INFIXR);
        tk->infix = SP_PALLOC(((SpInfixInfo){ termid, rassoc }), sizeof(SpInfixInfo));
        sp_insert_prec_assoc(pr, rassoc);
      }
      SP_ENSURE("expecting ';'", sp_ch(';'));
    } else if (k == SP_KW_NOTATION) {
      uint32_t x = sp_lookup_ident(sp_t_terms)->data;
      SP_ENSURE("unknown term in notation", x != 0);
      uint32_t termid = ~x;
      SpTermMeta *tm = &sp_terms[termid];
      sp_binders(SP_KW_TERM, tm->num_args, tm->b, tm->ret_sort, tm->ret_deps);
      SP_ENSURE("expecting '=' '('", sp_ch('=') && sp_ch('('));
      SpTokenInfo *tk = (SpTokenInfo *)&sp_arena[sp_parse_new_token()];
      SP_ENSURE("duplicate prefix/notation token", tk->prefix == 0);
      SP_ENSURE("expecting ':'", sp_ch(':'));
      uint16_t pr = sp_prec();
      SP_ENSURE("expecting ')'", sp_ch(')'));
      sp_set_prec(tk, pr);
      uint8_t *start = sp_cur;
      uint16_t nlits = 0;
      while (*sp_cur != ';' && *sp_cur != 0) {
        if (sp_ch('(')) {
          sp_parse_new_token();
          SP_ENSURE("expecting ':'", sp_ch(':'));
          sp_prec();
          SP_ENSURE("expecting ')'", sp_ch(')'));
        } else {
          sp_lookup_ident(sp_t_terms);
        }
        SP_ENSURE("lit overflow", nlits++ != 0xFFFF);
      }
      sp_cur = start;
      tk->prefix = SP_PALLOC(((SpPrefixInfo){ termid, tm->num_args, nlits }), sizeof(SpPrefixInfo) + nlits * sizeof(SpLit));
      SpPrefixInfo *info = (SpPrefixInfo *)&sp_arena[tk->prefix];
      uint16_t *last_prec = NULL;
      uint64_t seen_vars = 0;
      for (int i = 0; i < nlits; i++) {
        SpLit *lit = &info->lits[i];
        if ((lit->tag = !sp_ch('('))) {
          if (last_prec) *last_prec = 0xFFFF;
          uint32_t var = sp_lookup_var();
          SP_ENSURE("expecting var in notation", var < tm->num_args && !(seen_vars & (1ull << var)));
          seen_vars |= 1ull << var;
          lit->var.var = (uint16_t)var;
          last_prec = &lit->var.prec;
        } else {
          lit->cnst.token = sp_parse_new_token();
          SpTokenInfo *c = (SpTokenInfo *)&sp_arena[lit->cnst.token];
          SP_ENSURE("expecting ':'", sp_ch(':'));
          uint16_t q = sp_prec();
          SP_ENSURE("expecting ')'", sp_ch(')'));
          sp_set_prec(c, q);
          if (last_prec) {
            SP_ENSURE("prec out of range", q < 0xFFFE);
            *last_prec = (uint16_t)(q + 1);
            last_prec = NULL;
          }
        }
      }
      SP_ENSURE("missing var in notation", seen_vars == (tm->num_args == 64 ? ~0ull : ((1ull << tm->num_args) - 1ull)));
      if (last_prec) { *last_prec = pr; sp_insert_prec_assoc(pr, 1); }
      sp_pop_vars();
      SP_ENSURE("expecting ';'", sp_ch(';'));
    } else if (k == SP_KW_COERCION) {
      uint32_t x = sp_lookup_ident(sp_t_terms)->data;
      SP_ENSURE("unknown term in coercion", x != 0);
      uint32_t termid = ~x;
      SP_ENSURE("coercion must be unary", sp_terms[termid].num_args == 1 && sp_ch(':'));
      SpTrie *xs1 = sp_lookup_ident(sp_t_sorts);
      SP_ENSURE("expecting sort", xs1->data != 0 && sp_ch('>'));
      uint8_t s1 = (uint8_t)~xs1->data;
      SpTrie *xs2 = sp_lookup_ident(sp_t_sorts);
      SP_ENSURE("expecting sort", xs2->data != 0 && sp_ch(';'));
      uint8_t s2 = (uint8_t)~xs2->data;
      SP_ENSURE("coercion sort mismatch",
        sp_terms[termid].b[0].sort == (uint16_t)(s1 + 1) &&
        !sp_terms[termid].b[0].bound &&
        sp_terms[termid].b[0].deps == 0 &&
        sp_terms[termid].ret_sort == (uint16_t)(s2 + 1) &&
        sp_terms[termid].ret_deps == 0);
      for (uint32_t sl = 0; sl < sp_num_sorts; sl++) {
        if (sp_coes[sl][s1].tag != SP_COE_EMPTY) {
          SP_ENSURE("coercion cycle", sl != s2 && sp_coes[sl][s2].tag == SP_COE_EMPTY);
          sp_coes[sl][s2] = (SpCoe){ .tag = SP_COE_TRANS, .trans = s1 };
        }
      }
      SP_ENSURE("coercion cycle/diamond", s1 != s2 && sp_coes[s1][s2].tag == SP_COE_EMPTY);
      uint8_t r1 = s1, r2 = s2;
      while (sp_coe_uf[r1] != r1) r1 = sp_coe_uf[r1];
      while (sp_coe_uf[r2] != r2) r2 = sp_coe_uf[r2];
      SP_ENSURE("coercion diamond", r1 != r2);
      sp_coe_uf[r1] = r2;
      sp_coes[s1][s2] = (SpCoe){ .tag = SP_COE_ONE, .termid = termid };
      for (uint32_t sl = 0; sl < sp_num_sorts; sl++) {
        if (sl == s1 || sp_coes[sl][s1].tag != SP_COE_EMPTY) {
          for (uint32_t sr = 0; sr < sp_num_sorts; sr++) {
            if (sp_coes[s2][sr].tag != SP_COE_EMPTY) {
              SP_ENSURE("coercion cycle", sl != sr && sp_coes[sl][sr].tag == SP_COE_EMPTY);
              sp_coes[sl][sr] = (SpCoe){ .tag = SP_COE_TRANS, .trans = s2 };
            }
          }
          if (sp_coes[s2][SP_PROV].tag != SP_COE_EMPTY) {
            SP_ENSURE("coercion diamond to provable", sp_coes[sl][SP_PROV].tag == SP_COE_EMPTY);
            sp_coes[sl][SP_PROV] = (SpCoe){ .tag = SP_COE_TRANS, .trans = s2 };
          }
        }
      }
    } else {
      SP_ENSURE("unexpected keyword at statement level", false);
    }
  }
}

static void sp_check_sort(uint8_t flags) {
  if (!sp_active) return;
  int k = sp_scan_non_decl();
  SP_ENSURE("expecting sort in spec", (k & 0xFF) == SP_KW_SORT);
  SP_ENSURE("too many sorts in spec", sp_num_sorts < 128);
  uint8_t mods = (uint8_t)(k >> 8);
  SpTrie *x = sp_parse_new_ident(sp_t_sorts, &sp_t_sorts_end, 1024);
  SP_ENSURE("duplicate sort name in spec", x->data == 0);
  SP_ENSURE("sort modifiers do not match spec", mods == flags);
  x->data = ~sp_num_sorts;
  sp_sorts[sp_num_sorts] = mods;
  sp_coe_uf[sp_num_sorts] = (uint8_t)sp_num_sorts;
  if (mods & SP_SORT_PROVABLE)
    sp_coes[sp_num_sorts][SP_PROV].tag = SP_COE_PROV;
  sp_num_sorts++;
  SP_ENSURE("expecting ';'", sp_ch(';'));
}

static void sp_check_term_or_def(bool is_def, uint32_t termid, int con_id, uint16_t num_args, const Binder *b,
                                 uint16_t ret_sort, uint64_t ret_deps, Term proof_body,
                                 int ndum, const Term *dum_terms, const uint16_t *dum_sorts) {
  if (!sp_active) return;
  int k = sp_scan_non_decl();
  SP_ENSURE("expecting term/def in spec", k == (is_def ? SP_KW_DEF : SP_KW_TERM));
  SpTrie *x = sp_parse_new_ident(sp_t_terms, &sp_t_terms_end, 32768);
  sp_binders(k, num_args, b, ret_sort, ret_deps);
  if (k == SP_KW_DEF && sp_ch('=')) {
    SP_ENSURE("expecting '$'", *sp_cur == '$');
    do { sp_cur++; } while (sp_is_ws(*sp_cur));
    uint32_t e = sp_coerce(sp_expr(0), (uint8_t)(ret_sort - 1));
    SP_ENSURE("expecting '$'", sp_ch('$'));
    int dum_map[256]; memset(dum_map, -1, sizeof(dum_map));
    int next_dum = 0;
    bool ok = sp_match_expr(e, proof_body, num_args, dum_map, &next_dum, ndum, dum_terms, dum_sorts);
    SP_ENSURE("def body does not match spec", ok && next_dum == ndum);
  }
  SP_ENSURE("duplicate term/def name in spec", x->data == 0);
  x->data = ~termid;
  SpTermMeta *tm = &sp_terms[termid];
  tm->num_args = num_args; tm->ret_sort = ret_sort; tm->ret_deps = ret_deps;
  tm->con_id = con_id; tm->is_def = is_def;
  for (uint16_t i = 0; i < num_args; i++) tm->b[i] = b[i];
  sp_pop_vars();
  SP_ENSURE("expecting ';'", sp_ch(';'));
}

static void sp_check_ax_or_thm(bool is_thm, uint32_t thmid, uint16_t num_args, const Binder *b,
                               int nhyp, const Term *hyps, Term concl) {
  if (!sp_active) return;
  int k = sp_scan_non_decl();
  SP_ENSURE("expecting axiom/theorem in spec", k == (is_thm ? SP_KW_THEOREM : SP_KW_AXIOM));
  SpTrie *x = sp_parse_new_ident(sp_t_thms, &sp_t_thms_end, 65536);
  uint32_t hr = sp_binders(SP_KW_THEOREM, num_args, b, 0, 0);
  SP_ENSURE("missing theorem conclusion in spec", hr != 0xFFFFFFFFu);
  SpExprList top;
  memcpy(&top, &sp_store[hr], sizeof(top));
  int dum_map[1] = { -1 }, next_dum = 0;
  SP_ENSURE("conclusion expression mismatch with spec", sp_match_expr(top.hd, concl, num_args, dum_map, &next_dum, 0, NULL, NULL));
  uint32_t cur = top.tl;
  uint32_t rev_hyps[64]; int snh = 0;
  while (cur != 0xFFFFFFFFu) {
    SP_ENSURE("too many hypotheses in spec", snh < 64);
    SpExprList el;
    memcpy(&el, &sp_store[cur], sizeof(el));
    rev_hyps[snh++] = el.hd;
    cur = el.tl;
  }
  SP_ENSURE("hypothesis count mismatch with spec", snh == nhyp);
  for (int i = 0; i < nhyp; i++) {
    SP_ENSURE("hypothesis expression mismatch with spec", sp_match_expr(rev_hyps[nhyp - 1 - i], hyps[i], num_args, dum_map, &next_dum, 0, NULL, NULL));
  }
  SP_ENSURE("duplicate axiom/theorem name in spec", x->data == 0);
  x->data = ~thmid;
  sp_pop_vars();
  SP_ENSURE("expecting ';'", sp_ch(';'));
}

static void sp_finish(void) {
  if (!sp_active) return;
  int k = sp_scan_non_decl();
  SP_ENSURE("trailing statements or unconsumed spec input", k == 0 && *sp_cur == 0);
  free(sp_buf);
  sp_buf = NULL;
  sp_active = false;
}

static void sp_init_from_bytes(uint8_t *buf, size_t len) {
  bool in_comment = false, in_math = false;
  for (size_t i = 0; i < len; i++) {
    uint8_t c = buf[i];
    if (in_comment) {
      SP_ENSURE("invalid character in .mm0 comment", c != 0 && c != '\r');
      if (c == '\n') in_comment = false;
    } else {
      SP_ENSURE("invalid character in .mm0 spec", c == '\n' || (c >= 32 && c <= 126));
      if (c == '$') in_math = !in_math;
      else if (!in_math && c == '-' && i + 1 < len && buf[i + 1] == '-') {
        in_comment = true;
        i++;
      }
    }
  }
  sp_buf = buf;
  sp_cur = buf;
  sp_end = buf + len;
  /* one spec per process: the static tables start zeroed, so only touched pages cost memory */
  sp_t_sorts_end = sp_t_sorts + 2; sp_t_terms_end = sp_t_terms + 2;
  sp_t_thms_end = sp_t_thms + 2; sp_t_tokens_end = sp_t_tokens + 2;
  sp_arena_sz = 1; sp_store_sz = 0; sp_prec_assoc_sz = 0; sp_num_sorts = 0; sp_num_vars = 0;
  sp_delims[' '] = SP_DELIM_SPACE | SP_DELIM_RIGHT;
  sp_delims['\n'] = SP_DELIM_SPACE | SP_DELIM_RIGHT;
  sp_delims['$'] = SP_DELIM_RIGHT;
  SpTrie *p = sp_t_tokens + 1;
  p = sp_extend(sp_t_tokens, &p->next['(' & 0xF], &sp_t_tokens_end, 16384);
  sp_open_paren = sp_extend(sp_t_tokens, &p->next[('(' >> 4) & 0xF], &sp_t_tokens_end, 16384);
  p = sp_t_tokens + 1;
  p = sp_extend(sp_t_tokens, &p->next[')' & 0xF], &sp_t_tokens_end, 16384);
  sp_close_paren = sp_extend(sp_t_tokens, &p->next[(')' >> 4) & 0xF], &sp_t_tokens_end, 16384);
  sp_active = true;
  sp_ws();
}

static bool sp_load_file(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) return false;
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  fseek(f, 0, SEEK_SET);
  if (n < 0) { fclose(f); return false; }
  uint8_t *buf = calloc((size_t)n + 16, 1);
  if (!buf) { fclose(f); return false; }
  if (n > 0 && fread(buf, 1, (size_t)n, f) != (size_t)n) { free(buf); fclose(f); return false; }
  fclose(f);
  sp_init_from_bytes(buf, (size_t)n);
  return true;
}

static void sp_auto_init(int argc, char **argv) {
  sp_active = false;
  sp_proof_only = false;
  sp_depth = 0;
  SP_ENSURE("no spec: refusing (usage: verifier <proof> <spec.mm0 | - | --proof-only>)", argc == 3 && argv[2][0] != 0);
  if (strcmp(argv[2], "--proof-only") == 0) {
    sp_proof_only = true;
    return;
  }
  if (strcmp(argv[2], "-") == 0) {
    size_t cap = 65536, len = 0;
    uint8_t *buf = calloc(cap + 16, 1);
    SP_ENSURE("alloc failed", buf != NULL);
    for (;;) {
      if (len == cap) {
        cap *= 2;
        uint8_t *nb = realloc(buf, cap + 16);
        SP_ENSURE("alloc failed", nb != NULL);
        memset(nb + len, 0, cap + 16 - len);
        buf = nb;
      }
      ssize_t r = read(STDIN_FILENO, buf + len, cap - len);
      SP_ENSURE("stdin read error", r >= 0);
      if (r == 0) break;
      len += (size_t)r;
    }
    sp_init_from_bytes(buf, len);
    return;
  }
  SP_ENSURE("cannot open spec file", sp_load_file(argv[2]));
}
