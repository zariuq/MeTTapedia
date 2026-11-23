#pragma once
/* tcalc: a small kernel for the transform step.

   Terms are hash-consed n-ary nodes; a Term is an index. Each node caches its sort,
   the holes below it, its dependency mask (the bound variables it may mention) and
   whether it contains unknowns.

   State <K ; W>: K binds unknowns (with a trail, for two-way unification) and holds
   disequations; W is the set of occurrences, each a term in a space.

   One rule, fire: take occurrences, keep (read) occurrences, tell equations and
   disequations into K, check that absent/count queries hold at every solution, check
   the hole sorts and the separation guards, mint a fresh name if asked, make the result.

   Sorts and separation guards come from the binder context a rule is written in:
   a bound hole x must stay apart from every hole that does not depend on x.
   Unknowns (tc_meta) acquire a trailed sort when placed in a sorted constructor
   argument or unified with a sorted term; binding to an incompatible sort is refused.

   Extensions: tc_promote checks a proof script once against its context and installs
   it as a rule (SHARE); tc_def adds a defined constructor whose unfolding is checked
   by conversion steps (EXTEND with delta); fresh names are minted by fire. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef uint32_t Term;                       /* 0 = none; every refusal returns 0 or -1 */
typedef uint32_t Occ;                        /* occurrence id, 0 = none */
enum { K_NAME = 1, K_BV, K_VAR, K_META, K_APP };
enum { SORT_PURE = 1, SORT_STRICT = 2, SORT_PROVABLE = 4, SORT_FREE = 8 };
enum { FIBRE_PURE = 1, FIBRE_GROUND = 2, FIBRE_LINEAR = 4, FIBRE_FLAT = 8 };
#define TC_ANY   0                           /* sort 0: unsorted, no checks */
#define TC_VARS  64                          /* holes per context */
#define TC_ARGS  32                          /* constructor arity */
#define TC_HYPS  24                          /* kept premises / hypotheses per rule */

typedef struct { uint16_t sort; uint8_t bound; uint64_t deps; } Binder;  /* deps: earlier positions */
typedef struct { Term t; uint8_t space; } Pat;
typedef struct { Term t; uint8_t space; uint32_t n; } Count;
typedef struct {
  uint8_t ntake, nkeep, nabsent, ncount, ntell, nneq, nmake_extra, birth_law;
  Pat     take[4], absent[4], make, make_extra[4];
  Count   count[4];
  Term    tell[4][2], neq[4][2];
  int8_t  fresh;                             /* hole bound to a newly minted name, or -1 */
  Pat     keep[TC_HYPS];                     /* last: an installed rule stores only nkeep of them */
} Rule;

enum { TC_ENT_KEEPS = 0, TC_ENT_INPUTS = 1, TC_ENT_FRESH = 2 };
typedef struct {
  const char *name;
  uint8_t kind;
  int rule;
  uint8_t nholes;
  uint8_t holes[TC_ARGS];
} TcEntry;
typedef struct {
  const char *prefix, *header, *body_type;     /* names the specializer emits under */
  uint64_t max_slot;
  int nentries;
  TcEntry entries[32];
  int unset_rule, unset_nbinds;
  uint8_t unset_hole[TC_ARGS];
  uint64_t unset_val[TC_ARGS];
} TcTheory;

enum { CV_REFL, CV_CONG, CV_SYM, CV_UNFOLD };
typedef struct Conv {
  uint8_t kind; int con; Term t;             /* CONG/UNFOLD: con; UNFOLD: t, the unfolded term, if stated */
  int n; const struct Conv *kid;             /* CONG: n children; SYM, UNFOLD: kid[0] */
  const Term *args, *dummies;                /* UNFOLD: args (checked if given), dummies */
} Conv;
enum { ST_RULE, ST_CONV };
typedef struct {
  uint8_t kind; int rule; int prem[TC_HYPS]; /* prem: >= 0 an earlier step, -1-k hypothesis k */
  const Term *inst; Term target; const Conv *conv;
} Step;

bool tc_init(uint32_t nodes, uint32_t occs);
int  tc_sort(uint8_t flags);
int  tc_con(uint16_t sort, uint64_t retdeps, int arity, const Binder *args);
bool tc_ctx(int n, const Binder *vars);      /* the context later terms, rules and lemmas use */
bool tc_ctx_push(Binder var);                /* extend the current context by one variable */
Term tc_v(int i);                            /* context variable i */
Term tc_app(int con, const Term *args);      /* checked formation */
Term tc_name(uint16_t sort, uint64_t id);
Term tc_bv(uint16_t sort, unsigned i);       /* a concrete bound variable, i < 64 */
Term tc_meta(void);                          /* a fresh unknown */
uint64_t tc_fresh_name(void);
uint64_t tc_next_name(void);
void tc_node(Term t, uint8_t *kind, uint32_t *head, int *arity, const Term **args);  /* args: valid until a term is made */
uint64_t tc_name_id(Term t);
uint16_t tc_sort_of(Term t);
uint64_t tc_steps(void);                     /* rule and conversion steps checked so far */

void tc_protect(uint8_t space);              /* only firings write here once sealed */
void tc_seal(void);
int  tc_rule(const Rule *r);                 /* trusted, in the current context */
uint8_t tc_rule_fibre(int rule);             /* FIBRE_PURE / GROUND / LINEAR / FLAT */
int  tc_def(uint16_t sort, uint64_t retdeps, int arity, int ndummies, Term body);
int  tc_promote(int nbinders, uint8_t space, int nhyp, const Term *hyps, Term concl,
                const Step *steps, int nsteps);
bool tc_lemma(int nbinders, uint8_t space);   /* the same check, one step at a time: open a lemma, */
bool tc_lemma_hyp(Term hyp);                 /*   add hypothesis k (referred to as -1-k), */
int  tc_lemma_step(const Step *step);        /*   check a step (its index, or -1), */
Term tc_lemma_term(int ref);                 /*   read what a step or hypothesis states, */
int  tc_lemma_end(int ref);                  /*   install ref's statement as a rule (its id, or -1) */
void tc_transient(void);                     /* terms made from now on are released by the next
                                                tc_rule or tc_promote, except the patterns it installs.
                                                Anything that writes kernel state (board, K, defs, a new
                                                context or unknown) cancels it, so after a release no kernel
                                                structure holds a released term; id-keyed caches are reset. */
void tc_birth(void);                         /* birth-named transient scope: each tc_app allocates a fresh
                                                occurrence node; rule patterns compile to bytecode before release. */
void tc_unset(Occ u);                        /* declare u as the default occurrence for unset slots */
Occ  tc_post(uint8_t space, Term t);         /* trusted for protected spaces */
Occ  tc_fire(int rule, const Occ *take, const Occ *keep, const Term *inst);
const Term *tc_flat_args(Occ o, uint32_t ktag);   /* valid until a term is made */
Occ  tc_flat_make(uint8_t space, uint32_t head, uint16_t sort, int arity, const Term *args);
Occ  tc_flat_put(Occ dest, uint8_t space, int con, const Term *args);
Occ  tc_flat_out(Occ dest, uint8_t space, int con, const Term *args);
Occ  tc_flat_fire(int rule, const Occ *keep, const Term *inst, Occ dest);
Occ  tc_convert(Occ p, const Conv *c, Term target);
bool tc_alive(Occ o);
Term tc_term(Occ o);
bool tc_tell(Term u, Term v);
bool tc_tell_neq(Term u, Term v);
Term tc_deref(Term t);

/* ---- Rows 3-5: NamedSpaces, SpacesCreation (Births), and NamedSpacesReach ---- */
uint16_t tc_space_sort(void);                /* sort of space handles (allocated lazily) */
Term tc_space_term(uint8_t space);           /* canonical Term for static space 0..255 */
Term tc_at_space(Term space, Term t);        /* located pattern/term: t at space */
Term tc_at_birth(Term space, Term t);        /* located birth-marker pattern/term: t birthing space */
Occ  tc_post_at(Term space, Term t, bool marker);
Term tc_occ_space(Occ o);                    /* space Term of occurrence o */
bool tc_occ_marker(Occ o);                   /* true iff o is a space birth marker */
bool tc_space_born(Term space);              /* true iff space has a live birth marker in W */
void tc_set_handle_con(int con);             /* unary constructor handle(s) carrying space reach */
int  tc_reach(const Term *seeds, int nseed, Term *out, int cap);
Occ  tc_fire_reach(int rule, const Occ *take, const Occ *keep, const Term *inst,
                   const Term *seeds, int nseed);
Occ  tc_search_reach(int rule, const Term *seeds, int nseed);
Occ  tc_last_extra(int idx);                 /* extra made occurrence idx (0..3) of last firing */

/* ---- Row 6: ProgramReflection & ProgramBindersQuoted ---- */
void tc_set_quote_con(int quote_con, int activate_con, int lam_con, int app_con);
Term tc_active_step(Term t);                 /* one active-context step (beta or activate-quote; quote inert) */
Term tc_active_norm(Term t, int max_steps);  /* normalize in active contexts (0 if stuck/diverged) */
Occ  tc_active_step_occ(Occ o);              /* one active-context step on a board occurrence */

/* ---- Row 7: RhoContinuation & ContextualCommunicationReflection ---- */
void tc_set_rho_con(int quote_con, int drop_con, bool allow_proc_drop);
Term tc_rho_norm_name(Term t);               /* normalize Name-sort quote(drop(n)) = n */
Occ  tc_rho_step_occ(Occ o);                 /* Process-sort drop(quote(P)) -> P (gated by allow_proc_drop) */
Term tc_rho_comm(Term ch_out, Term ch_in, Term payload_proc,
                 Term cont_pat, int var_name, int var_proc);

/* ---- Modular Prepared-Step & Cursor Interface (CeTTa <-> tcalc Bridge) ----
 * 1. Candidate / PreparedStep: proposed by an external cursor/index (e.g. CeTTa
 *    hash-consed SpaceMatchBackend or a candidate generator).
 * 2. Admission & Commit (tc_commit_prepared): tcalc checks the prepared step in
 *    <K ; W>, consumes linear takes, mints fresh names/births, and populates a
 *    TcAdmissionReceipt only when admitted (refused candidates leave no receipt). */
typedef struct {
  int        rule;
  const Occ *take;      /* optional array of ntake occurrence IDs (NULL if ntake == 0) */
  const Occ *keep;      /* optional array of nkeep occurrence IDs (NULL if nkeep == 0) */
  const Term *inst;     /* optional hole binding array (NULL if inferred from premises) */
  Occ        dest;      /* optional destination slot for FIBRE_FLAT rules (0 = new occ) */
  int        nseeds;    /* optional reachability root count (> 0 uses tc_fire_reach) */
  const Term *seeds;    /* optional reachability root seeds */
} TcPreparedStep;

typedef struct {
  bool    admitted;     /* true iff admission succeeded */
  int     rule;
  Occ     out;          /* primary made occurrence (0 if refused) */
  uint8_t nextra;
  Occ     extra[4];     /* extra made occurrences (0..3) */
  Term    out_term;     /* primary made Term (0 if refused or flat-only slot) */
} TcAdmissionReceipt;

typedef struct TcCandidateCursor {
  void *ctx;
  bool (*next)(void *ctx, TcPreparedStep *out);
} TcCandidateCursor;

bool tc_commit_prepared(const TcPreparedStep *step, TcAdmissionReceipt *receipt);
int  tc_step_cursor(TcCandidateCursor *cursor, TcAdmissionReceipt *receipt);

