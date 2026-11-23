/* Unit tests for the tcalc kernel beyond the MM0 and Micromath suites. */
#include <stdio.h>
#include <stdlib.h>
#include "tcalc.h"

static int checks;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "FAIL line %d: %s\n", __LINE__, #c); exit(1); } checks++; } while (0)

static int WFF, VAR, IM, AL, P, Q, PX;
static Term im(Term a, Term b) { Term x[2] = { a, b }; return tc_app(IM, x); }
static Term al(Term x, Term a) { Term y[2] = { x, a }; return tc_app(AL, y); }
static Term c0(int con) { return tc_app(con, NULL); }
static bool mock_cursor_next(void *ctx, TcPreparedStep *out);
typedef struct {
  int idx, count;
  TcPreparedStep items[4];
} MockCursor;
static bool mock_cursor_next(void *ctx, TcPreparedStep *out) {
  MockCursor *m = (MockCursor *)ctx;
  if (m->idx >= m->count) return false;
  *out = m->items[m->idx++];
  return true;
}

static Term px(Term x) { return tc_app(PX, &x); }

int main(void) {
  CHECK(tc_init(1u << 16, 1u << 10));
  WFF = tc_sort(SORT_PROVABLE); VAR = tc_sort(0);
  int STRICT = tc_sort(SORT_STRICT), PURE = tc_sort(SORT_PURE);
  Binder ww[2] = { { (uint16_t)WFF, 0, 0 }, { (uint16_t)WFF, 0, 0 } };
  Binder xa[2] = { { (uint16_t)VAR, 1, 0 }, { (uint16_t)WFF, 0, 1 } };          /* al {x} (a: wff x) */
  Binder xv = { (uint16_t)VAR, 0, 0 };
  IM = tc_con((uint16_t)WFF, 0, 2, ww); AL = tc_con((uint16_t)WFF, 0, 2, xa);
  P = tc_con((uint16_t)WFF, 0, 0, NULL); Q = tc_con((uint16_t)WFF, 0, 0, NULL); PX = tc_con((uint16_t)WFF, 0, 1, &xv);
  CHECK(IM >= 0 && AL >= 0 && P >= 0 && Q >= 0 && PX >= 0);
  Binder bad_bound = { (uint16_t)STRICT, 1, 0 };
  CHECK(tc_con((uint16_t)WFF, 0, 1, &bad_bound) == -1);                       /* no binders over a strict sort */
  CHECK(tc_con((uint16_t)PURE, 0, 0, NULL) == -1);                            /* no constructors in a pure sort */
  Term p = c0(P), q = c0(Q);
  CHECK(tc_app(IM, (Term[]){ p, tc_name((uint16_t)VAR, 0) }) == 0);          /* sorts are checked */
  CHECK(al(tc_name((uint16_t)VAR, 0), p) == 0);                               /* bound position requires bound var */

  /* Hilbert with ax5. Context: a b c wff, x bound, f wff not depending on x. */
  Binder ctx[5] = { { (uint16_t)WFF, 0, 0 }, { (uint16_t)WFF, 0, 0 }, { (uint16_t)WFF, 0, 0 },
                    { (uint16_t)VAR, 1, 0 }, { (uint16_t)WFF, 0, 0 } };
  CHECK(tc_ctx(5, ctx));
  Term A = tc_v(0), B = tc_v(1), Cc = tc_v(2), X = tc_v(3), F = tc_v(4);
  Rule a1 = { .make = { im(A, im(B, A)), 0 }, .fresh = -1 };
  Rule a2 = { .make = { im(im(A, im(B, Cc)), im(im(A, B), im(A, Cc))), 0 }, .fresh = -1 };
  Rule mp = { .nkeep = 2, .keep = { { A, 0 }, { im(A, B), 0 } }, .make = { B, 0 }, .fresh = -1 };
  Rule ax5 = { .make = { im(F, al(X, F)), 0 }, .fresh = -1 };             /* x apart from f: from the context */
  int r1 = tc_rule(&a1), r2 = tc_rule(&a2), rmp = tc_rule(&mp), r5 = tc_rule(&ax5);
  CHECK(r1 >= 0 && r2 >= 0 && rmp >= 0 && r5 >= 0);

  Term pp = im(p, p);
  Occ s0 = tc_fire(r1, NULL, NULL, (Term[5]){ p, pp }), s1 = tc_fire(r2, NULL, NULL, (Term[5]){ p, pp, p });
  Occ s2 = tc_fire(rmp, NULL, (Occ[]){ s0, s1 }, NULL), s3 = tc_fire(r1, NULL, NULL, (Term[5]){ p, p });
  Occ s4 = tc_fire(rmp, NULL, (Occ[]){ s3, s2 }, NULL);
  CHECK(s4 && tc_term(s4) == pp);
  CHECK(!tc_fire(rmp, NULL, (Occ[]){ s2, s3 }, NULL));                         /* swapped premises */
  Term x0 = tc_bv((uint16_t)VAR, 0);
  CHECK(tc_fire(r5, NULL, NULL, (Term[5]){ [3] = x0, [4] = p }));
  CHECK(!tc_fire(r5, NULL, NULL, (Term[5]){ [3] = x0, [4] = px(x0) }));       /* x occurs in f */
  CHECK(!tc_fire(r5, NULL, NULL, (Term[5]){ [3] = tc_name((uint16_t)VAR, 0), [4] = p })); /* x must be bound */
  CHECK(!tc_fire(r1, NULL, NULL, (Term[5]){ A, p }));                         /* the board is closed */
  CHECK(!tc_fire(r1, NULL, NULL, (Term[5]){ tc_name((uint16_t)VAR, 0), p })); /* a: wff, given a var name */
  CHECK(!tc_fire(rmp, NULL, (Occ[]){ 9999, s3 }, NULL));                      /* no such premise */
  Occ wrong_space = tc_post(2, tc_term(s2));
  CHECK(wrong_space && !tc_fire(rmp, NULL, (Occ[]){ s3, wrong_space }, NULL)); /* premise in another space */
  Term zm = tc_meta();
  Occ open_occ = tc_post(0, im(zm, p));                                        /* an unknown in a wff position */
  CHECK(tc_ctx(2, ww));
  Rule swap = { .nkeep = 1, .keep = { { im(tc_v(0), tc_v(1)), 0 } }, .make = { im(tc_v(1), tc_v(0)), 0 }, .fresh = -1 };
  int rsw = tc_rule(&swap);
  CHECK(rsw >= 0 && open_occ && !tc_fire(rsw, NULL, (Occ[]){ open_occ }, NULL)); /* a := $z is not yet a wff */
  CHECK(tc_fire(rmp, NULL, (Occ[]){ s3, open_occ }, NULL));                   /* reading it tells $z := a */
  CHECK(tc_deref(zm) == tc_term(s3));

  /* EXTEND: a fresh name of sort var, defined from existing names only. */
  Binder dctx[2] = { { (uint16_t)VAR, 0, 0 }, { (uint16_t)VAR, 0, 0 } };
  CHECK(tc_ctx(2, dctx));
  Binder vv[2] = { { (uint16_t)VAR, 0, 0 }, { (uint16_t)VAR, 0, 0 } };
  int DEFEQ = tc_con((uint16_t)WFF, 0, 2, vv);
  Rule rdef = { .make = { tc_app(DEFEQ, (Term[]){ tc_v(0), tc_v(1) }), 0 }, .fresh = 0 };
  int rd = tc_rule(&rdef);
  uint64_t k = tc_fresh_name();
  CHECK(rd >= 0 && tc_fire(rd, NULL, NULL, (Term[2]){ 0, tc_name((uint16_t)VAR, k) }) && tc_next_name() == k + 2);
  CHECK(!tc_fire(rd, NULL, NULL, (Term[2]){ 0, tc_name((uint16_t)VAR, k + 2) }));   /* names itself */
  CHECK(!tc_fire(rd, NULL, NULL, (Term[2]){ tc_name((uint16_t)VAR, 0), tc_name((uint16_t)VAR, k) })); /* chosen name */
  Rule rvar = { .make = { tc_name((uint16_t)VAR, k), 0 }, .fresh = -1 };      /* a trusted rule making data */
  int rv = tc_rule(&rvar);
  CHECK(rv >= 0);

  /* Definitions and conversion on the board: dn a := (a -> a). */
  CHECK(tc_ctx(1, ww));
  int DN = tc_def((uint16_t)WFF, 0, 1, 0, im(tc_v(0), tc_v(0)));
  CHECK(DN >= 0);
  Term dnp = tc_app(DN, &p);
  Conv refl_p = { .kind = CV_REFL, .t = p };
  Conv unf = { .kind = CV_UNFOLD, .con = DN, .args = &p, .dummies = NULL, .kid = &(Conv){ .kind = CV_REFL, .t = pp } };
  Occ c1 = tc_convert(s4, &unf, dnp);                                         /* |- p -> p  gives  |- dn p */
  CHECK(c1 && tc_term(c1) == dnp);
  Conv wrong = { .kind = CV_UNFOLD, .con = DN, .args = &q, .kid = &(Conv){ .kind = CV_REFL, .t = im(q, q) } };
  CHECK(!tc_convert(s4, &wrong, tc_app(DN, &q)));
  (void)refl_p;
  /* a definition whose body mentions a bound dummy free is refused */
  Binder dd[2] = { { (uint16_t)WFF, 0, 0 }, { (uint16_t)VAR, 1, 0 } };
  CHECK(tc_ctx(2, dd));
  CHECK(tc_def((uint16_t)WFF, 0, 1, 1, im(tc_v(0), px(tc_v(1)))) == -1);
  int D2 = tc_def((uint16_t)WFF, 0, 1, 1, al(tc_v(1), im(tc_v(0), px(tc_v(1)))));    /* bound by al */
  CHECK(D2 >= 0);
  Term px0 = px(x0), d2px0 = tc_app(D2, &px0), bad_rhs = al(x0, im(px0, px0));
  Occ o_d2 = tc_post(0, d2px0);
  Conv bad_cap = { .kind = CV_UNFOLD, .con = D2, .args = &px0, .dummies = &x0, .kid = &(Conv){ .kind = CV_REFL, .t = bad_rhs } };
  CHECK(o_d2 && !tc_convert(o_d2, &bad_cap, bad_rhs));                         /* dummy x0 captured by arg px(x0) */
  CHECK(!tc_fire(rsw, NULL, (Occ[]){ o_d2 }, NULL));                           /* flat rule checks constructor head */

  /* SHARE: id lemma checked once in context (a: wff), then one firing per use. */
  CHECK(tc_ctx(5, ctx));
  Step id[5] = {
    { .kind = ST_RULE, .rule = r1, .inst = (Term[5]){ A, im(A, A) } },
    { .kind = ST_RULE, .rule = r2, .inst = (Term[5]){ A, im(A, A), A } },
    { .kind = ST_RULE, .rule = rmp, .prem = { 0, 1 } },
    { .kind = ST_RULE, .rule = r1, .inst = (Term[5]){ A, A } },
    { .kind = ST_RULE, .rule = rmp, .prem = { 3, 2 } },
  };
  tc_seal();
  CHECK(tc_rule(&a1) == -1);                                                   /* sealed: no new axioms */
  CHECK(tc_promote(1, 0, 0, NULL, im(A, A), id, 5) == -1);                    /* b..f would be dummies, not bound */
  CHECK(tc_ctx(0, NULL));
  Step mkv = { .kind = ST_RULE, .rule = rv, .inst = (Term[2]){ 0 } };
  CHECK(tc_promote(0, 0, 0, NULL, tc_name((uint16_t)VAR, k), &mkv, 1) == -1);  /* a lemma states a provable sort */
  Term nk = tc_name((uint16_t)VAR, k);
  Step mk_imp = { .kind = ST_RULE, .rule = rd, .inst = (Term[2]){ nk, nk } };
  CHECK(tc_promote(0, 0, 0, NULL, tc_app(DEFEQ, (Term[]){ nk, nk }), &mk_imp, 1) == -1); /* impure rule refused in lemma */
  CHECK(tc_ctx(1, ctx));                                                       /* context: (a: wff) */
  int lid = tc_promote(1, 0, 0, NULL, im(A, A), id, 5);
  CHECK(lid >= 0);
  Occ u = tc_fire(lid, NULL, NULL, (Term[1]){ im(p, q) });
  CHECK(u && tc_term(u) == im(im(p, q), im(p, q)));
  CHECK(tc_ctx(2, ctx));                                                       /* context: (a b: wff) */
  CHECK(tc_promote(2, 0, 0, NULL, im(A, B), id, 5) == -1);                    /* proves a -> a, not a -> b */
  Step peek = { .kind = ST_RULE, .rule = rmp, .prem = { -1, -1 } };
  CHECK(tc_promote(2, 0, 1, (Term[]){ A }, B, &peek, 1) == -1);               /* cannot look inside a */
  CHECK(tc_ctx(5, ctx));
  /* the separation inside ax5 follows from the context: f must not depend on x */
  Step g = { .kind = ST_RULE, .rule = r5, .inst = (Term[5]){ [3] = X, [4] = F } };
  CHECK(tc_promote(5, 0, 0, NULL, im(F, al(X, F)), &g, 1) >= 0);
  Binder dep[5] = { { (uint16_t)WFF, 0, 0 }, { (uint16_t)WFF, 0, 0 }, { (uint16_t)WFF, 0, 0 },
                    { (uint16_t)VAR, 1, 0 }, { (uint16_t)WFF, 0, 8 } };          /* f depends on x */
  CHECK(tc_ctx(5, dep));
  Step g2 = { .kind = ST_RULE, .rule = r5, .inst = (Term[5]){ [3] = tc_v(3), [4] = tc_v(4) } };
  CHECK(tc_promote(5, 0, 0, NULL, im(tc_v(4), al(tc_v(3), tc_v(4))), &g2, 1) == -1);
  CHECK(tc_post(0, q));                                                        /* an unprotected space */
  tc_protect(1);
  CHECK(!tc_post(1, q));                                                       /* sealed and protected */

  /* The transform part: take, tells, occurs check, absence at every solution, disequations. */
  CHECK(tc_init(1u << 16, 1u << 10));
  int D = tc_sort(0);
  Binder one = { (uint16_t)D, 0, 0 };
  int REQ = tc_con((uint16_t)D, 0, 1, &one), DONE = tc_con((uint16_t)D, 0, 1, &one), PP = tc_con((uint16_t)D, 0, 1, &one);
  int CA = tc_con((uint16_t)D, 0, 0, NULL), CB = tc_con((uint16_t)D, 0, 0, NULL), F1 = tc_con((uint16_t)D, 0, 1, &one);
  Term a = c0(CA), b = c0(CB), Z = tc_meta();
  CHECK(tc_ctx(1, &one));
  Term V = tc_v(0);
  Rule rt = { .ntake = 1, .take = { { tc_app(REQ, &V), 0 } }, .ntell = 1, .tell = { { Z, V } },
              .make = { tc_app(DONE, &V), 0 }, .fresh = -1 };
  int it = tc_rule(&rt);
  Occ o1 = tc_post(0, tc_app(REQ, &a));
  Rule rt2 = { .ntake = 2, .take = { { tc_app(REQ, &V), 0 }, { tc_app(REQ, &V), 0 } },
               .make = { tc_app(DONE, &V), 0 }, .fresh = -1 };
  Rule rtk_alias = { .ntake = 1, .take = { { tc_app(REQ, &V), 0 } }, .nkeep = 1, .keep = { { tc_app(REQ, &V), 0 } },
                     .make = { tc_app(DONE, &V), 0 }, .fresh = -1 };
  int it2 = tc_rule(&rt2), itk_alias = tc_rule(&rtk_alias);
  CHECK(it2 >= 0 && !tc_fire(it2, (Occ[]){ o1, o1 }, NULL, NULL));            /* take multiset aliasing refused */
  CHECK(itk_alias >= 0 && !tc_fire(itk_alias, (Occ[]){ o1 }, (Occ[]){ o1 }, NULL)); /* take-keep aliasing refused */
  CHECK(it >= 0 && o1 && tc_fire(it, (Occ[]){ o1 }, NULL, NULL) && tc_deref(Z) == a);
  CHECK(!tc_alive(o1) && !tc_fire(it, (Occ[]){ o1 }, NULL, NULL));          /* taken once */
  Term M = tc_meta();
  CHECK(!tc_tell(M, tc_app(F1, &M)));                                         /* occurs check */
  Term pa = tc_app(PP, &a);
  Rule ra = { .nabsent = 1, .absent = { { pa, 0 } }, .make = { c0(CB), 0 }, .fresh = -1 };
  int iab = tc_rule(&ra);
  CHECK(iab >= 0);
  Occ op = tc_post(0, pa);
  CHECK(!tc_fire(iab, NULL, NULL, NULL));                                     /* (p a) present */
  CHECK(tc_init(1u << 16, 1u << 10));
  D = tc_sort(0); one = (Binder){ (uint16_t)D, 0, 0 };
  PP = tc_con((uint16_t)D, 0, 1, &one); CA = tc_con((uint16_t)D, 0, 0, NULL); CB = tc_con((uint16_t)D, 0, 0, NULL);
  a = c0(CA); b = c0(CB); pa = tc_app(PP, &a);
  CHECK(tc_ctx(0, NULL));
  ra = (Rule){ .nabsent = 1, .absent = { { pa, 0 } }, .make = { b, 0 }, .fresh = -1 };
  iab = tc_rule(&ra);
  op = tc_post(0, tc_app(PP, &b));
  CHECK(op && tc_fire(iab, NULL, NULL, NULL));                                /* only (p b): admitted */
  Term Zm = tc_meta();
  op = tc_post(0, tc_app(PP, &Zm));
  CHECK(op && !tc_fire(iab, NULL, NULL, NULL));                               /* (p $z): $z = a is a solution */
  CHECK(tc_tell_neq(Zm, a));
  CHECK(tc_fire(iab, NULL, NULL, NULL));                                      /* $z != a: no solution has (p a) */
  CHECK(!tc_tell(Zm, a));                                                     /* the disequation holds */

  /* ---- Lean Interface.Step Conformance Gate ---- */
  /* 1. Evidence.Family (Step/EvidenceInterfaceFamily.lean):
        4 members (covered, refuted, incomplete, disequal) x 4 probes (absentP, readOpp, bindA, findP)
        plus universal count(p(a), 0) == absent(p(a)). */
  static const uint8_t ev_want[4][4] = {
    { 1, 0, 1, 0 }, /* covered:    no rows          -> absentP=1, readOpp=0, bindA=1, findP=0 */
    { 1, 1, 1, 0 }, /* refuted:    row opp(a)       -> absentP=1, readOpp=1, bindA=1, findP=0 */
    { 0, 0, 1, 1 }, /* incomplete: row p(X), X open -> absentP=0, readOpp=0, bindA=1, findP=1 */
    { 1, 0, 0, 0 }, /* disequal:   row p(X), X != a -> absentP=1, readOpp=0, bindA=0, findP=0 */
  };
  uint8_t ev_mask[4] = { 0, 0, 0, 0 };
  for (int m = 0; m < 4; m++) {
    for (int pr = 0; pr < 5; pr++) {
      CHECK(tc_init(1u << 12, 1u << 8));
      D = tc_sort(0); one = (Binder){ (uint16_t)D, 0, 0 };
      PP = tc_con((uint16_t)D, 0, 1, &one);
      int OPP = tc_con((uint16_t)D, 0, 1, &one);
      CA = tc_con((uint16_t)D, 0, 0, NULL); CB = tc_con((uint16_t)D, 0, 0, NULL);
      a = c0(CA); b = c0(CB); pa = tc_app(PP, &a);
      Term oppa = tc_app(OPP, &a), Xm = tc_meta(), pxm = tc_app(PP, &Xm);
      CHECK(tc_ctx(0, NULL));
      Occ row1 = m == 1 ? tc_post(0, oppa) : 0;
      Occ row2 = m >= 2 ? tc_post(0, pxm) : 0;
      if (m == 3) CHECK(tc_tell_neq(Xm, a));
      Rule rp = { .make = { b, 0 }, .fresh = -1 };
      if (pr == 0) { rp.nabsent = 1; rp.absent[0] = (Pat){ pa, 0 }; }
      else if (pr == 1) { rp.nkeep = 1; rp.keep[0] = (Pat){ oppa, 0 }; }
      else if (pr == 2) { rp.ntell = 1; rp.tell[0][0] = Xm; rp.tell[0][1] = a; }
      else if (pr == 3) { rp.nkeep = 1; rp.keep[0] = (Pat){ pa, 0 }; }
      else { rp.ncount = 1; rp.count[0] = (Count){ pa, 0, 0 }; }
      int ir = tc_rule(&rp);
      CHECK(ir >= 0);
      Occ keep_occ = pr == 1 ? row1 : (pr == 3 ? row2 : 0);
      bool got = tc_fire(ir, NULL, (pr == 1 || pr == 3) ? &keep_occ : NULL, NULL) != 0;
      bool want = ev_want[m][pr < 4 ? pr : 0] != 0;
      CHECK(got == want);
      if (pr < 4 && got) ev_mask[m] |= (uint8_t)(1u << pr);
    }
  }
  for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) CHECK(ev_mask[i] != ev_mask[j]);

  /* 2. DisequalityFramesControls (Step/DisequalityFramesControls.lean):
        DependentTell: tellApart_admitted, identify_refused, identify_admitted_without, compatible_admitted.
        ContextualTell: makeHelper (H = 7), apartSeven_refused, apartEight_admitted. */
  CHECK(tc_init(1u << 12, 1u << 8));
  D = tc_sort(0); one = (Binder){ (uint16_t)D, 0, 0 };
  Binder two[2] = { one, one };
  int ARR = tc_con((uint16_t)D, 0, 2, two), GND = tc_con((uint16_t)D, 0, 0, NULL);
  Term gnd = c0(GND), arr_gg = tc_app(ARR, (Term[]){ gnd, gnd }), Xd = tc_meta();
  CHECK(tc_ctx(0, NULL));
  Rule r_tell_apart = { .nneq = 1, .neq = { { Xd, arr_gg } }, .make = { gnd, 0 }, .fresh = -1 };
  Rule r_identify   = { .ntell = 1, .tell = { { Xd, arr_gg } }, .make = { gnd, 0 }, .fresh = -1 };
  Rule r_compat     = { .ntell = 1, .tell = { { Xd, gnd } }, .make = { gnd, 0 }, .fresh = -1 };
  int i_ta = tc_rule(&r_tell_apart), i_id = tc_rule(&r_identify), i_cm = tc_rule(&r_compat);
  CHECK(i_ta >= 0 && i_id >= 0 && i_cm >= 0);
  CHECK(tc_fire(i_ta, NULL, NULL, NULL));                                     /* tellApart_admitted */
  CHECK(!tc_fire(i_id, NULL, NULL, NULL));                                    /* identify_refused */
  CHECK(tc_fire(i_cm, NULL, NULL, NULL) && tc_deref(Xd) == gnd);              /* compatible_admitted */
  CHECK(tc_init(1u << 12, 1u << 8));
  D = tc_sort(0); one = (Binder){ (uint16_t)D, 0, 0 };
  two[0] = two[1] = one;
  ARR = tc_con((uint16_t)D, 0, 2, two); GND = tc_con((uint16_t)D, 0, 0, NULL);
  gnd = c0(GND); arr_gg = tc_app(ARR, (Term[]){ gnd, gnd }); Xd = tc_meta();
  CHECK(tc_ctx(0, NULL));
  r_identify = (Rule){ .ntell = 1, .tell = { { Xd, arr_gg } }, .make = { gnd, 0 }, .fresh = -1 };
  i_id = tc_rule(&r_identify);
  CHECK(i_id >= 0 && tc_fire(i_id, NULL, NULL, NULL) && tc_deref(Xd) == arr_gg); /* identify_admitted_without */
  /* ContextualTell: helper H valued 7, apartFrom(7) refused, apartFrom(8) admitted. */
  for (int t = 0; t < 9; t++) tc_fresh_name();
  Term H = tc_meta(), c7 = tc_name((uint16_t)D, 7), c8 = tc_name((uint16_t)D, 8);
  CHECK(tc_ctx(1, &one));
  Rule r_mk_helper = { .ntell = 1, .tell = { { H, c7 } }, .make = { tc_v(0), 0 }, .fresh = 0 };
  Rule r_apart7    = { .nneq = 1, .neq = { { H, c7 } }, .make = { tc_v(0), 0 }, .fresh = 0 };
  Rule r_apart8    = { .nneq = 1, .neq = { { H, c8 } }, .make = { tc_v(0), 0 }, .fresh = 0 };
  int i_mh = tc_rule(&r_mk_helper), i_a7 = tc_rule(&r_apart7), i_a8 = tc_rule(&r_apart8);
  CHECK(i_mh >= 0 && i_a7 >= 0 && i_a8 >= 0);
  CHECK(tc_fire(i_mh, NULL, NULL, NULL));                                     /* makeHelper_admitted */
  CHECK(!tc_fire(i_a7, NULL, NULL, NULL));                                    /* apartSeven_refused */
  CHECK(tc_fire(i_a8, NULL, NULL, NULL));                                     /* apartEight_admitted */

  /* 3. CanonicalFirstOrder Controls (Step/CanonicalFirstOrder.lean):
        hollow_cube_never_round (pairwise consistent tells that are jointly inconsistent in all 6 orders),
        clique_explored_once (3 producers in all 6 orders),
        dependent_pair_kept (watcher-before-writer admitted, writer-before-watcher refused). */
  static const int perms[6][3] = { {0,1,2}, {0,2,1}, {1,0,2}, {1,2,0}, {2,0,1}, {2,1,0} };
  for (int p_idx = 0; p_idx < 6; p_idx++) {
    CHECK(tc_init(1u << 12, 1u << 8));
    D = tc_sort(0); CA = tc_con((uint16_t)D, 0, 0, NULL); CB = tc_con((uint16_t)D, 0, 0, NULL);
    a = c0(CA); b = c0(CB);
    Term Xc = tc_meta(), Yc = tc_meta();
    CHECK(tc_ctx(0, NULL));
    Rule hc[3] = {
      { .ntell = 1, .tell = { { Xc, Yc } }, .make = { a, 0 }, .fresh = -1 },
      { .ntell = 1, .tell = { { Xc, a } },  .make = { a, 0 }, .fresh = -1 },
      { .ntell = 1, .tell = { { Yc, b } },  .make = { a, 0 }, .fresh = -1 },
    };
    int rhc[3] = { tc_rule(&hc[0]), tc_rule(&hc[1]), tc_rule(&hc[2]) };
    CHECK(tc_fire(rhc[perms[p_idx][0]], NULL, NULL, NULL));                   /* 1st of pair admitted */
    CHECK(tc_fire(rhc[perms[p_idx][1]], NULL, NULL, NULL));                   /* 2nd of pair admitted (all 6 pairs!) */
    CHECK(!tc_fire(rhc[perms[p_idx][2]], NULL, NULL, NULL));                  /* 3rd always refused (hollow cube!) */
  }
  /* dependent_pair_kept: watcher checks absent(p(a)), writer makes p(a) */
  for (int order = 0; order < 2; order++) {
    CHECK(tc_init(1u << 12, 1u << 8));
    D = tc_sort(0); one = (Binder){ (uint16_t)D, 0, 0 };
    PP = tc_con((uint16_t)D, 0, 1, &one); CA = tc_con((uint16_t)D, 0, 0, NULL); CB = tc_con((uint16_t)D, 0, 0, NULL);
    a = c0(CA); b = c0(CB); pa = tc_app(PP, &a);
    CHECK(tc_ctx(0, NULL));
    Rule r_watcher = { .nabsent = 1, .absent = { { pa, 0 } }, .make = { b, 0 }, .fresh = -1 };
    Rule r_writer  = { .make = { pa, 0 }, .fresh = -1 };
    int iw = tc_rule(&r_watcher), iwr = tc_rule(&r_writer);
    if (order == 0) {
      CHECK(tc_fire(iw, NULL, NULL, NULL) && tc_fire(iwr, NULL, NULL, NULL)); /* watcher then writer: admitted */
    } else {
      CHECK(tc_fire(iwr, NULL, NULL, NULL) && !tc_fire(iw, NULL, NULL, NULL)); /* writer then watcher: refused */
    }
  }

  /* 4. Universal Count Query Controls (ContextualPrincipalCountQueries.lean):
        - exact count 1, 2 on multiset board
        - principal table cardinality 1 + ambiguous open occurrence p(X) -> refused!
        - disequation X != a excludes p(X) -> count 1 admitted!
        - query-local existential count(p(?v), 1) on {p(X)} -> admitted!
        - nonlinear query-local existential count(pair(?v, ?v), 1) on {pair(X, Y)} -> refused! */
  CHECK(tc_init(1u << 12, 1u << 8));
  D = tc_sort(0); one = (Binder){ (uint16_t)D, 0, 0 };
  two[0] = two[1] = one;
  PP = tc_con((uint16_t)D, 0, 1, &one);
  int PAIR = tc_con((uint16_t)D, 0, 2, two);
  CA = tc_con((uint16_t)D, 0, 0, NULL); CB = tc_con((uint16_t)D, 0, 0, NULL);
  a = c0(CA); b = c0(CB); pa = tc_app(PP, &a);
  CHECK(tc_ctx(1, &one));
  V = tc_v(0);
  Rule rc0 = { .ncount = 1, .count = { { pa, 0, 0 } }, .make = { b, 0 }, .fresh = -1 };
  Rule rc1 = { .ncount = 1, .count = { { pa, 0, 1 } }, .make = { b, 0 }, .fresh = -1 };
  Rule rc2 = { .ncount = 1, .count = { { pa, 0, 2 } }, .make = { b, 0 }, .fresh = -1 };
  Rule rce = { .ncount = 1, .count = { { tc_app(PP, &V), 0, 1 } }, .make = { b, 0 }, .fresh = -1 };
  Rule rcp = { .ncount = 1, .count = { { tc_app(PAIR, (Term[]){ V, V }), 0, 1 } }, .make = { b, 0 }, .fresh = -1 };
  Rule rtk = { .ntake = 1, .take = { { pa, 0 } }, .make = { b, 0 }, .fresh = -1 };
  int ic0 = tc_rule(&rc0), ic1 = tc_rule(&rc1), ic2 = tc_rule(&rc2), ice = tc_rule(&rce), icp = tc_rule(&rcp), itk = tc_rule(&rtk);
  CHECK(ic0 >= 0 && ic1 >= 0 && ic2 >= 0 && ice >= 0 && icp >= 0 && itk >= 0);
  CHECK(tc_fire(ic0, NULL, NULL, NULL) && !tc_fire(ic1, NULL, NULL, NULL));   /* empty: count=0 */
  Occ o_pa1 = tc_post(0, pa);
  CHECK(o_pa1 && !tc_fire(ic0, NULL, NULL, NULL) && tc_fire(ic1, NULL, NULL, NULL) && !tc_fire(ic2, NULL, NULL, NULL));
  Occ o_pa2 = tc_post(0, pa);                                                 /* multiset: second p(a) */
  CHECK(o_pa2 && o_pa2 != o_pa1 && !tc_fire(ic1, NULL, NULL, NULL) && tc_fire(ic2, NULL, NULL, NULL));
  CHECK(tc_fire(itk, (Occ[]){ o_pa2 }, NULL, NULL) && tc_alive(o_pa1) && !tc_alive(o_pa2));
  CHECK(tc_fire(ic1, NULL, NULL, NULL));                                      /* back to count=1 */
  Term Xk = tc_meta(), Yk = tc_meta();
  Occ o_px = tc_post(0, tc_app(PP, &Xk));
  CHECK(o_px && !tc_fire(ic1, NULL, NULL, NULL));                             /* p(X) open: count(p(a),1) REFUSED */
  CHECK(!tc_fire(ic2, NULL, NULL, NULL));                                     /* count(p(a),2) also REFUSED */
  CHECK(tc_fire(ice, (Occ[]){}, NULL, NULL) == 0);                            /* 2 occurrences match p(?v): count=1 refused */
  CHECK(tc_tell_neq(Xk, a));
  CHECK(tc_fire(ic1, NULL, NULL, NULL));                                      /* X != a: count(p(a),1) ADMITTED! */
  CHECK(tc_fire(itk, (Occ[]){ o_pa1 }, NULL, NULL));                          /* remove p(a); only p(X) remains */
  CHECK(tc_fire(ice, NULL, NULL, NULL));                                      /* {p(X)}: count(p(?v),1) ADMITTED! */
  Occ o_xy = tc_post(0, tc_app(PAIR, (Term[]){ Xk, Yk }));
  CHECK(o_xy && !tc_fire(icp, NULL, NULL, NULL));                             /* {pair(X,Y)}: count(pair(?v,?v),1) REFUSED! */
  CHECK(tc_tell(Xk, Yk) && tc_fire(icp, NULL, NULL, NULL));                   /* after X=Y: count(pair(?v,?v),1) ADMITTED! */

  /* ---- R113 Adversarial Regression & Fast-Path vs. Slow-Path Differential Gate ---- */
  /* 5. Fibre classification tags (tc_rule_fibre) + premise-order invariance + fast-vs-slow lockstep. */
  CHECK(tc_init(1u << 16, 1u << 12));
  WFF = tc_sort(SORT_PROVABLE); VAR = tc_sort(0);
  ww[0] = ww[1] = (Binder){ (uint16_t)WFF, 0, 0 };
  xa[0] = (Binder){ (uint16_t)VAR, 1, 0 }; xa[1] = (Binder){ (uint16_t)WFF, 0, 1 };
  IM = tc_con((uint16_t)WFF, 0, 2, ww); AL = tc_con((uint16_t)WFF, 0, 2, xa);
  P = tc_con((uint16_t)WFF, 0, 0, NULL); Q = tc_con((uint16_t)WFF, 0, 0, NULL);
  p = c0(P); q = c0(Q);
  CHECK(tc_ctx(5, ctx));
  A = tc_v(0); B = tc_v(1); Cc = tc_v(2); X = tc_v(3); F = tc_v(4);
  Rule r_ax1  = { .make = { im(A, im(B, A)), 0 }, .fresh = -1 };
  Rule r_ax5  = { .make = { im(F, al(X, F)), 0 }, .fresh = -1 };
  Rule r_lin  = { .nkeep = 1, .keep = { { im(A, B), 0 } }, .make = { im(B, A), 0 }, .fresh = -1 };
  Rule r_mp1  = { .nkeep = 2, .keep = { { A, 0 }, { im(A, B), 0 } }, .make = { B, 0 }, .fresh = -1 };
  Rule r_mp2  = { .nkeep = 2, .keep = { { im(A, B), 0 }, { A, 0 } }, .make = { B, 0 }, .fresh = -1 };
  Rule r_mps1 = { .nkeep = 2, .keep = { { A, 0 }, { im(A, B), 0 } }, .ntell = 1, .tell = { { p, p } }, .make = { B, 0 }, .fresh = -1 };
  Rule r_mps2 = { .nkeep = 2, .keep = { { im(A, B), 0 }, { A, 0 } }, .ntell = 1, .tell = { { p, p } }, .make = { B, 0 }, .fresh = -1 };
  /* Flat rule where make builds im(B, A) so k->flat = true, plus its reversed and slow-oracle twins: */
  Rule r_fl1  = { .nkeep = 2, .keep = { { im(A, Cc), 0 }, { im(A, B), 0 } }, .make = { im(B, Cc), 0 }, .fresh = -1 };
  Rule r_fl2  = { .nkeep = 2, .keep = { { im(A, B), 0 }, { im(A, Cc), 0 } }, .make = { im(B, Cc), 0 }, .fresh = -1 };
  Rule r_fls1 = { .nkeep = 2, .keep = { { im(A, Cc), 0 }, { im(A, B), 0 } }, .ntell = 1, .tell = { { p, p } }, .make = { im(B, Cc), 0 }, .fresh = -1 };
  Rule r_fls2 = { .nkeep = 2, .keep = { { im(A, B), 0 }, { im(A, Cc), 0 } }, .ntell = 1, .tell = { { p, p } }, .make = { im(B, Cc), 0 }, .fresh = -1 };
  int iax1 = tc_rule(&r_ax1), iax5 = tc_rule(&r_ax5), ilin = tc_rule(&r_lin);
  int imp1 = tc_rule(&r_mp1), imp2 = tc_rule(&r_mp2), imps1 = tc_rule(&r_mps1), imps2 = tc_rule(&r_mps2);
  int ifl1 = tc_rule(&r_fl1), ifl2 = tc_rule(&r_fl2), ifls1 = tc_rule(&r_fls1), ifls2 = tc_rule(&r_fls2);
  CHECK(tc_rule_fibre(iax1) == FIBRE_PURE);
  CHECK(tc_rule_fibre(iax5) == FIBRE_PURE);
  CHECK(tc_rule_fibre(ilin) == (FIBRE_PURE | FIBRE_GROUND | FIBRE_LINEAR | FIBRE_FLAT));
  CHECK(tc_rule_fibre(imp1) == (FIBRE_PURE | FIBRE_GROUND));
  CHECK(tc_rule_fibre(ifl1) == (FIBRE_PURE | FIBRE_GROUND | FIBRE_FLAT));
  CHECK(tc_rule_fibre(ifls1) == 0);

  /* R113 probe 1: both premise orders (A, A->B) and (A->B, A), fast vs slow, on open & ground boards */
  Occ op0 = tc_post(0, p), oq0 = tc_post(0, q), opp0 = tc_post(0, im(p, q)), oqp0 = tc_post(0, im(q, p));
  (void)oq0;
  Term z1 = tc_meta(), z2 = tc_meta(), z3 = tc_meta(), z4 = tc_meta();
  Occ oz1 = tc_post(0, im(z1, q)), oz2 = tc_post(0, im(z2, q)), oz3 = tc_post(0, im(z3, q)), oz4 = tc_post(0, im(z4, q));
  Occ a_mp1  = tc_fire(imp1,  NULL, (Occ[]){ op0, oz1 }, NULL);
  Occ a_mp2  = tc_fire(imp2,  NULL, (Occ[]){ oz2, op0 }, NULL);
  Occ a_mps1 = tc_fire(imps1, NULL, (Occ[]){ op0, oz3 }, NULL);
  Occ a_mps2 = tc_fire(imps2, NULL, (Occ[]){ oz4, op0 }, NULL);
  CHECK(a_mp1 && a_mp2 && a_mps1 && a_mps2);
  CHECK(tc_term(a_mp1) == q && tc_term(a_mp2) == q && tc_term(a_mps1) == q && tc_term(a_mps2) == q);
  CHECK(tc_deref(z1) == p && tc_deref(z2) == p && tc_deref(z3) == p && tc_deref(z4) == p);
  /* Flat fast path vs reversed flat vs slow oracle across ground and open combinations: */
  Occ f_pool[6] = { opp0, oqp0, oz1, oz2, op0, oq0 };
  for (int i = 0; i < 6; i++) {
    for (int j = 0; j < 6; j++) {
      Occ r_fast1 = tc_fire(ifl1,  NULL, (Occ[]){ f_pool[i], f_pool[j] }, NULL);
      Occ r_fast2 = tc_fire(ifl2,  NULL, (Occ[]){ f_pool[j], f_pool[i] }, NULL);
      Occ r_slow1 = tc_fire(ifls1, NULL, (Occ[]){ f_pool[i], f_pool[j] }, NULL);
      Occ r_slow2 = tc_fire(ifls2, NULL, (Occ[]){ f_pool[j], f_pool[i] }, NULL);
      CHECK((r_fast1 != 0) == (r_slow1 != 0) && (r_fast2 != 0) == (r_slow2 != 0) && (r_fast1 != 0) == (r_fast2 != 0));
      if (r_fast1) CHECK(tc_term(r_fast1) == tc_term(r_slow1) && tc_term(r_fast1) == tc_term(r_fast2) && tc_term(r_fast2) == tc_term(r_slow2));
    }
  }

  /* 6. R113 probe 2 + full DAG torture gate (2^28 = 268,435,456 paths in 29 DAG nodes):
        occurs, norm (tc_deref), unify (two distinct DAG towers), umatch, inst, and fv (tc_def). */
  Term dag_z1 = tc_meta(), dag_z2 = tc_meta(), dag_t1 = dag_z1, dag_t2 = dag_z2, dag_v = A;
  for (int i = 0; i < 28; i++) {
    dag_t1 = im(dag_t1, dag_t1);
    dag_t2 = im(dag_t2, dag_t2);
    dag_v  = im(dag_v, dag_v);
  }
  Term dag_m = tc_meta();
  CHECK(!tc_tell(dag_z1, dag_t1));                                            /* occurs check: cycle refused in O(nodes) */
  CHECK(tc_tell(dag_m, dag_t1));                                              /* occurs check: non-cycle admitted in O(nodes) */
  CHECK(tc_tell(dag_t1, dag_t2));                                             /* unify two 2^28-path DAG towers in O(nodes) */
  CHECK(tc_tell(dag_z2, p));
  Term dag_p = p; for (int i = 0; i < 28; i++) dag_p = im(dag_p, dag_p);
  CHECK(tc_deref(dag_m) == dag_p);                                            /* norm 2^28-path DAG tower in O(nodes) */
  Rule r_dag = { .nkeep = 1, .keep = { { dag_v, 0 } }, .make = { dag_v, 0 }, .fresh = -1 };
  int idag = tc_rule(&r_dag);
  Occ odag_in = tc_post(0, dag_p);
  Occ odag_out = tc_fire(idag, NULL, &odag_in, NULL);                         /* umatch + inst on 2^28-path DAG rule */
  CHECK(idag >= 0 && odag_out && tc_term(odag_out) == dag_p);
  CHECK(tc_ctx(1, ww));
  Term dag_def_body = tc_v(0); for (int i = 0; i < 28; i++) dag_def_body = im(dag_def_body, dag_def_body);
  CHECK(tc_def((uint16_t)WFF, 0, 1, 0, dag_def_body) >= 0);                   /* fv on 2^28-path DAG body in O(nodes) */

  /* 7. Binder-bearing absent/count with separation (X # F), bare-variable sort-checked count,
        EXTEND rejecting open K_META, and API boundary guards (undeclared sort, K_VAR in tell). */
  CHECK(tc_init(1u << 12, 1u << 8));
  WFF = tc_sort(SORT_PROVABLE); VAR = tc_sort(0);
  IM = tc_con((uint16_t)WFF, 0, 2, (Binder[2]){ { (uint16_t)WFF, 0, 0 }, { (uint16_t)WFF, 0, 0 } });
  AL = tc_con((uint16_t)WFF, 0, 2, (Binder[2]){ { (uint16_t)VAR, 1, 0 }, { (uint16_t)WFF, 0, 1 } });
  P = tc_con((uint16_t)WFF, 0, 0, NULL); PX = tc_con((uint16_t)WFF, 0, 1, &(Binder){ (uint16_t)VAR, 0, 0 });
  p = c0(P); x0 = tc_bv((uint16_t)VAR, 0);
  CHECK(tc_name(9999, 0) == 0 && tc_bv(9999, 0) == 0);                        /* undeclared sort rejected */
  CHECK(tc_ctx(2, (Binder[2]){ { (uint16_t)VAR, 1, 0 }, { (uint16_t)WFF, 0, 0 } })); /* X bound, F independent of X */
  X = tc_v(0); F = tc_v(1);
  CHECK(!tc_tell(X, X) && !tc_tell_neq(F, p));                                /* K_VAR rejected in board tell/neq */
  Rule r_abs_al = { .nabsent = 1, .absent = { { al(X, F), 0 } }, .make = { p, 1 }, .fresh = -1 };
  Rule r_cnt_wff = { .ncount = 1, .count = { { F, 0, 1 } }, .make = { p, 1 }, .fresh = -1 };
  Rule r_ext_open = { .make = { px(X), 1 }, .fresh = 0 };
  CHECK(tc_rule(&r_ext_open) == -1);                                          /* fresh hole cannot be bound */
  int iabs_al = tc_rule(&r_abs_al), icnt_wff = tc_rule(&r_cnt_wff);
  CHECK(tc_ctx(2, (Binder[2]){ { (uint16_t)VAR, 0, 0 }, { (uint16_t)VAR, 0, 0 } }));
  Rule r_ext_var = { .make = { px(tc_v(0)), 1 }, .fresh = 0 };
  int iext_v = tc_rule(&r_ext_var);
  CHECK(iabs_al >= 0 && icnt_wff >= 0 && iext_v >= 0);
  CHECK(tc_fresh_name() == 0);
  CHECK(!tc_fire(iext_v, NULL, NULL, (Term[2]){ 0, tc_meta() }));             /* EXTEND refuses open K_META */
  CHECK(tc_fire(iabs_al, NULL, NULL, NULL));                                  /* empty board: al(X,F) absent */
  CHECK(tc_post(0, tc_name((uint16_t)VAR, 0)));                               /* VAR-sorted occurrence */
  CHECK(!tc_fire(icnt_wff, NULL, NULL, NULL));                                /* VAR does not count as WFF */
  CHECK(tc_post(0, al(x0, px(x0))));                                          /* x0 occurs in px(x0): violates X # F */
  CHECK(tc_fire(icnt_wff, NULL, NULL, NULL));                                 /* 1 WFF occurrence on board */
  CHECK(tc_fire(iabs_al, NULL, NULL, NULL));                                  /* al(x0, px(x0)) is not an X # F match! */
  CHECK(tc_post(0, al(x0, p)));                                               /* x0 # p: matches al(X, F) with X # F */
  CHECK(!tc_fire(iabs_al, NULL, NULL, NULL));                                 /* now al(X, F) is present: refused */

  /* 8. R115a + R115b Exhaustive Guard-Mutation & Adversarial Witness Suite
        (kills K07, K09, K10, K12, K14, K19, K23, K25, K26, K28, K38, K39, K40, K41,
         K44, K45, K50, K52, K54, plus p1_fresh..p9_stale_ctx & witness1/2). */
  CHECK(tc_init(1u << 14, 1u << 10));
  WFF = tc_sort(SORT_PROVABLE); VAR = tc_sort(0);
  int FREE_S = tc_sort(SORT_FREE), STRICT_S = tc_sort(SORT_STRICT);
  ww[0] = ww[1] = (Binder){ (uint16_t)WFF, 0, 0 };
  xa[0] = (Binder){ (uint16_t)VAR, 1, 0 }; xa[1] = (Binder){ (uint16_t)WFF, 0, 1 };
  Binder xv1 = { (uint16_t)VAR, 0, 0 };
  IM = tc_con((uint16_t)WFF, 0, 2, ww); AL = tc_con((uint16_t)WFF, 0, 2, xa); PX = tc_con((uint16_t)WFF, 0, 1, &xv1);
  int AN = tc_con((uint16_t)WFF, 0, 2, ww);                                   /* second binary wff constructor for head checks */
  P = tc_con((uint16_t)WFF, 0, 0, NULL); Q = tc_con((uint16_t)WFF, 0, 0, NULL);
  p = c0(P); q = c0(Q); x0 = tc_bv((uint16_t)VAR, 0);
  /* K23: regular binder depending on non-bound binder */
  CHECK(tc_con((uint16_t)WFF, 0, 2, (Binder[2]){ { (uint16_t)WFF, 0, 0 }, { (uint16_t)WFF, 0, 1 } }) == -1);
  CHECK(tc_con((uint16_t)WFF, 0, 2, (Binder[2]){ { (uint16_t)WFF, 0, 2 }, { (uint16_t)VAR, 1, 0 } }) == -1);
  /* K25: tc_con retdeps pointing to non-bound binder */
  CHECK(tc_con((uint16_t)WFF, 1, 1, &ww[0]) == -1);
  /* K39: pats_ok rejects unminted name */
  CHECK(tc_ctx(1, &ww[0]));
  A = tc_v(0);
  Rule r_unminted = { .make = { px(tc_name((uint16_t)VAR, 9)), 0 }, .fresh = -1 };
  CHECK(tc_rule(&r_unminted) == -1);
  /* K52: fresh hole cannot appear in keep */
  CHECK(tc_ctx(1, &xv1));
  Rule r_fresh_keep = { .nkeep = 1, .keep = { { px(tc_v(0)), 0 } }, .make = { px(tc_v(0)), 0 }, .fresh = 0 };
  CHECK(tc_rule(&r_fresh_keep) == -1);
  /* K41: implied check must verify boundness of hole vs constructor arg */
  CHECK(tc_ctx(1, &(Binder){ (uint16_t)VAR, 1, 0 }));
  X = tc_v(0);
  Rule r_imp_bnd = { .nkeep = 1, .keep = { { px(X), 0 } }, .make = { al(X, px(X)), 0 }, .fresh = -1 };
  int i_ib = tc_rule(&r_imp_bnd);
  CHECK(i_ib >= 0);
  Term n_v0 = tc_name((uint16_t)VAR, 0); tc_fresh_name();
  Occ o_pxn = tc_post(0, px(n_v0));
  CHECK(!tc_fire(i_ib, NULL, &o_pxn, NULL));                                  /* name n_v0 is not a bound var! */
  /* K26: bound hole avoids earlier independent hole (F at 0, X bound at 1) */
  CHECK(tc_ctx(2, (Binder[2]){ { (uint16_t)WFF, 0, 0 }, { (uint16_t)VAR, 1, 0 } }));
  F = tc_v(0); X = tc_v(1);
  Rule r_ax5_rev = { .make = { im(F, al(X, F)), 0 }, .fresh = -1 };
  int i_a5r = tc_rule(&r_ax5_rev);
  CHECK(i_a5r >= 0 && !tc_fire(i_a5r, NULL, NULL, (Term[2]){ px(x0), x0 }));  /* F=px(x0) mentions X=x0 -> refused! */
  /* K38, K44, K45: constant subterm in keep, FLAT head mismatch, deep APP head mismatch */
  CHECK(tc_ctx(2, ww));
  A = tc_v(0); B = tc_v(1);
  Rule r_const_keep = { .nkeep = 1, .keep = { { im(A, p), 0 } }, .make = { A, 0 }, .fresh = -1 };
  Rule r_mp_sp1 = { .nkeep = 2, .keep = { { A, 1 }, { im(A, B), 1 } }, .make = { B, 0 }, .fresh = -1 };
  int i_ck = tc_rule(&r_const_keep), i_mpsp1 = tc_rule(&r_mp_sp1);
  Occ o_im_pq = tc_post(0, im(p, q)), o_an_pp = tc_post(0, tc_app(AN, (Term[]){ p, p }));
  CHECK(!tc_fire(i_ck, NULL, &o_im_pq, NULL));                                /* K38: im(p,q) != im(A,p) */
  CHECK(!tc_fire(i_ck, NULL, &o_an_pp, NULL));                                /* K44: AN(p,p) != im(A,p) */
  Term deep_im = A, deep_an = p, deep_im_p = p;
  for (int i = 0; i < 8; i++) {
    deep_im = im(deep_im, deep_im);
    deep_an = im(deep_an, deep_an);
    deep_im_p = im(deep_im_p, deep_im_p);
  }
  deep_im = im(deep_im, p); deep_an = tc_app(AN, (Term[]){ deep_an, p }); deep_im_p = im(deep_im_p, p);
  Rule r_deep_head = { .nkeep = 1, .keep = { { deep_im, 0 } }, .make = { A, 0 }, .fresh = -1 };
  int i_dh = tc_rule(&r_deep_head);
  Occ o_dan = tc_post(0, deep_an), o_dim = tc_post(0, deep_im_p);
  CHECK(i_dh >= 0 && !tc_fire(i_dh, NULL, &o_dan, NULL) && tc_fire(i_dh, NULL, &o_dim, NULL)); /* K45 */
  /* K14, K28, K50: tc_def free dummy, retdeps on bound arg in fv, ar+nd != cn */
  CHECK(tc_ctx(2, (Binder[2]){ { (uint16_t)WFF, 0, 0 }, { (uint16_t)FREE_S, 1, 0 } }));
  CHECK(tc_def((uint16_t)WFF, 0, 1, 1, tc_v(0)) == -1);                       /* K14: dummy of SORT_FREE */
  CHECK(tc_ctx(2, (Binder[2]){ { (uint16_t)WFF, 0, 0 }, { (uint16_t)VAR, 1, 0 } }));
  CHECK(tc_def((uint16_t)WFF, 0, 1, 0, tc_v(0)) == -1);                       /* K50: ar+nd != cn */
  int BCON = tc_con((uint16_t)WFF, 1, 1, &(Binder){ (uint16_t)VAR, 1, 0 });   /* bound arg 0 escapes in retdeps! */
  CHECK(BCON >= 0 && tc_def((uint16_t)WFF, 0, 1, 1, tc_app(BCON, (Term[]){ tc_v(1) })) == -1); /* K28 */
  /* K19, K54: CV_CONG wrong arity, tc_convert target check, p4_convert_capture */
  CHECK(tc_ctx(1, &ww[0]));
  int D_id = tc_def((uint16_t)WFF, 0, 1, 0, im(tc_v(0), tc_v(0)));
  CHECK(D_id >= 0);
  Occ o_pp = tc_post(0, im(p, p)), o_dp = tc_post(0, tc_app(D_id, &p));
  Conv c_unf_pp = { .kind = CV_UNFOLD, .con = D_id, .args = &p, .kid = &(Conv){ .kind = CV_REFL, .t = im(p, p) } };
  CHECK(!tc_convert(o_pp, &c_unf_pp, q));                                     /* K54: target q != D_id(p) */
  Conv c_bad_unf = { .kind = CV_UNFOLD, .con = D_id, .args = &p, .kid = &(Conv){ .kind = CV_REFL, .t = p } };
  CHECK(o_dp && !tc_convert(o_dp, &c_bad_unf, p));                            /* K18: unfold kid l2 != sub */
  Occ o_dp_pp = tc_post(0, im(tc_app(D_id, &p), im(p, p)));
  Conv c_sym_kids[2] = { c_unf_pp, { .kind = CV_SYM, .kid = &c_unf_pp } };
  Conv c_cong_sym = { .kind = CV_CONG, .con = IM, .n = 2, .kid = c_sym_kids };
  CHECK(o_dp_pp && tc_convert(o_dp_pp, &c_cong_sym, im(im(p, p), tc_app(D_id, &p)))); /* K49: CV_SYM swaps l, r */
  Conv c_refl_p3[3] = { { .kind = CV_REFL, .t = p }, { .kind = CV_REFL, .t = p }, { .kind = CV_REFL, .t = p } };
  Conv c_bad_ar = { .kind = CV_CONG, .con = IM, .n = 3, .kid = c_refl_p3 };
  CHECK(!tc_convert(o_pp, &c_bad_ar, im(p, p)));                              /* K19: CV_CONG arity 3 != 2 */
  /* p2_flatmake: unchecked write refused */
  CHECK(tc_flat_make(0, 999, (uint16_t)WFF, 0, NULL) == 0);
  CHECK(tc_flat_make(0, (uint32_t)IM, (uint16_t)WFF, 1, &p) == 0);
  CHECK(tc_flat_make(0, (uint32_t)IM, (uint16_t)WFF, 2, (Term[2]){ n_v0, p }) == 0);
  /* K07, K09, K10, K12, K40, p3_promote_binds, p9_stale_ctx */
  CHECK(tc_ctx(2, ww));
  A = tc_v(0); B = tc_v(1);
  Rule r8_ax1 = { .make = { im(A, im(B, A)), 0 }, .fresh = -1 };
  Rule r8_sw  = { .nkeep = 1, .keep = { { im(A, B), 0 } }, .make = { im(B, A), 0 }, .fresh = -1 };
  Rule r8_unused = { .make = { p, 0 }, .fresh = -1 };
  int i8_ax1 = tc_rule(&r8_ax1), i8_sw = tc_rule(&r8_sw), i8_un = tc_rule(&r8_unused);
  CHECK(i8_ax1 >= 0 && i8_sw >= 0 && i8_un >= 0);
  Term stale_v = tc_v(0);                                                     /* hole 0 from (a: wff) */
  CHECK(tc_ctx(1, &xv1));                                                     /* now hole 0 is (x: var) */
  CHECK(tc_def((uint16_t)WFF, 0, 1, 0, im(stale_v, stale_v)) == -1);          /* p9_stale_ctx on tc_def */
  Step st_hv = { .kind = ST_RULE, .rule = i8_ax1, .inst = (Term[2]){ p, p } };
  Term hv = tc_v(0);
  CHECK(tc_promote(1, 0, 1, &hv, im(p, im(p, p)), &st_hv, 1) == -1);          /* K07/M48: var-sorted hypothesis */
  CHECK(tc_ctx(2, ww));
  Term hole_out = im(tc_v(1), tc_v(1));
  CHECK(tc_ctx(1, &ww[0]));                                                   /* cn = 1, so hole_out (head 1) is outside ctx! */
  CHECK(tc_promote(1, 0, 1, &hole_out, im(p, im(p, p)), &st_hv, 1) == -1);    /* K40: hole outside ctx */
  CHECK(tc_ctx(0, NULL));
  Term hyp_pq = im(p, q), hyp_qp = im(q, p);
  Step st_ok_sw = { .kind = ST_RULE, .rule = i8_sw, .prem = { -1 } };
  CHECK(tc_promote(0, 0, 1, &hyp_qp, hyp_pq, &st_ok_sw, 1) >= 0);             /* primes rbuf[0] = hyp_pq on stack */
  Step st_self = { .kind = ST_RULE, .rule = i8_sw, .prem = { 0 } };
  CHECK(tc_promote(0, 0, 1, &hyp_pq, hyp_qp, &st_self, 1) == -1);             /* K09: step 0 references prem 0 */
  Step st_sp1 = { .kind = ST_RULE, .rule = i_mpsp1, .prem = { -1, -2 } };
  Term hy_mp[2] = { p, im(p, q) };
  CHECK(tc_promote(0, 0, 2, hy_mp, q, &st_sp1, 1) == -1);                     /* K10/M50: premise space 0 != rule space 1 */
  Step st_bad_cv[2] = {
    { .kind = ST_RULE, .rule = i8_ax1, .inst = (Term[2]){ p, p } },
    { .kind = ST_CONV, .prem = { -1 }, .target = q, .conv = &c_unf_pp }
  };
  Term hyp_pp = im(p, p);
  CHECK(tc_promote(0, 0, 1, &hyp_pp, q, st_bad_cv, 2) == -1);                 /* K12: ST_CONV target q unchecked */
  Step st_bad_inst = { .kind = ST_RULE, .rule = i8_un, .inst = (Term[2]){ stale_v, 0 } };
  CHECK(tc_promote(0, 0, 1, &hyp_pp, p, &st_bad_inst, 1) == -1);              /* K48: inst checked by lemma_term */
  Step st_m37[2] = {
    { .kind = ST_RULE, .rule = i_dh, .prem = { -1 }, .inst = (Term[2]){ p, p } },
    { .kind = ST_RULE, .rule = i_dh, .prem = { -1 }, .inst = (Term[2]){ q, p } }
  };
  CHECK(tc_promote(0, 0, 1, &deep_im_p, q, st_m37, 2) == -1);                 /* M37: promote bumps ug per step */
  /* W21, W24, W28, W30, W39, W40, W44, W23, M13 from R115a witness{,2}.c */
  Term wX = tc_meta();
  CHECK(tc_tell_neq(wX, q));
  CHECK(!tc_tell(im(wX, p), im(q, p)) && !tc_tell(im(wX, p), im(q, p)));      /* W21: undo invalidates ucache */
  CHECK(tc_ctx(2, ww));
  Rule r_eat = { .ntake = 1, .take = { { im(tc_v(0), tc_v(1)), 0 } }, .make = { p, 1 }, .fresh = -1 };
  Rule r_m13 = { .nneq = 1, .neq = { { tc_v(0), p } }, .nabsent = 1, .absent = { { im(p, p), 0 } }, .make = { p, 0 }, .fresh = -1 };
  int ieat = tc_rule(&r_eat), im13 = tc_rule(&r_m13);
  Term m13X = tc_meta();
  CHECK(im13 >= 0 && !tc_fire(im13, NULL, NULL, (Term[2]){ m13X, p }) && tc_tell(m13X, p)); /* M13: failed fire rolls back nne */
  Occ o_eat = tc_post(0, im(p, q));
  CHECK(ieat >= 0 && o_eat && tc_fire(ieat, &o_eat, NULL, NULL));
  CHECK(!tc_fire(i8_sw, NULL, &o_eat, NULL));                                 /* W24: taken occurrence clears Wtag */
  Term wZ = tc_meta();
  CHECK(!tc_app(AL, (Term[]){ wZ, p }));                                      /* W30: unknown at bound position */
  CHECK(!tc_fire(i_a5r, NULL, NULL, (Term[2]){ px(wZ), x0 }));                /* W39: separation rejects unknown */
  Term wZ2 = tc_meta();
  CHECK(tc_tell(wZ2, p));
  CHECK(tc_fire(i_a5r, NULL, NULL, (Term[2]){ im(wZ2, p), x0 }));             /* W28: holes normalized before holes_ok */
  CHECK(tc_ctx(0, NULL));
  Rule r_abs_p = { .nabsent = 1, .absent = { { p, 0 } }, .make = { q, 0 }, .fresh = -1 };
  Rule r_cnt2_p = { .ncount = 1, .count = { { p, 4, 2 } }, .make = { q, 1 }, .fresh = -1 };
  int iabs_p = tc_rule(&r_abs_p), icnt2_p = tc_rule(&r_cnt2_p);
  CHECK(iabs_p >= 0 && icnt2_p >= 0);
  CHECK(tc_init(1u << 12, 1u << 8));
  WFF = tc_sort(SORT_PROVABLE);
  P = tc_con((uint16_t)WFF, 0, 0, NULL); Q = tc_con((uint16_t)WFF, 0, 0, NULL);
  p = c0(P); q = c0(Q);
  CHECK(tc_ctx(0, NULL));
  Rule r_w40 = { .nabsent = 1, .absent = { { p, 0 } }, .make = { q, 0 }, .fresh = -1 };
  Rule r_w23 = { .ncount = 1, .count = { { p, 0, 2 } }, .make = { q, 1 }, .fresh = -1 };
  int iw40 = tc_rule(&r_w40), iw23 = tc_rule(&r_w23);
  CHECK(tc_post(3, p) && tc_fire(iw40, NULL, NULL, NULL));                    /* W40: absent only checks its space */
  tc_seal();
  CHECK(tc_post(0, p) && tc_post(0, p) && tc_fire(iw23, NULL, NULL, NULL));   /* W23: no post dedup when has_take */
  (void)STRICT_S;

  /* Transient terms: a lemma's proof terms go when it is installed; its statement stays. */
  CHECK(tc_init(1u << 12, 1u << 8));
  WFF = tc_sort(SORT_PROVABLE);
  Binder tw[2] = { { (uint16_t)WFF, 0, 0 }, { (uint16_t)WFF, 0, 0 } };
  IM = tc_con((uint16_t)WFF, 0, 2, tw); P = tc_con((uint16_t)WFF, 0, 0, NULL); Q = tc_con((uint16_t)WFF, 0, 0, NULL);
  p = c0(P); q = c0(Q);
  CHECK(tc_ctx(2, tw));
  Rule t_k = { .make = { im(tc_v(0), im(tc_v(1), tc_v(0))), 0 }, .fresh = -1 };            /* a -> (b -> a) */
  Rule t_mp = { .nkeep = 2, .keep = { { tc_v(0), 0 }, { im(tc_v(0), tc_v(1)), 0 } }, .make = { tc_v(1), 0 }, .fresh = -1 };
  int ik = tc_rule(&t_k), imp = tc_rule(&t_mp);
  CHECK(ik >= 0 && imp >= 0);
  for (int pin = 0; pin < 2; pin++) {                        /* from a, derive q -> a */
    CHECK(tc_ctx(1, tw));
    Term ta = tc_v(0);
    tc_transient();
    Term concl = im(q, ta), mid = im(ta, concl);              /* mid: only a proof term */
    if (pin) CHECK(tc_post(0, p));                            /* a board write keeps every term */
    Step st[2] = { { .kind = ST_RULE, .rule = ik, .inst = (Term[2]){ ta, q }, .target = mid },
                   { .kind = ST_RULE, .rule = imp, .prem = { -1, 0 }, .target = concl } };
    int lem = tc_promote(1, 0, 1, (Term[1]){ ta }, concl, st, 2);
    CHECK(lem >= 0);
    CHECK((im(p, p) == mid) == !pin);                         /* released: mid's slot is reused */
    CHECK(im(q, ta) == concl);                                /* the statement keeps its term */
    Occ hp = tc_post(0, p);
    Occ got = tc_fire(lem, NULL, (Occ[1]){ hp }, NULL);
    CHECK(got && tc_term(got) == im(q, p));
  }
  CHECK(tc_ctx(1, tw));
  tc_transient();
  Term claim = im(p, tc_v(0));
  Step bad = { .kind = ST_RULE, .rule = ik, .inst = (Term[2]){ tc_v(0), q }, .target = claim };
  CHECK(tc_promote(1, 0, 0, NULL, claim, &bad, 1) == -1);                                  /* claimed result checked */

  /* A release must leave no kernel state pointing at a released term (main:8's two probes). */
  for (int variant = 0; variant < 2; variant++) {
    CHECK(tc_init(1u << 12, 1u << 8));
    WFF = tc_sort(SORT_PROVABLE);
    IM = tc_con((uint16_t)WFF, 0, 2, tw);
    Term na = tc_name((uint16_t)WFF, tc_fresh_name()), nb = tc_name((uint16_t)WFF, tc_fresh_name());
    CHECK(tc_ctx(2, tw));
    Rule flip = { .nkeep = 1, .keep = { { im(tc_v(0), tc_v(1)), 0 } }, .make = { im(tc_v(1), tc_v(0)), 0 }, .fresh = -1 };
    Term m = tc_meta();
    if (variant == 0) {                                      /* a tell in scope writes K: no release */
      tc_transient();
      CHECK(tc_tell(m, im(na, nb)));
      Rule flip2 = { .nkeep = 1, .keep = { { im(tc_v(1), tc_v(1)), 0 } }, .make = { im(tc_v(0), tc_v(0)), 0 }, .fresh = -1 };
      CHECK(tc_rule(&flip2) >= 0);                          /* its patterns would take the told term's slot */
      CHECK(tc_tell(m, im(na, nb)) && !tc_tell_neq(m, im(na, nb)));
    } else {                                                 /* a cached unification goes with a release */
      CHECK(tc_tell(m, nb));
      tc_transient();
      CHECK(tc_tell(im(na, m), im(na, nb)));
      CHECK(tc_rule(&flip) >= 0);
      CHECK(!tc_tell(im(na, na), im(nb, nb)));
    }
  }

  /* The arena grows past its initial size; terms made before a growth are still found. */
  CHECK(tc_init(256, 2));
  WFF = tc_sort(SORT_PROVABLE);
  IM = tc_con((uint16_t)WFF, 0, 2, tw); P = tc_con((uint16_t)WFF, 0, 0, NULL);
  Term chain = c0(P), first = 0;
  for (int i = 0; i < 5000; i++) { chain = im(chain, c0(P)); if (i == 10) first = chain; }
  Term again = c0(P);
  for (int i = 0; i <= 10; i++) again = im(again, c0(P));
  CHECK(chain && again == first);

  /* Birth-named scope (tc_birth) and by-value flat tuples (tc_flat_put / tc_flat_fire). */
  CHECK(tc_init(1u << 12, 1u << 8));
  WFF = tc_sort(SORT_PROVABLE);
  IM = tc_con((uint16_t)WFF, 0, 2, tw); P = tc_con((uint16_t)WFF, 0, 0, NULL); Q = tc_con((uint16_t)WFF, 0, 0, NULL);
  CHECK(tc_ctx(1, tw));
  tc_birth();
  Term b_p1 = c0(P), b_p2 = c0(P), b_v0 = tc_v(0);
  CHECK(b_p1 != b_p2);                                       /* distinct birth-named occurrences */
  Rule b_ax = { .make = { im(b_p1, b_v0), 0 }, .fresh = -1 };
  int ib_ax = tc_rule(&b_ax);
  CHECK(ib_ax >= 0);
  CHECK(tc_ctx(0, NULL));
  tc_birth();
  Term b_q = c0(Q), b_t1 = im(c0(P), b_q), b_t2 = im(c0(P), b_q);
  CHECK(b_t1 != b_t2 && tc_lemma(0, 0));
  Step b_s0_bad = { .kind = ST_RULE, .rule = ib_ax, .inst = (Term[1]){ c0(Q) }, .target = b_t1 };
  Step b_s0     = { .kind = ST_RULE, .rule = ib_ax, .inst = (Term[1]){ b_q },   .target = b_t1 };
  Conv b_refl = { .kind = CV_REFL };
  Step b_s1_bad = { .kind = ST_CONV, .prem = { 0 }, .target = b_t2, .conv = &b_refl };
  Step b_s1_ok  = { .kind = ST_CONV, .prem = { 0 }, .target = b_t1, .conv = &b_refl };
  CHECK(tc_lemma_step(&b_s0_bad) == -1);                                /* OP_HOLE rejects fresh c0(Q) copy */
  CHECK(tc_lemma(0, 0) && tc_lemma_step(&b_s0) == 0 && tc_lemma_step(&b_s1_bad) == -1); /* CV_REFL rejects copy b_t2 */
  CHECK(tc_lemma(0, 0) && tc_lemma_step(&b_s0) == 0 && tc_lemma_step(&b_s1_ok) == 1 && tc_lemma_end(1) >= 0);
  CHECK(tc_ctx(2, tw));
  Rule b_flat = { .nkeep = 1, .keep = { { im(c0(P), tc_v(0)), 0 } }, .make = { im(tc_v(0), c0(Q)), 0 }, .fresh = -1 };
  int ib_fl = tc_rule(&b_flat);
  tc_seal();
  Occ fo0 = tc_flat_put(0, 0, IM, (Term[2]){ c0(P), c0(Q) });
  Occ fo1 = tc_flat_put(0, 0, IM, (Term[2]){ c0(Q), c0(P) });
  Occ fo_dst = tc_flat_fire(ib_fl, &fo0, NULL, 0);
  CHECK(fo0 && fo1 && fo_dst && !tc_flat_fire(ib_fl, &fo1, NULL, fo_dst));   /* constant guard P != Q refused */
  CHECK(tc_term(fo_dst) == im(c0(Q), c0(Q)));                                /* lazy Term materialization */
  CHECK(tc_flat_fire(ib_fl, &fo0, NULL, fo_dst) == fo_dst);                  /* in-place dest update */

  /* ---- 9. Rows 3-7 Conformance Gate: NamedSpaces, SpacesCreation (Births), NamedSpacesReach,
             ProgramReflection / QuotedLambda, and RhoContinuation ---- */
  {
    /* Row 3 (NamedSpaces.lean): unresolved_takes_from_either_space & resolved_rule_takes_only_there */
    CHECK(tc_init(1u << 12, 1u << 8));
    uint16_t S_SP = tc_space_sort();
    int S_D = tc_sort(0);
    Binder b_d = { (uint16_t)S_D, 0, 0 };
    int C_P = tc_con((uint16_t)S_D, 0, 1, &b_d);
    int C_7 = tc_con((uint16_t)S_D, 0, 0, NULL);
    int C_OK = tc_con((uint16_t)S_D, 0, 0, NULL);
    Term t7 = c0(C_7), p7 = tc_app(C_P, &t7), ok_t = c0(C_OK);
    Term sub1 = tc_name(S_SP, tc_fresh_name()), sub2 = tc_name(S_SP, tc_fresh_name());
    Term thm_sp = tc_space_term(0);
    Binder sp_ctx[1] = { { S_SP, 0, 0 } };
    CHECK(tc_ctx(1, sp_ctx));
    Term V_SP = tc_v(0);
    Rule r_unres = {
      .ntake = 1, .take = { { tc_at_space(V_SP, p7), 0 } },
      .make = { tc_at_space(thm_sp, ok_t), 0 }, .fresh = -1
    };
    Rule r_res_sub1 = {
      .ntake = 1, .take = { { tc_at_space(sub1, p7), 0 } },
      .make = { tc_at_space(thm_sp, ok_t), 0 }, .fresh = -1
    };
    int i_unres = tc_rule(&r_unres), i_res1 = tc_rule(&r_res_sub1);
    CHECK(i_unres >= 0 && i_res1 >= 0);
    Occ o_sub1 = tc_post_at(sub1, p7, false), o_sub2 = tc_post_at(sub2, p7, false);
    CHECK(o_sub1 && o_sub2 && tc_occ_space(o_sub1) == sub1 && tc_occ_space(o_sub2) == sub2);
    CHECK(!tc_fire(i_res1, &o_sub2, NULL, NULL));                            /* resolved_rule_takes_only_there: refuses sub2 */
    CHECK(tc_fire(i_unres, &o_sub1, NULL, NULL));                            /* unresolved_takes_from_either_space: sub1 */
    CHECK(tc_fire(i_unres, &o_sub2, NULL, NULL));                            /* unresolved_takes_from_either_space: sub2 */
    Occ o_sub1_b = tc_post_at(sub1, p7, false);
    CHECK(tc_fire(i_res1, &o_sub1_b, NULL, NULL));                           /* resolved_rule_takes_only_there: admits sub1 */

    /* Row 4 (Step/SpacesCreation.lean): Births (keeps, fresh, single, located) */
    CHECK(tc_init(1u << 12, 1u << 8));
    S_SP = tc_space_sort();
    S_D = tc_sort(0); b_d = (Binder){ (uint16_t)S_D, 0, 0 };
    C_P = tc_con((uint16_t)S_D, 0, 1, &b_d); C_7 = tc_con((uint16_t)S_D, 0, 0, NULL); C_OK = tc_con((uint16_t)S_D, 0, 0, NULL);
    t7 = c0(C_7); p7 = tc_app(C_P, &t7); ok_t = c0(C_OK);
    Term sp1 = tc_space_term(1), sp2 = tc_space_term(2);
    Occ m_sp1 = tc_post_at(sp1, ok_t, true);                                 /* start: space 1 is born */
    CHECK(m_sp1 && tc_occ_marker(m_sp1) && tc_space_born(sp1) && !tc_space_born(sp2));
    CHECK(tc_ctx(0, NULL));
    Rule r_row_sp2 = { .birth_law = 1, .make = { tc_at_space(sp2, p7), 0 }, .fresh = -1 };
    Rule r_create_sp2 = { .birth_law = 1, .make = { tc_at_birth(sp2, ok_t), 0 }, .fresh = -1 };
    Rule r_double_marker = {
      .birth_law = 1, .nmake_extra = 1,
      .make = { tc_at_birth(sp2, ok_t), 0 },
      .make_extra = { { tc_at_birth(sp2, ok_t), 0 } }, .fresh = -1
    };
    Rule r_take_marker = {
      .birth_law = 1, .ntake = 1, .take = { { tc_at_space(sp1, ok_t), 0 } },
      .make = { tc_at_space(sp1, p7), 0 }, .fresh = -1
    };
    int ir_row2 = tc_rule(&r_row_sp2), ir_cr2 = tc_rule(&r_create_sp2);
    int ir_dbl = tc_rule(&r_double_marker), ir_tkm = tc_rule(&r_take_marker);
    CHECK(!tc_fire(ir_row2, NULL, NULL, NULL));                              /* row_before_birth_refused */
    CHECK(!tc_fire(ir_tkm, &m_sp1, NULL, NULL));                             /* taking_marker_refused */
    CHECK(!tc_fire(ir_dbl, NULL, NULL, NULL));                               /* Births.single: two markers for sp2 refused */
    CHECK(tc_fire(ir_cr2, NULL, NULL, NULL) && tc_space_born(sp2));          /* create_admitted */
    CHECK(tc_fire(ir_row2, NULL, NULL, NULL));                               /* row_after_birth_admitted */
    CHECK(!tc_fire(ir_cr2, NULL, NULL, NULL));                               /* second_birth_refused */
    /* Also verify create_with_row_admitted on a fresh space sp3 */
    Term sp3 = tc_space_term(3);
    Rule r_cwr3 = {
      .birth_law = 1, .nmake_extra = 1,
      .make = { tc_at_birth(sp3, ok_t), 0 },
      .make_extra = { { tc_at_space(sp3, p7), 0 } }, .fresh = -1
    };
    int ir_cwr3 = tc_rule(&r_cwr3);
    CHECK(!tc_space_born(sp3) && tc_fire(ir_cwr3, NULL, NULL, NULL));        /* create_with_row_admitted */
    CHECK(tc_space_born(sp3) && tc_last_extra(0) && tc_term(tc_last_extra(0)) == p7);

    /* Row 5 (NamedSpacesReach.lean): indirection_separates, handle_gives_reach, no_handle_no_reach,
       search_finds_held_contradiction, search_ignores_unheld, guest_cannot_select_at_thm,
       reach_refuses_unbound_absence */
    CHECK(tc_init(1u << 12, 1u << 8));
    S_SP = tc_space_sort();
    S_D = tc_sort(0); b_d = (Binder){ (uint16_t)S_D, 0, 0 };
    Binder b_sp = { S_SP, 0, 0 };
    C_P = tc_con((uint16_t)S_D, 0, 1, &b_d);
    int C_NOT = tc_con((uint16_t)S_D, 0, 1, &b_d);
    int C_HND = tc_con((uint16_t)S_D, 0, 1, &b_sp);
    int C_NOT_HND = tc_con((uint16_t)S_D, 0, 1, &b_sp);
    C_7 = tc_con((uint16_t)S_D, 0, 0, NULL);
    int C_FALSE = tc_con((uint16_t)S_D, 0, 0, NULL);
    tc_set_handle_con(C_HND);
    t7 = c0(C_7); p7 = tc_app(C_P, &t7);
    Term np7 = tc_app(C_NOT, &p7), falsity = c0(C_FALSE);
    Term actor = tc_space_term(1), r_sub1 = tc_space_term(2), r_sub2 = tc_space_term(3);
    Term secret = tc_space_term(4), thm = tc_space_term(5);
    Term h_sub1 = tc_app(C_HND, &r_sub1), nh_sub2 = tc_app(C_NOT_HND, &r_sub2);
    Occ o_h1 = tc_post_at(actor, h_sub1, false), o_nh2 = tc_post_at(actor, nh_sub2, false);
    CHECK(o_h1 && o_nh2);
    Term reached[16];
    int n_reached = tc_reach(&actor, 1, reached, 16);
    CHECK(n_reached == 2 && reached[0] == actor && reached[1] == r_sub1);    /* handle_gives_reach + no_handle_no_reach */
    CHECK(tc_ctx(1, &b_sp));
    V_SP = tc_v(0);
    /* Indirection rule: read handle($s) at actor, read p(7) at $s -> make false at actor */
    Term pat_h = tc_app(C_HND, &V_SP);
    Rule r_indir = {
      .nkeep = 2,
      .keep = { { tc_at_space(actor, pat_h), 0 }, { tc_at_space(V_SP, p7), 0 } },
      .make = { tc_at_space(actor, falsity), 0 }, .fresh = -1
    };
    int i_indir = tc_rule(&r_indir);
    Occ o_p7_sub2 = tc_post_at(r_sub2, p7, false);
    CHECK(!tc_fire(i_indir, NULL, (Occ[2]){ o_h1, o_p7_sub2 }, NULL));       /* indirection_separates: p(7) at sub2 refused */
    Occ o_p7_sub1 = tc_post_at(r_sub1, p7, false);
    CHECK(tc_fire(i_indir, NULL, (Occ[2]){ o_h1, o_p7_sub1 }, NULL));        /* indirection_separates: p(7) at sub1 admitted */
    /* Contradiction rule across held spaces: read p(7) at $s and not(p(7)) at $s -> make false at actor */
    Rule r_contra = {
      .nkeep = 2,
      .keep = { { tc_at_space(V_SP, p7), 0 }, { tc_at_space(V_SP, np7), 0 } },
      .make = { tc_at_space(actor, falsity), 0 }, .fresh = -1
    };
    int i_contra = tc_rule(&r_contra);
    tc_post_at(secret, p7, false); tc_post_at(secret, np7, false);           /* contradiction at unheld secret */
    CHECK(!tc_search_reach(i_contra, &actor, 1));                            /* search_ignores_unheld */
    tc_post_at(r_sub1, np7, false);                                          /* now contradiction at held sub1 */
    CHECK(tc_search_reach(i_contra, &actor, 1));                             /* search_finds_held_contradiction */
    /* guest_cannot_select_at_thm: guest at sub1 tries to post to thm */
    Rule r_guest_thm = { .make = { tc_at_space(thm, falsity), 0 }, .fresh = -1 };
    int i_gthm = tc_rule(&r_guest_thm);
    CHECK(!tc_fire_reach(i_gthm, NULL, NULL, NULL, &r_sub1, 1));             /* guest_cannot_select_at_thm */
    /* reach_refuses_unbound_absence: absent(p(7) at $s) with $s unbound */
    Rule r_unb_abs = {
      .nabsent = 1, .absent = { { tc_at_space(V_SP, falsity), 0 } },
      .make = { tc_at_space(actor, p7), 0 }, .fresh = -1
    };
    int i_uabs = tc_rule(&r_unb_abs);
    CHECK(!tc_fire_reach(i_uabs, NULL, NULL, NULL, &actor, 1));              /* reach_refuses_unbound_absence */

    /* Row 6 (ProgramReflection.lean & ProgramBindersQuoted.lean):
       inert quote, one-layer activate, quoted-lambda beta, and semantic vs raw query */
    CHECK(tc_init(1u << 12, 1u << 8));
    int S_TM = tc_sort(0);
    Binder b_tm1 = { (uint16_t)S_TM, 0, 0 };
    Binder b_tm2[2] = { b_tm1, b_tm1 };
    Binder b_lam[2] = { { (uint16_t)S_TM, 1, 0 }, { (uint16_t)S_TM, 0, 1 } };
    int C_QUOTE = tc_con((uint16_t)S_TM, 0, 1, &b_tm1);
    int C_ACT   = tc_con((uint16_t)S_TM, 0, 1, &b_tm1);
    int C_LAM   = tc_con((uint16_t)S_TM, 0, 2, b_lam);
    int C_APP   = tc_con((uint16_t)S_TM, 0, 2, b_tm2);
    int C_ATOM  = tc_con((uint16_t)S_TM, 0, 0, NULL);
    tc_set_quote_con(C_QUOTE, C_ACT, C_LAM, C_APP);
    Term ka = c0(C_ATOM), bv0 = tc_bv((uint16_t)S_TM, 0);
    Term q_ka = tc_app(C_QUOTE, &ka), qq_ka = tc_app(C_QUOTE, &q_ka);
    Term act_qq = tc_app(C_ACT, &qq_ka), act_atom = tc_app(C_ACT, &ka);
    CHECK(tc_active_norm(act_qq, 10) == q_ka);                               /* one_layer: activate(quote(quote(a))) -> quote(a) */
    CHECK(tc_active_step(act_atom) == 0);                                    /* activation_needs_code: activate(a) stuck */
    Term omega_b = tc_app(C_APP, (Term[2]){ bv0, bv0 });
    Term omega = tc_app(C_LAM, (Term[2]){ bv0, omega_b });
    Term big_omega = tc_app(C_APP, (Term[2]){ omega, omega });
    Term q_omega = tc_app(C_QUOTE, &big_omega);
    Term act_q_omega = tc_app(C_ACT, &q_omega);
    CHECK(tc_active_step(q_omega) == 0 && tc_active_norm(q_omega, 5) == q_omega); /* quoted_loop_halts: quote(Omega) is inert */
    CHECK(tc_active_step(act_q_omega) == big_omega && tc_active_norm(act_q_omega, 10) == 0); /* activated_loop_diverges */
    /* Passing quoted code by beta then explicitly activating (ProgramBindersQuoted.lean): */
    Term id_tm = tc_app(C_LAM, (Term[2]){ bv0, bv0 });
    Term q_id = tc_app(C_QUOTE, &id_tm);
    Term lam_act = tc_app(C_LAM, (Term[2]){ bv0, tc_app(C_ACT, &bv0) });
    Term prog = tc_app(C_APP, (Term[2]){ lam_act, q_id });
    CHECK(tc_active_norm(prog, 10) == id_tm);                                /* passing_then_activating_on_step */
    /* CV_CONG refuses to rewrite inside quote: */
    CHECK(tc_ctx(0, NULL));
    int D_ATOM = tc_def((uint16_t)S_TM, 0, 0, 0, ka);
    Term da = c0(D_ATOM), q_da = tc_app(C_QUOTE, &da);
    Occ o_qda = tc_post(0, q_da);
    Conv c_unf_a = { .kind = CV_UNFOLD, .con = D_ATOM, .kid = &(Conv){ .kind = CV_REFL, .t = ka } };
    Conv c_in_q = { .kind = CV_CONG, .con = C_QUOTE, .n = 1, .kid = &c_unf_a };
    CHECK(o_qda && !tc_convert(o_qda, &c_in_q, q_ka));                       /* quotation_inert under CV_CONG */

    /* Row 7 (RhoContinuation.lean & ContextualCommunicationReflection.lean):
       Name-sort quote(drop(n)) = n vs Process-sort drop(quote(P)) -> P, and continuation view split */
    CHECK(tc_init(1u << 12, 1u << 8));
    int S_PROC = tc_sort(0), S_NAME = tc_sort(0);
    Binder b_proc = { (uint16_t)S_PROC, 0, 0 }, b_name = { (uint16_t)S_NAME, 0, 0 };
    Binder b_np[2] = { b_name, b_proc };
    int R_QUOTE = tc_con((uint16_t)S_NAME, 0, 1, &b_proc);
    int R_DROP  = tc_con((uint16_t)S_PROC, 0, 1, &b_name);
    int R_SEND  = tc_con((uint16_t)S_PROC, 0, 2, b_np);
    int R_NIL   = tc_con((uint16_t)S_PROC, 0, 0, NULL);
    tc_set_rho_con(R_QUOTE, R_DROP, false);                                  /* profile: allow_proc_drop = false */
    Term p_nil = c0(R_NIL), n0 = tc_app(R_QUOTE, &p_nil);
    Term drop_n0 = tc_app(R_DROP, &n0), q_drop_n0 = tc_app(R_QUOTE, &drop_n0);
    CHECK(tc_rho_norm_name(q_drop_n0) == n0);                                /* Name-sort law: @( *(n0) ) = n0 */
    Occ o_send_qd = tc_post(0, tc_app(R_SEND, (Term[2]){ q_drop_n0, p_nil }));
    Conv c_rho_refl = { .kind = CV_REFL };
    CHECK(o_send_qd && tc_convert(o_send_qd, &c_rho_refl, tc_app(R_SEND, (Term[2]){ n0, p_nil })));
    Occ o_drop_q = tc_post(0, drop_n0);
    CHECK(o_drop_q && !tc_rho_step_occ(o_drop_q));                           /* Process-sort drop refused when disabled */
    tc_set_rho_con(R_QUOTE, R_DROP, true);                                   /* profile: allow_proc_drop = true */
    Occ o_stepped = tc_rho_step_occ(o_drop_q);
    CHECK(o_stepped && tc_term(o_stepped) == p_nil);                         /* Process-sort *( @(0) ) -> 0 admitted */
    /* Continuation view split: K[v_name, v_proc] = send(v_name, v_proc) */
    CHECK(tc_ctx(2, b_np));
    Term cont_pat = tc_app(R_SEND, (Term[2]){ tc_v(0), tc_v(1) });
    Term comm_res = tc_rho_comm(q_drop_n0, n0, p_nil, cont_pat, 0, 1);
    CHECK(comm_res == tc_app(R_SEND, (Term[2]){ n0, p_nil }));               /* K[@(0), 0] with channel eq @(*n0) == n0 */

    /* ---- Modular Prepared-Step & Cursor Bridge (PreparedStep.lean / AdmissionRecords.lean) ---- */
    CHECK(tc_init(1u << 12, 1u << 8));
    int S_V = tc_sort(0);
    Binder bv = { (uint16_t)S_V, 0, 0 };
    Binder bv2[2] = { bv, bv };
    int C_FACT = tc_con((uint16_t)S_V, 0, 2, bv2);
    int C_OUT  = tc_con((uint16_t)S_V, 0, 1, &bv);
    int C_AUX  = tc_con((uint16_t)S_V, 0, 1, &bv);
    int C_A    = tc_con((uint16_t)S_V, 0, 0, NULL);
    int C_B    = tc_con((uint16_t)S_V, 0, 0, NULL);
    Term ta = c0(C_A), tb = c0(C_B);
    CHECK(tc_ctx(2, bv2));
    Term vx = tc_v(0), vy = tc_v(1);
    Rule r_prep = {
      .ntake = 1,
      .take = { { tc_app(C_FACT, (Term[2]){ vx, vy }), 0 } },
      .nneq = 1, .neq = { { vx, vy } },
      .make = { tc_app(C_OUT, &vx), 0 },
      .nmake_extra = 1, .make_extra = { { tc_app(C_AUX, &vy), 0 } },
      .fresh = -1
    };
    int ir_prep = tc_rule(&r_prep);
    Occ o_same = tc_post(0, tc_app(C_FACT, (Term[2]){ ta, ta }));
    Occ o_diff = tc_post(0, tc_app(C_FACT, (Term[2]){ ta, tb }));
    TcAdmissionReceipt rec;
    /* Refused candidate (vx == vy violates neq): no receipt, o_same stays alive */
    TcPreparedStep cand_bad = { .rule = ir_prep, .take = &o_same };
    CHECK(!tc_commit_prepared(&cand_bad, &rec));
    CHECK(!rec.admitted && rec.out == 0 && rec.out_term == 0 && rec.nextra == 0);
    CHECK(tc_alive(o_same));
    /* Cursor proposes [cand_bad, cand_good]: skips refused cand_bad, commits cand_good */
    MockCursor mc = {
      .idx = 0, .count = 2,
      .items = {
        { .rule = ir_prep, .take = &o_same },
        { .rule = ir_prep, .take = &o_diff }
      }
    };
    TcCandidateCursor cur = { .ctx = &mc, .next = mock_cursor_next };
    CHECK(tc_step_cursor(&cur, &rec) == 1);
    CHECK(rec.admitted && rec.rule == ir_prep && rec.out != 0);
    CHECK(rec.out_term == tc_app(C_OUT, &ta));
    CHECK(rec.nextra == 1 && tc_term(rec.extra[0]) == tc_app(C_AUX, &tb));
    CHECK(tc_alive(o_same) && !tc_alive(o_diff));
    /* Second step on exhausted cursor returns 0 with empty receipt */
    CHECK(tc_step_cursor(&cur, &rec) == 0 && !rec.admitted);
  }

  printf("tcalc unit tests: %d checks passed\n", checks);
  return 0;
}
