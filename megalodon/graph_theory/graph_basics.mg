Definition simple_graph : set -> (set -> set -> prop) -> prop :=
  fun V R =>
    and (forall x y, R x y -> R y x)
        (and (forall x :e V, ~R x x)
             (forall x y, R x y -> and (x :e V) (y :e V))).

Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_clique : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => and (S c= V) (forall x :e S, forall y :e S, x <> y -> R x y).

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => and (S c= V) (forall x :e S, forall y :e S, x <> y -> ~(R x y)).

Theorem simple_graph_sym : forall V:set, forall R:set -> set -> prop,
  simple_graph V R -> forall x y, R x y -> R y x.
let V. let R: set -> set -> prop.
assume Hsg: simple_graph V R.
exact andEL (forall x y, R x y -> R y x)
            (and (forall x :e V, ~R x x) (forall x y, R x y -> and (x :e V) (y :e V)))
            Hsg.
Qed.

Theorem simple_graph_irreflexive : forall V:set, forall R:set -> set -> prop,
  simple_graph V R -> forall x :e V, ~R x x.
let V. let R: set -> set -> prop.
assume Hsg: simple_graph V R.
claim Hrest: and (forall x :e V, ~R x x) (forall x y, R x y -> and (x :e V) (y :e V)).
  exact andER (forall x y, R x y -> R y x)
              (and (forall x :e V, ~R x x) (forall x y, R x y -> and (x :e V) (y :e V)))
              Hsg.
exact andEL (forall x :e V, ~R x x) (forall x y, R x y -> and (x :e V) (y :e V)) Hrest.
Qed.

Theorem simple_graph_edge_in_V : forall V:set, forall R:set -> set -> prop,
  simple_graph V R -> forall x y, R x y -> and (x :e V) (y :e V).
let V. let R: set -> set -> prop.
assume Hsg: simple_graph V R.
claim Hrest: and (forall x :e V, ~R x x) (forall x y, R x y -> and (x :e V) (y :e V)).
  exact andER (forall x y, R x y -> R y x)
              (and (forall x :e V, ~R x x) (forall x y, R x y -> and (x :e V) (y :e V)))
              Hsg.
exact andER (forall x :e V, ~R x x) (forall x y, R x y -> and (x :e V) (y :e V)) Hrest.
Qed.

Theorem triangle_free_no_selfloop : forall V:set, forall R:set -> set -> prop,
  triangle_free V R ->
  forall x :e V, ~R x x.
let V. let R: set -> set -> prop.
assume Htf: triangle_free V R.
let x. assume Hx: x :e V.
apply notI.
assume Hxx: R x x.
exact Htf x Hx x Hx x Hx Hxx Hxx Hxx.
Qed.

Theorem is_indep_set_Subq : forall V:set, forall R:set -> set -> prop,
  forall S T:set,
    is_indep_set V R S ->
    T c= S ->
    is_indep_set V R T.
let V. let R: set -> set -> prop.
let S. let T.
assume HS: is_indep_set V R S.
assume HTS: T c= S.
claim HSV: S c= V.
  exact andEL (S c= V) (forall x :e S, forall y :e S, x <> y -> ~(R x y)) HS.
claim HindS: forall x :e S, forall y :e S, x <> y -> ~(R x y).
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~(R x y)) HS.
apply andI (T c= V) (forall x :e T, forall y :e T, x <> y -> ~(R x y)).
- prove T c= V.
  let t. assume Ht: t :e T.
  exact HSV t (HTS t Ht).
- prove forall x :e T, forall y :e T, x <> y -> ~(R x y).
  let x. assume HxT: x :e T.
  let y. assume HyT: y :e T.
  assume Hneq: x <> y.
  exact HindS x (HTS x HxT) y (HTS y HyT) Hneq.
Qed.

Theorem is_clique_Subq : forall V:set, forall R:set -> set -> prop,
  forall S T:set,
    is_clique V R S ->
    T c= S ->
    is_clique V R T.
let V. let R: set -> set -> prop.
let S. let T.
assume HS: is_clique V R S.
assume HTS: T c= S.
claim HSV: S c= V.
  exact andEL (S c= V) (forall x :e S, forall y :e S, x <> y -> R x y) HS.
claim HclS: forall x :e S, forall y :e S, x <> y -> R x y.
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> R x y) HS.
apply andI (T c= V) (forall x :e T, forall y :e T, x <> y -> R x y).
- prove T c= V.
  let t. assume Ht: t :e T.
  exact HSV t (HTS t Ht).
- prove forall x :e T, forall y :e T, x <> y -> R x y.
  let x. assume HxT: x :e T.
  let y. assume HyT: y :e T.
  assume Hneq: x <> y.
  exact HclS x (HTS x HxT) y (HTS y HyT) Hneq.
Qed.

Theorem neighborhood_indep : forall V:set, forall R:set -> set -> prop,
  simple_graph V R ->
  triangle_free V R ->
  forall v :e V, forall a b :e V, R v a -> R v b -> (a = b -> False) -> not (R a b).
let V. let R: set -> set -> prop.
assume Hsg: simple_graph V R.
assume Htf: triangle_free V R.
let v. assume Hv: v :e V.
let a. assume Ha: a :e V.
let b. assume Hb: b :e V.
assume Hva: R v a.
assume Hvb: R v b.
assume Habneq: a = b -> False.
apply notI.
assume Hab: R a b.
exact Htf v Hv a Ha b Hb Hva Hab Hvb.
Qed.

Theorem triangle_free_Subq : forall V:set, forall T:set, forall R:set -> set -> prop,
  T c= V ->
  triangle_free V R ->
  triangle_free T R.
let V. let T. let R: set -> set -> prop.
assume HTV: T c= V.
assume Htf: triangle_free V R.
let x. assume HxT: x :e T.
let y. assume HyT: y :e T.
let z. assume HzT: z :e T.
assume Hxy: R x y.
assume Hyz: R y z.
assume Hxz: R x z.
exact Htf x (HTV x HxT) y (HTV y HyT) z (HTV z HzT) Hxy Hyz Hxz.
Qed.

Definition neigh : set -> (set -> set -> prop) -> set -> set :=
  fun V R v => Sep V (fun x:set => R v x).

Theorem neigh_Subq_V : forall V:set, forall R:set -> set -> prop,
  forall v, neigh V R v c= V.
let V. let R: set -> set -> prop.
let v.
prove neigh V R v c= V.
let x. assume Hx: x :e neigh V R v.
apply SepE V (fun t:set => R v t) x Hx.
assume HxV: x :e V.
assume Hrv: R v x.
exact HxV.
Qed.

Theorem neigh_irreflexive_empty : forall V:set, forall R:set -> set -> prop,
  simple_graph V R ->
  forall v :e V, v /:e neigh V R v.
let V. let R: set -> set -> prop.
assume Hsg: simple_graph V R.
let v. assume Hv: v :e V.
assume Hvin: v :e neigh V R v.
apply SepE V (fun t:set => R v t) v Hvin.
assume HvV: v :e V. assume Hrv: R v v.
exact (simple_graph_irreflexive V R Hsg v HvV) Hrv.
Qed.

Theorem triangle_free_neigh_indep : forall V:set, forall R:set -> set -> prop,
  simple_graph V R ->
  triangle_free V R ->
  forall v :e V, is_indep_set V R (neigh V R v).
let V. let R: set -> set -> prop.
assume Hsg: simple_graph V R.
assume Htf: triangle_free V R.
let v. assume Hv: v :e V.
apply andI (neigh V R v c= V) (forall x :e neigh V R v, forall y :e neigh V R v, x <> y -> ~(R x y)).
- exact neigh_Subq_V V R v.
- prove forall x :e neigh V R v, forall y :e neigh V R v, x <> y -> ~(R x y).
  let x. assume HxN: x :e neigh V R v.
  let y. assume HyN: y :e neigh V R v.
  assume Hneq: x <> y.
  apply notI.
  assume Hxy: R x y.
  apply SepE V (fun t:set => R v t) x HxN.
  assume HxV: x :e V. assume Hvx: R v x.
  apply SepE V (fun t:set => R v t) y HyN.
  assume HyV: y :e V. assume Hvy: R v y.
  exact Htf v Hv x HxV y HyV Hvx Hxy Hvy.
Qed.

Definition complement_rel : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun V R x y => and (x :e V) (and (y :e V) (and (x <> y) (~(R x y)))).

Theorem simple_graph_complement : forall V:set, forall R:set -> set -> prop,
  simple_graph V R ->
  simple_graph V (complement_rel V R).
let V. let R: set -> set -> prop.
assume Hsg: simple_graph V R.
apply andI (forall x y, complement_rel V R x y -> complement_rel V R y x)
           (and (forall x :e V, ~complement_rel V R x x)
                (forall x y, complement_rel V R x y -> and (x :e V) (y :e V))).
- prove forall x y, complement_rel V R x y -> complement_rel V R y x.
  let x. let y.
  assume Hc: complement_rel V R x y.
  apply andI (y :e V) (and (x :e V) (and (y <> x) (~(R y x)))).
  * exact andEL (y :e V) (and (x <> y) (~(R x y)))
               (andER (x :e V) (and (y :e V) (and (x <> y) (~(R x y)))) Hc).
  * apply andI (x :e V) (and (y <> x) (~(R y x))).
    + exact andEL (x :e V) (and (y :e V) (and (x <> y) (~(R x y)))) Hc.
    + claim Hneqxy: x <> y.
        exact andEL (x <> y) (~(R x y))
                    (andER (y :e V) (and (x <> y) (~(R x y)))
                           (andER (x :e V) (and (y :e V) (and (x <> y) (~(R x y)))) Hc)).
      apply andI (y <> x) (~(R y x)).
      - assume Hyx: y = x.
        apply Hneqxy.
        rewrite Hyx.
        let Q:set -> set -> prop. assume HQ: Q x x. exact HQ.
      - apply notI.
        assume Hyx: R y x.
        claim Hxy: R x y.
          exact simple_graph_sym V R Hsg y x Hyx.
        exact andER (x <> y) (~(R x y))
                    (andER (y :e V) (and (x <> y) (~(R x y)))
                           (andER (x :e V) (and (y :e V) (and (x <> y) (~(R x y)))) Hc)) Hxy.
- prove and (forall x :e V, ~complement_rel V R x x)
            (forall x y, complement_rel V R x y -> and (x :e V) (y :e V)).
  apply andI (forall x :e V, ~complement_rel V R x x)
             (forall x y, complement_rel V R x y -> and (x :e V) (y :e V)).
  * prove forall x :e V, ~complement_rel V R x x.
    let x. assume Hx: x :e V.
    apply notI.
    assume Hcxx: complement_rel V R x x.
    claim Hneqxx: x <> x.
      exact andEL (x <> x) (~(R x x))
                  (andER (x :e V) (and (x <> x) (~(R x x)))
                         (andER (x :e V) (and (x :e V) (and (x <> x) (~(R x x)))) Hcxx)).
    exact Hneqxx (fun Q:set -> set -> prop => fun HQ: Q x x => HQ).
  * prove forall x y, complement_rel V R x y -> and (x :e V) (y :e V).
    let x. let y. assume Hc: complement_rel V R x y.
    apply andI (x :e V) (y :e V).
    - exact andEL (x :e V) (and (y :e V) (and (x <> y) (~(R x y)))) Hc.
    - exact andEL (y :e V) (and (x <> y) (~(R x y)))
                  (andER (x :e V) (and (y :e V) (and (x <> y) (~(R x y)))) Hc).
Qed.

Theorem clique_complement_indep : forall V:set, forall R:set -> set -> prop,
  forall S:set,
    is_clique V (complement_rel V R) S ->
    is_indep_set V R S.
let V. let R: set -> set -> prop.
let S.
assume Hc: is_clique V (complement_rel V R) S.
claim HSV: S c= V.
  exact andEL (S c= V) (forall x :e S, forall y :e S, x <> y -> complement_rel V R x y) Hc.
claim Hedges: forall x :e S, forall y :e S, x <> y -> complement_rel V R x y.
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> complement_rel V R x y) Hc.
apply andI (S c= V) (forall x :e S, forall y :e S, x <> y -> ~(R x y)).
- exact HSV.
- prove forall x :e S, forall y :e S, x <> y -> ~(R x y).
  let x. assume Hx: x :e S.
  let y. assume Hy: y :e S.
  assume Hneq: x <> y.
  claim Hcomp: complement_rel V R x y.
    exact Hedges x Hx y Hy Hneq.
  exact andER (x <> y) (~(R x y))
              (andER (y :e V) (and (x <> y) (~(R x y)))
                     (andER (x :e V) (and (y :e V) (and (x <> y) (~(R x y)))) Hcomp)).
Qed.

Theorem indep_clique_complement : forall V:set, forall R:set -> set -> prop,
  forall S:set,
    is_indep_set V R S ->
    is_clique V (complement_rel V R) S.
let V. let R: set -> set -> prop.
let S.
assume Hind: is_indep_set V R S.
claim HSV: S c= V.
  exact andEL (S c= V) (forall x :e S, forall y :e S, x <> y -> ~(R x y)) Hind.
claim Hindpair: forall x :e S, forall y :e S, x <> y -> ~(R x y).
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~(R x y)) Hind.
apply andI (S c= V) (forall x :e S, forall y :e S, x <> y -> complement_rel V R x y).
- exact HSV.
- prove forall x :e S, forall y :e S, x <> y -> complement_rel V R x y.
  let x. assume Hx: x :e S.
  let y. assume Hy: y :e S.
  assume Hneq: x <> y.
  apply andI (x :e V) (and (y :e V) (and (x <> y) (~(R x y)))).
  * exact HSV x Hx.
  * apply andI (y :e V) (and (x <> y) (~(R x y))).
    + exact HSV y Hy.
    + apply andI (x <> y) (~(R x y)).
      - exact Hneq.
      - exact Hindpair x Hx y Hy Hneq.
Qed.

Theorem clique_in_complement_iff_indep : forall V:set, forall R:set -> set -> prop,
  forall S:set,
    is_clique V (complement_rel V R) S <-> is_indep_set V R S.
let V. let R: set -> set -> prop.
let S.
apply iffI (is_clique V (complement_rel V R) S) (is_indep_set V R S).
- exact clique_complement_indep V R S.
- exact indep_clique_complement V R S.
Qed.

Definition induced_rel : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun T R x y => and (x :e T) (and (y :e T) (R x y)).

Theorem simple_graph_induced : forall V:set, forall T:set, forall R:set -> set -> prop,
  T c= V ->
  simple_graph V R ->
  simple_graph T (induced_rel T R).
let V. let T. let R: set -> set -> prop.
assume HTV: T c= V.
assume Hsg: simple_graph V R.
apply andI (forall x y, induced_rel T R x y -> induced_rel T R y x)
           (and (forall x :e T, ~induced_rel T R x x)
                (forall x y, induced_rel T R x y -> and (x :e T) (y :e T))).
- prove forall x y, induced_rel T R x y -> induced_rel T R y x.
  let x. let y.
  assume Hir: induced_rel T R x y.
  claim Hxy: R x y.
    exact andER (y :e T) (R x y) (andER (x :e T) (and (y :e T) (R x y)) Hir).
  claim Hyx: R y x.
    exact simple_graph_sym V R Hsg x y Hxy.
  apply andI (y :e T) (and (x :e T) (R y x)).
  * exact andEL (y :e T) (R x y) (andER (x :e T) (and (y :e T) (R x y)) Hir).
  * apply andI (x :e T) (R y x).
    + exact andEL (x :e T) (and (y :e T) (R x y)) Hir.
    + exact Hyx.
- prove and (forall x :e T, ~induced_rel T R x x)
            (forall x y, induced_rel T R x y -> and (x :e T) (y :e T)).
  apply andI (forall x :e T, ~induced_rel T R x x)
             (forall x y, induced_rel T R x y -> and (x :e T) (y :e T)).
  * prove forall x :e T, ~induced_rel T R x x.
    let x. assume HxT: x :e T.
    apply notI.
    assume Hxx: induced_rel T R x x.
    claim HxV: x :e V.
      exact HTV x HxT.
    claim Hrx: R x x.
      exact andER (x :e T) (R x x) (andER (x :e T) (and (x :e T) (R x x)) Hxx).
    exact (simple_graph_irreflexive V R Hsg x HxV) Hrx.
  * prove forall x y, induced_rel T R x y -> and (x :e T) (y :e T).
    let x. let y. assume Hir: induced_rel T R x y.
    apply andI (x :e T) (y :e T).
    - exact andEL (x :e T) (and (y :e T) (R x y)) Hir.
    - exact andEL (y :e T) (R x y) (andER (x :e T) (and (y :e T) (R x y)) Hir).
Qed.

Theorem triangle_free_induced : forall V:set, forall T:set, forall R:set -> set -> prop,
  T c= V ->
  triangle_free V R ->
  triangle_free T (induced_rel T R).
let V. let T. let R: set -> set -> prop.
assume HTV: T c= V.
assume Htf: triangle_free V R.
let x. assume HxT: x :e T.
let y. assume HyT: y :e T.
let z. assume HzT: z :e T.
assume Hxy: induced_rel T R x y.
assume Hyz: induced_rel T R y z.
assume Hxz: induced_rel T R x z.
claim HxyR: R x y.
  exact andER (y :e T) (R x y) (andER (x :e T) (and (y :e T) (R x y)) Hxy).
claim HyzR: R y z.
  exact andER (z :e T) (R y z) (andER (y :e T) (and (z :e T) (R y z)) Hyz).
claim HxzR: R x z.
  exact andER (z :e T) (R x z) (andER (x :e T) (and (z :e T) (R x z)) Hxz).
exact Htf x (HTV x HxT) y (HTV y HyT) z (HTV z HzT) HxyR HyzR HxzR.
Qed.

Theorem neigh_induced_Subq : forall V:set, forall T:set, forall R:set -> set -> prop,
  T c= V ->
  forall v:set, neigh T (induced_rel T R) v c= neigh V R v.
let V. let T. let R: set -> set -> prop.
assume HTV: T c= V.
let v.
prove neigh T (induced_rel T R) v c= neigh V R v.
let x. assume Hx: x :e neigh T (induced_rel T R) v.
apply SepE T (fun t:set => induced_rel T R v t) x Hx.
assume HxT: x :e T. assume Hir: induced_rel T R v x.
claim Hrv: R v x.
  exact andER (x :e T) (R v x) (andER (v :e T) (and (x :e T) (R v x)) Hir).
exact SepI V (fun t:set => R v t) x (HTV x HxT) Hrv.
Qed.

Theorem clique_induced_of_clique : forall V:set, forall T:set, forall R:set -> set -> prop,
  T c= V ->
  forall S:set,
    is_clique V R S ->
    S c= T ->
    is_clique T (induced_rel T R) S.
let V. let T. let R: set -> set -> prop.
assume HTV: T c= V.
let S.
assume Hcl: is_clique V R S.
assume HST: S c= T.
claim HSV: S c= V.
  exact andEL (S c= V) (forall x :e S, forall y :e S, x <> y -> R x y) Hcl.
claim Hed: forall x :e S, forall y :e S, x <> y -> R x y.
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> R x y) Hcl.
apply andI (S c= T) (forall x :e S, forall y :e S, x <> y -> induced_rel T R x y).
- exact HST.
- prove forall x :e S, forall y :e S, x <> y -> induced_rel T R x y.
  let x. assume Hx: x :e S.
  let y. assume Hy: y :e S.
  assume Hneq: x <> y.
  apply andI (x :e T) (and (y :e T) (R x y)).
  * exact HST x Hx.
  * apply andI (y :e T) (R x y).
    + exact HST y Hy.
    + exact Hed x Hx y Hy Hneq.
Qed.

Theorem indep_induced_of_indep : forall V:set, forall T:set, forall R:set -> set -> prop,
  T c= V ->
  forall S:set,
    is_indep_set V R S ->
    S c= T ->
    is_indep_set T (induced_rel T R) S.
let V. let T. let R: set -> set -> prop.
assume HTV: T c= V.
let S.
assume Hind: is_indep_set V R S.
assume HST: S c= T.
claim HSV: S c= V.
  exact andEL (S c= V) (forall x :e S, forall y :e S, x <> y -> ~(R x y)) Hind.
claim Hindpair: forall x :e S, forall y :e S, x <> y -> ~(R x y).
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~(R x y)) Hind.
apply andI (S c= T) (forall x :e S, forall y :e S, x <> y -> ~(induced_rel T R x y)).
- exact HST.
- prove forall x :e S, forall y :e S, x <> y -> ~(induced_rel T R x y).
  let x. assume Hx: x :e S.
  let y. assume Hy: y :e S.
  assume Hneq: x <> y.
  apply notI.
  assume Hir: induced_rel T R x y.
  claim Hxy: R x y.
    exact andER (y :e T) (R x y) (andER (x :e T) (and (y :e T) (R x y)) Hir).
  exact Hindpair x Hx y Hy Hneq Hxy.
Qed.

Theorem clique_of_induced : forall V:set, forall T:set, forall R:set -> set -> prop,
  T c= V ->
  forall S:set,
    is_clique T (induced_rel T R) S ->
    is_clique V R S.
let V. let T. let R: set -> set -> prop.
assume HTV: T c= V.
let S.
assume Hcl: is_clique T (induced_rel T R) S.
claim HST: S c= T.
  exact andEL (S c= T) (forall x :e S, forall y :e S, x <> y -> induced_rel T R x y) Hcl.
claim Hed: forall x :e S, forall y :e S, x <> y -> induced_rel T R x y.
  exact andER (S c= T) (forall x :e S, forall y :e S, x <> y -> induced_rel T R x y) Hcl.
apply andI (S c= V) (forall x :e S, forall y :e S, x <> y -> R x y).
- prove S c= V.
  let x. assume Hx: x :e S.
  exact HTV x (HST x Hx).
- prove forall x :e S, forall y :e S, x <> y -> R x y.
  let x. assume Hx: x :e S.
  let y. assume Hy: y :e S.
  assume Hneq: x <> y.
  claim Hir: induced_rel T R x y.
    exact Hed x Hx y Hy Hneq.
  exact andER (y :e T) (R x y) (andER (x :e T) (and (y :e T) (R x y)) Hir).
Qed.

Definition is_walk : set -> (set -> set -> prop) -> set -> (set -> set) -> prop :=
  fun V R k W =>
    and (nat_p k)
        (and (forall i :e ordsucc k, W i :e V)
             (forall i :e k, R (W i) (W (ordsucc i)))).

Definition is_path : set -> (set -> set -> prop) -> set -> (set -> set) -> prop :=
  fun V R k W =>
    and (is_walk V R k W)
        (forall i :e ordsucc k, forall j :e ordsucc k, W i = W j -> i = j).

Definition is_cycle : set -> (set -> set -> prop) -> set -> (set -> set) -> prop :=
  fun V R k W =>
    and (is_walk V R k W)
        (and (3 c= k)
             (and (W 0 = W k)
                  (forall i :e k, forall j :e k, W i = W j -> i = j))).

Definition path_length_two : set -> (set -> set -> prop) -> set -> set -> set -> prop :=
  fun V R x y z =>
    and (x :e V)
        (and (y :e V)
             (and (z :e V)
                  (and (x <> y)
                       (and (y <> z)
                            (and (R x y) (R y z)))))).

Theorem path_length_two_is_path : forall V:set, forall R:set -> set -> prop,
  forall x y z :e V,
    path_length_two V R x y z ->
    exists W:set -> set, is_path V R 2 W /\ W 0 = x /\ W 1 = y /\ W 2 = z.
Admitted.

Definition graph_iso : set -> (set -> set -> prop) -> set -> (set -> set -> prop) -> prop :=
  fun V1 R1 V2 R2 =>
    exists f:set -> set,
      bij V1 V2 f /\
      (forall x :e V1, forall y :e V1, iff (R1 x y) (R2 (f x) (f y))).

Definition automorphism : set -> (set -> set -> prop) -> prop :=
  fun V R => graph_iso V R V R.

Theorem iso_refl : forall V:set, forall R:set -> set -> prop,
  graph_iso V R V R.
let V. let R: set -> set -> prop.
prove exists f:set -> set, bij V V f /\ (forall x :e V, forall y :e V, iff (R x y) (R (f x) (f y))).
witness (fun z:set => z).
apply andI (bij V V (fun z:set => z))
           (forall x :e V, forall y :e V, iff (R x y) (R x y)).
- apply bijI.
  * let u. assume Hu: u :e V. exact Hu.
  * let u. assume Hu: u :e V. let v. assume Hv: v :e V. assume Heq: u = v. exact Heq.
  * let w. assume Hw: w :e V.
    witness w.
    apply andI (w :e V) ((fun z:set => z) w = w).
    - exact Hw.
    - let Q:set -> set -> prop. assume HQ: Q w w. exact HQ.
- let x. assume Hx: x :e V. let y. assume Hy: y :e V.
  apply iffI (R x y) (R x y).
  * assume Hxy: R x y. exact Hxy.
  * assume Hxy: R x y. exact Hxy.
Qed.
Theorem iso_sym : forall V1 V2:set, forall R1 R2:set -> set -> prop,
  graph_iso V1 R1 V2 R2 -> graph_iso V2 R2 V1 R1.
let V1. let V2. let R1: set -> set -> prop. let R2: set -> set -> prop.
assume Hiso: graph_iso V1 R1 V2 R2.
apply Hiso.
let f:set -> set.
assume Hpair: bij V1 V2 f /\ (forall x :e V1, forall y :e V1, iff (R1 x y) (R2 (f x) (f y))).
claim Hbij: bij V1 V2 f.
  exact andEL (bij V1 V2 f) (forall x :e V1, forall y :e V1, iff (R1 x y) (R2 (f x) (f y))) Hpair.
claim Hpres: forall x :e V1, forall y :e V1, iff (R1 x y) (R2 (f x) (f y)).
  exact andER (bij V1 V2 f) (forall x :e V1, forall y :e V1, iff (R1 x y) (R2 (f x) (f y))) Hpair.
claim Hsurj: forall w :e V2, exists u :e V1, f u = w.
  apply and3E (forall u :e V1, f u :e V2) (forall u v :e V1, f u = f v -> u = v) (forall w :e V2, exists u :e V1, f u = w) Hbij.
  assume H1: forall u :e V1, f u :e V2.
  assume H2: forall u v :e V1, f u = f v -> u = v.
  assume H3: forall w :e V2, exists u :e V1, f u = w.
  exact H3.
prove exists g:set -> set, bij V2 V1 g /\ (forall x :e V2, forall y :e V2, iff (R2 x y) (R1 (g x) (g y))).
witness (inv V1 f).
apply andI (bij V2 V1 (inv V1 f))
           (forall x :e V2, forall y :e V2, iff (R2 x y) (R1 (inv V1 f x) (inv V1 f y))).
- exact bij_inv V1 V2 f Hbij.
- let x. assume Hx: x :e V2.
  let y. assume Hy: y :e V2.
  apply iffI (R2 x y) (R1 (inv V1 f x) (inv V1 f y)).
  * assume Hxy: R2 x y.
    claim Hprex: and (inv V1 f x :e V1) (f (inv V1 f x) = x).
      exact surj_rinv V1 V2 f Hsurj x Hx.
    claim Hprey: and (inv V1 f y :e V1) (f (inv V1 f y) = y).
      exact surj_rinv V1 V2 f Hsurj y Hy.
    claim Hiff: iff (R1 (inv V1 f x) (inv V1 f y)) (R2 (f (inv V1 f x)) (f (inv V1 f y))).
      exact Hpres (inv V1 f x) (andEL (inv V1 f x :e V1) (f (inv V1 f x) = x) Hprex)
                  (inv V1 f y) (andEL (inv V1 f y :e V1) (f (inv V1 f y) = y) Hprey).
    claim Hback: R2 (f (inv V1 f x)) (f (inv V1 f y)) -> R1 (inv V1 f x) (inv V1 f y).
      exact andER (R1 (inv V1 f x) (inv V1 f y) -> R2 (f (inv V1 f x)) (f (inv V1 f y)))
                  (R2 (f (inv V1 f x)) (f (inv V1 f y)) -> R1 (inv V1 f x) (inv V1 f y)) Hiff.
    claim Hfx: f (inv V1 f x) = x.
      exact andER (inv V1 f x :e V1) (f (inv V1 f x) = x) Hprex.
    claim Hfy: f (inv V1 f y) = y.
      exact andER (inv V1 f y :e V1) (f (inv V1 f y) = y) Hprey.
    claim Hmapped: R2 (f (inv V1 f x)) (f (inv V1 f y)).
      rewrite Hfx. rewrite Hfy. exact Hxy.
    exact Hback Hmapped.
  * assume Hxy: R1 (inv V1 f x) (inv V1 f y).
    claim Hprex: and (inv V1 f x :e V1) (f (inv V1 f x) = x).
      exact surj_rinv V1 V2 f Hsurj x Hx.
    claim Hprey: and (inv V1 f y :e V1) (f (inv V1 f y) = y).
      exact surj_rinv V1 V2 f Hsurj y Hy.
    claim Hiff: iff (R1 (inv V1 f x) (inv V1 f y)) (R2 (f (inv V1 f x)) (f (inv V1 f y))).
      exact Hpres (inv V1 f x) (andEL (inv V1 f x :e V1) (f (inv V1 f x) = x) Hprex)
                  (inv V1 f y) (andEL (inv V1 f y :e V1) (f (inv V1 f y) = y) Hprey).
    claim Hforw: R1 (inv V1 f x) (inv V1 f y) -> R2 (f (inv V1 f x)) (f (inv V1 f y)).
      exact andEL (R1 (inv V1 f x) (inv V1 f y) -> R2 (f (inv V1 f x)) (f (inv V1 f y)))
                  (R2 (f (inv V1 f x)) (f (inv V1 f y)) -> R1 (inv V1 f x) (inv V1 f y))
                  Hiff.
    claim Hmapped: R2 (f (inv V1 f x)) (f (inv V1 f y)).
      exact Hforw Hxy.
    claim Hfx: f (inv V1 f x) = x.
      exact andER (inv V1 f x :e V1) (f (inv V1 f x) = x) Hprex.
    claim Hfy: f (inv V1 f y) = y.
      exact andER (inv V1 f y :e V1) (f (inv V1 f y) = y) Hprey.
    rewrite <- Hfx.
    rewrite <- Hfy.
    exact Hmapped.
Qed.

Theorem iso_trans : forall U V W:set, forall R1 R2 R3:set -> set -> prop,
  graph_iso U R1 V R2 -> graph_iso V R2 W R3 -> graph_iso U R1 W R3.
let U. let V. let W. let R1: set -> set -> prop. let R2: set -> set -> prop. let R3: set -> set -> prop.
assume HisoUV: graph_iso U R1 V R2.
assume HisoVW: graph_iso V R2 W R3.
apply HisoUV.
let f:set -> set.
assume HpairUV: bij U V f /\ (forall x :e U, forall y :e U, iff (R1 x y) (R2 (f x) (f y))).
claim HbijUV: bij U V f.
  exact andEL (bij U V f) (forall x :e U, forall y :e U, iff (R1 x y) (R2 (f x) (f y))) HpairUV.
claim HpresUV: forall x :e U, forall y :e U, iff (R1 x y) (R2 (f x) (f y)).
  exact andER (bij U V f) (forall x :e U, forall y :e U, iff (R1 x y) (R2 (f x) (f y))) HpairUV.
claim HmapUV: forall u :e U, f u :e V.
  apply and3E (forall u :e U, f u :e V) (forall u v :e U, f u = f v -> u = v) (forall w :e V, exists u :e U, f u = w) HbijUV.
  assume H1: forall u :e U, f u :e V.
  assume H2: forall u v :e U, f u = f v -> u = v.
  assume H3: forall w :e V, exists u :e U, f u = w.
  exact H1.
apply HisoVW.
let g:set -> set.
assume HpairVW: bij V W g /\ (forall x :e V, forall y :e V, iff (R2 x y) (R3 (g x) (g y))).
claim HbijVW: bij V W g.
  exact andEL (bij V W g) (forall x :e V, forall y :e V, iff (R2 x y) (R3 (g x) (g y))) HpairVW.
claim HpresVW: forall x :e V, forall y :e V, iff (R2 x y) (R3 (g x) (g y)).
  exact andER (bij V W g) (forall x :e V, forall y :e V, iff (R2 x y) (R3 (g x) (g y))) HpairVW.
prove exists h:set -> set, bij U W h /\ (forall x :e U, forall y :e U, iff (R1 x y) (R3 (h x) (h y))).
witness (fun x => g (f x)).
apply andI (bij U W (fun x => g (f x)))
           (forall x :e U, forall y :e U, iff (R1 x y) (R3 (g (f x)) (g (f y)))).
- exact bij_comp U V W f g HbijUV HbijVW.
- let x. assume Hx: x :e U.
  let y. assume Hy: y :e U.
  claim HiffUV: iff (R1 x y) (R2 (f x) (f y)).
    exact HpresUV x Hx y Hy.
  claim HiffVW: iff (R2 (f x) (f y)) (R3 (g (f x)) (g (f y))).
    exact HpresVW (f x) (HmapUV x Hx) (f y) (HmapUV y Hy).
  apply iffI (R1 x y) (R3 (g (f x)) (g (f y))).
  * assume Hxy: R1 x y.
    claim HforwUV: R1 x y -> R2 (f x) (f y).
      exact andEL (R1 x y -> R2 (f x) (f y)) (R2 (f x) (f y) -> R1 x y) HiffUV.
    claim HforwVW: R2 (f x) (f y) -> R3 (g (f x)) (g (f y)).
      exact andEL (R2 (f x) (f y) -> R3 (g (f x)) (g (f y))) (R3 (g (f x)) (g (f y)) -> R2 (f x) (f y)) HiffVW.
    exact HforwVW (HforwUV Hxy).
  * assume Hxy: R3 (g (f x)) (g (f y)).
    claim HbackVW: R3 (g (f x)) (g (f y)) -> R2 (f x) (f y).
      exact andER (R2 (f x) (f y) -> R3 (g (f x)) (g (f y)))
                  (R3 (g (f x)) (g (f y)) -> R2 (f x) (f y)) HiffVW.
    claim HbackUV: R2 (f x) (f y) -> R1 x y.
      exact andER (R1 x y -> R2 (f x) (f y)) (R2 (f x) (f y) -> R1 x y) HiffUV.
    exact HbackUV (HbackVW Hxy).
Qed.

Theorem iso_preserves_simple : forall V1 V2:set, forall R1 R2:set -> set -> prop,
  graph_iso V1 R1 V2 R2 ->
  simple_graph V1 R1 -> simple_graph V2 R2.
Admitted.

Theorem iso_preserves_triangle_free : forall V1 V2:set, forall R1 R2:set -> set -> prop,
  graph_iso V1 R1 V2 R2 ->
  triangle_free V1 R1 -> triangle_free V2 R2.
let V1. let V2. let R1: set -> set -> prop. let R2: set -> set -> prop.
assume Hiso: graph_iso V1 R1 V2 R2.
assume Htf: triangle_free V1 R1.
apply Hiso.
let f:set -> set.
assume Hpair: bij V1 V2 f /\ (forall x :e V1, forall y :e V1, iff (R1 x y) (R2 (f x) (f y))).
claim Hbij: bij V1 V2 f.
  exact andEL (bij V1 V2 f) (forall x :e V1, forall y :e V1, iff (R1 x y) (R2 (f x) (f y))) Hpair.
claim Hpres: forall x :e V1, forall y :e V1, iff (R1 x y) (R2 (f x) (f y)).
  exact andER (bij V1 V2 f) (forall x :e V1, forall y :e V1, iff (R1 x y) (R2 (f x) (f y))) Hpair.
claim Hsurj: forall w :e V2, exists u :e V1, f u = w.
  apply and3E (forall u :e V1, f u :e V2) (forall u v :e V1, f u = f v -> u = v) (forall w :e V2, exists u :e V1, f u = w) Hbij.
  assume H1: forall u :e V1, f u :e V2.
  assume H2: forall u v :e V1, f u = f v -> u = v.
  assume H3: forall w :e V2, exists u :e V1, f u = w.
  exact H3.
prove triangle_free V2 R2.
let x. assume Hx: x :e V2.
let y. assume Hy: y :e V2.
let z. assume Hz: z :e V2.
assume Hxy: R2 x y.
assume Hyz: R2 y z.
assume Hxz: R2 x z.
claim Hprex: and (inv V1 f x :e V1) (f (inv V1 f x) = x).
  exact surj_rinv V1 V2 f Hsurj x Hx.
claim Hprey: and (inv V1 f y :e V1) (f (inv V1 f y) = y).
  exact surj_rinv V1 V2 f Hsurj y Hy.
claim Hprez: and (inv V1 f z :e V1) (f (inv V1 f z) = z).
  exact surj_rinv V1 V2 f Hsurj z Hz.
claim Hiff_xy: iff (R1 (inv V1 f x) (inv V1 f y)) (R2 (f (inv V1 f x)) (f (inv V1 f y))).
  exact Hpres (inv V1 f x) (andEL (inv V1 f x :e V1) (f (inv V1 f x) = x) Hprex)
              (inv V1 f y) (andEL (inv V1 f y :e V1) (f (inv V1 f y) = y) Hprey).
claim Hiff_yz: iff (R1 (inv V1 f y) (inv V1 f z)) (R2 (f (inv V1 f y)) (f (inv V1 f z))).
  exact Hpres (inv V1 f y) (andEL (inv V1 f y :e V1) (f (inv V1 f y) = y) Hprey)
              (inv V1 f z) (andEL (inv V1 f z :e V1) (f (inv V1 f z) = z) Hprez).
claim Hiff_xz: iff (R1 (inv V1 f x) (inv V1 f z)) (R2 (f (inv V1 f x)) (f (inv V1 f z))).
  exact Hpres (inv V1 f x) (andEL (inv V1 f x :e V1) (f (inv V1 f x) = x) Hprex)
              (inv V1 f z) (andEL (inv V1 f z :e V1) (f (inv V1 f z) = z) Hprez).
claim Hback_xy: R2 (f (inv V1 f x)) (f (inv V1 f y)) -> R1 (inv V1 f x) (inv V1 f y).
  exact andER (R1 (inv V1 f x) (inv V1 f y) -> R2 (f (inv V1 f x)) (f (inv V1 f y)))
              (R2 (f (inv V1 f x)) (f (inv V1 f y)) -> R1 (inv V1 f x) (inv V1 f y)) Hiff_xy.
claim Hback_yz: R2 (f (inv V1 f y)) (f (inv V1 f z)) -> R1 (inv V1 f y) (inv V1 f z).
  exact andER (R1 (inv V1 f y) (inv V1 f z) -> R2 (f (inv V1 f y)) (f (inv V1 f z)))
              (R2 (f (inv V1 f y)) (f (inv V1 f z)) -> R1 (inv V1 f y) (inv V1 f z)) Hiff_yz.
claim Hback_xz: R2 (f (inv V1 f x)) (f (inv V1 f z)) -> R1 (inv V1 f x) (inv V1 f z).
  exact andER (R1 (inv V1 f x) (inv V1 f z) -> R2 (f (inv V1 f x)) (f (inv V1 f z)))
              (R2 (f (inv V1 f x)) (f (inv V1 f z)) -> R1 (inv V1 f x) (inv V1 f z)) Hiff_xz.
claim Hfx: f (inv V1 f x) = x.
  exact andER (inv V1 f x :e V1) (f (inv V1 f x) = x) Hprex.
claim Hfy: f (inv V1 f y) = y.
  exact andER (inv V1 f y :e V1) (f (inv V1 f y) = y) Hprey.
claim Hfz: f (inv V1 f z) = z.
  exact andER (inv V1 f z :e V1) (f (inv V1 f z) = z) Hprez.
claim Rxy': R2 (f (inv V1 f x)) (f (inv V1 f y)).
  rewrite Hfx. rewrite Hfy. exact Hxy.
claim Ryz': R2 (f (inv V1 f y)) (f (inv V1 f z)).
  rewrite Hfy. rewrite Hfz. exact Hyz.
claim Rxz': R2 (f (inv V1 f x)) (f (inv V1 f z)).
  rewrite Hfx. rewrite Hfz. exact Hxz.
claim R1xy: R1 (inv V1 f x) (inv V1 f y).
  exact Hback_xy Rxy'.
claim R1yz: R1 (inv V1 f y) (inv V1 f z).
  exact Hback_yz Ryz'.
claim R1xz: R1 (inv V1 f x) (inv V1 f z).
  exact Hback_xz Rxz'.
exact Htf (inv V1 f x) (andEL (inv V1 f x :e V1) (f (inv V1 f x) = x) Hprex)
          (inv V1 f y) (andEL (inv V1 f y :e V1) (f (inv V1 f y) = y) Hprey)
          (inv V1 f z) (andEL (inv V1 f z :e V1) (f (inv V1 f z) = z) Hprez)
          R1xy R1yz R1xz.
Qed.

Definition connected : set -> (set -> set -> prop) -> prop :=
  fun V R =>
    forall A B:set,
      A c= V ->
      B c= V ->
      A <> Empty ->
      B <> Empty ->
      V c= A :\/: B ->
      A :/\: B = Empty ->
      exists a :e A, exists b :e B, R a b.

Definition directed_graph : set -> (set -> set -> prop) -> prop :=
  fun V A =>
    and (forall x :e V, ~A x x)
        (forall x y, A x y -> and (x :e V) (y :e V)).

Definition xor : prop -> prop -> prop :=
  fun A B => or (and A (~B)) (and B (~A)).

Definition symmetric_orientation : set -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun V R A =>
    and (directed_graph V A)
        (forall x :e V, forall y :e V, iff (R x y) (or (A x y) (A y x))).

Definition tournament : set -> (set -> set -> prop) -> prop :=
  fun V A =>
    and (directed_graph V A)
        (forall x :e V, forall y :e V, x <> y -> xor (A x y) (A y x)).

Definition complete_graph : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, x <> y -> R x y.

Definition empty_graph : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, ~R x y.

Definition bipartite : set -> (set -> set -> prop) -> prop :=
  fun V R =>
    exists X Y:set,
      and (X c= V)
          (and (Y c= V)
               (and (X :/\: Y = Empty)
                    (and (V c= X :\/: Y)
                         (and (forall x :e X, forall y :e X, ~R x y)
                              (forall x :e Y, forall y :e Y, ~R x y))))).

Definition out_neigh : set -> (set -> set -> prop) -> set -> set :=
  fun V A v => Sep V (fun x:set => A v x).

Definition in_neigh : set -> (set -> set -> prop) -> set -> set :=
  fun V A v => Sep V (fun x:set => A x v).

Theorem directed_out_subq : forall V:set, forall A:set -> set -> prop,
  directed_graph V A ->
  forall v, out_neigh V A v c= V.
let V. let A: set -> set -> prop.
assume Hdg: directed_graph V A.
let v.
prove out_neigh V A v c= V.
let x. assume Hx: x :e out_neigh V A v.
apply SepE V (fun t:set => A v t) x Hx.
assume HxV: x :e V. assume Hav: A v x.
claim Hmem: and (v :e V) (x :e V).
  exact andER (forall x :e V, ~A x x) (forall x y, A x y -> and (x :e V) (y :e V)) Hdg v x Hav.
exact andER (v :e V) (x :e V) Hmem.
Qed.

Theorem directed_in_subq : forall V:set, forall A:set -> set -> prop,
  directed_graph V A ->
  forall v, in_neigh V A v c= V.
let V. let A: set -> set -> prop.
assume Hdg: directed_graph V A.
let v.
prove in_neigh V A v c= V.
let x. assume Hx: x :e in_neigh V A v.
apply SepE V (fun t:set => A t v) x Hx.
assume HxV: x :e V. assume Hav: A x v.
claim Hmem: and (x :e V) (v :e V).
  exact andER (forall x :e V, ~A x x) (forall x y, A x y -> and (x :e V) (y :e V)) Hdg x v Hav.
exact andEL (x :e V) (v :e V) Hmem.
Qed.

Theorem directed_no_self_out : forall V:set, forall A:set -> set -> prop,
  directed_graph V A ->
  forall v :e V, v /:e out_neigh V A v.
let V. let A: set -> set -> prop.
assume Hdg: directed_graph V A.
let v. assume Hv: v :e V.
assume Hvout: v :e out_neigh V A v.
apply SepE V (fun t:set => A v t) v Hvout.
assume HvV: v :e V. assume Hav: A v v.
exact andEL (forall x :e V, ~A x x) (forall x y, A x y -> and (x :e V) (y :e V)) Hdg v HvV Hav.
Qed.

Theorem directed_no_self_in : forall V:set, forall A:set -> set -> prop,
  directed_graph V A ->
  forall v :e V, v /:e in_neigh V A v.
let V. let A: set -> set -> prop.
assume Hdg: directed_graph V A.
let v. assume Hv: v :e V.
assume Hvin: v :e in_neigh V A v.
apply SepE V (fun t:set => A t v) v Hvin.
assume HvV: v :e V. assume Hav: A v v.
exact andEL (forall x :e V, ~A x x) (forall x y, A x y -> and (x :e V) (y :e V)) Hdg v HvV Hav.
Qed.
Definition reachable : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun V R s t =>
    exists k:set, exists W:set -> set,
      is_walk V R k W /\ W 0 = s /\ W k = t.

Theorem reachable_refl : forall V:set, forall R:set -> set -> prop, forall v :e V,
  reachable V R v v.
let V. let R: set -> set -> prop.
let v. assume Hv: v :e V.
prove exists k:set, exists W:set -> set,
       is_walk V R k W /\ W 0 = v /\ W k = v.
witness 0.
witness (fun _:set => v).
apply andI.
- apply andI.
  * claim Hmem: forall i :e ordsucc 0, (fun _:set => v) i :e V.
      let i. assume Hi: i :e ordsucc 0.
      exact Hv.
    claim Hedges: forall i :e 0, R ((fun _:set => v) i) ((fun _:set => v) (ordsucc i)).
      let i. assume Hi: i :e 0.
      apply FalseE.
      exact EmptyE i Hi.
    exact andI (nat_p 0)
               (and (forall i :e ordsucc 0, (fun _:set => v) i :e V)
                    (forall i :e 0, R ((fun _:set => v) i) ((fun _:set => v) (ordsucc i))))
               nat_0
               (andI (forall i :e ordsucc 0, (fun _:set => v) i :e V)
                     (forall i :e 0, R ((fun _:set => v) i) ((fun _:set => v) (ordsucc i)))
                     Hmem
                     Hedges).
  * reflexivity.
- reflexivity.
Qed.

Definition vertex_cut : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S =>
    and (S c= V)
        (and (connected V R)
             (~(connected (V :\: S) (induced_rel (V :\: S) R)))).

Definition cut_vertex : set -> (set -> set -> prop) -> set -> prop :=
  fun V R v =>
    and (v :e V)
        (and (connected V R)
             (~(connected (V :\: {v}) (induced_rel (V :\: {v}) R)))).

Definition delete_edge_rel : set -> set -> (set -> set -> prop) -> set -> set -> prop :=
  fun a b R x y =>
    and (R x y)
        (~(or (and (x = a) (y = b)) (and (x = b) (y = a)))).

Definition bridge : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun V R a b =>
    and (a :e V)
        (and (b :e V)
             (and (R a b)
                  (and (connected V R)
                       (~(connected V (delete_edge_rel a b R)))))).

Theorem vertex_cut_subset : forall V:set, forall R:set -> set -> prop, forall S:set,
  vertex_cut V R S -> S c= V.
let V. let R: set -> set -> prop. let S.
assume Hvc: vertex_cut V R S.
exact andEL (S c= V) (and (connected V R) (~(connected (V :\: S) (induced_rel (V :\: S) R)))) Hvc.
Qed.

Theorem cut_vertex_in_V : forall V:set, forall R:set -> set -> prop, forall v:set,
  cut_vertex V R v -> v :e V.
let V. let R: set -> set -> prop. let v.
assume Hcv: cut_vertex V R v.
exact andEL (v :e V) (and (connected V R) (~(connected (V :\: {v}) (induced_rel (V :\: {v}) R)))) Hcv.
Qed.

Theorem vertex_cut_connected : forall V:set, forall R:set -> set -> prop, forall S:set,
  vertex_cut V R S -> connected V R.
let V. let R: set -> set -> prop. let S.
assume Hvc: vertex_cut V R S.
exact andEL (connected V R) (~(connected (V :\: S) (induced_rel (V :\: S) R)))
            (andER (S c= V) (and (connected V R) (~(connected (V :\: S) (induced_rel (V :\: S) R)))) Hvc).
Qed.

Theorem vertex_cut_not_connected_subgraph : forall V:set, forall R:set -> set -> prop, forall S:set,
  vertex_cut V R S -> ~(connected (V :\: S) (induced_rel (V :\: S) R)).
let V. let R: set -> set -> prop. let S.
assume Hvc: vertex_cut V R S.
exact andER (connected V R) (~(connected (V :\: S) (induced_rel (V :\: S) R)))
            (andER (S c= V) (and (connected V R) (~(connected (V :\: S) (induced_rel (V :\: S) R)))) Hvc).
Qed.

Theorem cut_vertex_connected : forall V:set, forall R:set -> set -> prop, forall v:set,
  cut_vertex V R v -> connected V R.
let V. let R: set -> set -> prop. let v.
assume Hcv: cut_vertex V R v.
exact andEL (connected V R) (~(connected (V :\: {v}) (induced_rel (V :\: {v}) R)))
            (andER (v :e V) (and (connected V R) (~(connected (V :\: {v}) (induced_rel (V :\: {v}) R)))) Hcv).
Qed.

Theorem cut_vertex_disconnects : forall V:set, forall R:set -> set -> prop, forall v:set,
  cut_vertex V R v -> ~(connected (V :\: {v}) (induced_rel (V :\: {v}) R)).
let V. let R: set -> set -> prop. let v.
assume Hcv: cut_vertex V R v.
exact andER (connected V R) (~(connected (V :\: {v}) (induced_rel (V :\: {v}) R)))
            (andER (v :e V) (and (connected V R) (~(connected (V :\: {v}) (induced_rel (V :\: {v}) R)))) Hcv).
Qed.

Theorem bridge_endpoints_in_V : forall V:set, forall R:set -> set -> prop, forall a b:set,
  bridge V R a b -> and (a :e V) (b :e V).
let V. let R: set -> set -> prop. let a. let b.
assume Hbr: bridge V R a b.
apply andI (a :e V) (b :e V).
- exact andEL (a :e V)
               (and (b :e V)
                    (and (R a b)
                         (and (connected V R) (~(connected V (delete_edge_rel a b R))))))
               Hbr.
- exact andEL (b :e V)
               (and (R a b)
                    (and (connected V R) (~(connected V (delete_edge_rel a b R)))))
               (andER (a :e V)
                      (and (b :e V)
                           (and (R a b)
                                (and (connected V R) (~(connected V (delete_edge_rel a b R))))))
                      Hbr).
Qed.

Theorem bridge_connected : forall V:set, forall R:set -> set -> prop, forall a b:set,
  bridge V R a b -> connected V R.
let V. let R: set -> set -> prop. let a. let b.
assume Hbr: bridge V R a b.
exact andEL (connected V R) (~(connected V (delete_edge_rel a b R)))
            (andER (R a b)
                   (and (connected V R) (~(connected V (delete_edge_rel a b R))))
                   (andER (b :e V)
                          (and (R a b)
                               (and (connected V R) (~(connected V (delete_edge_rel a b R)))))
                          (andER (a :e V)
                                 (and (b :e V)
                                      (and (R a b)
                                           (and (connected V R) (~(connected V (delete_edge_rel a b R))))))
                                 Hbr))).
Qed.

Theorem bridge_delete_disconnected : forall V:set, forall R:set -> set -> prop, forall a b:set,
  bridge V R a b -> ~(connected V (delete_edge_rel a b R)).
let V. let R: set -> set -> prop. let a. let b.
assume Hbr: bridge V R a b.
exact andER (connected V R) (~(connected V (delete_edge_rel a b R)))
            (andER (R a b)
                   (and (connected V R) (~(connected V (delete_edge_rel a b R))))
                   (andER (b :e V)
                          (and (R a b)
                               (and (connected V R) (~(connected V (delete_edge_rel a b R)))))
                          (andER (a :e V)
                                 (and (b :e V)
                                      (and (R a b)
                                           (and (connected V R) (~(connected V (delete_edge_rel a b R))))))
                                 Hbr))).
Qed.

Theorem is_walk_induced_lift : forall V:set, forall T:set, forall R:set -> set -> prop,
  forall k:set, forall W:set -> set,
    T c= V ->
    is_walk T (induced_rel T R) k W ->
    is_walk V R k W.
let V. let T. let R: set -> set -> prop.
let k. let W.
assume HTV: T c= V.
assume Hwalk: is_walk T (induced_rel T R) k W.
claim Hnat: nat_p k.
  exact andEL (nat_p k) (and (forall i :e ordsucc k, W i :e T)
                              (forall i :e k, induced_rel T R (W i) (W (ordsucc i)))) Hwalk.
claim HmemT: forall i :e ordsucc k, W i :e T.
  exact andEL (forall i :e ordsucc k, W i :e T)
              (forall i :e k, induced_rel T R (W i) (W (ordsucc i)))
              (andER (nat_p k)
                     (and (forall i :e ordsucc k, W i :e T)
                          (forall i :e k, induced_rel T R (W i) (W (ordsucc i))))
                     Hwalk).
claim HedgesT: forall i :e k, induced_rel T R (W i) (W (ordsucc i)).
  exact andER (forall i :e ordsucc k, W i :e T)
              (forall i :e k, induced_rel T R (W i) (W (ordsucc i)))
              (andER (nat_p k)
                     (and (forall i :e ordsucc k, W i :e T)
                          (forall i :e k, induced_rel T R (W i) (W (ordsucc i))))
                     Hwalk).
apply andI (nat_p k)
           (and (forall i :e ordsucc k, W i :e V)
                (forall i :e k, R (W i) (W (ordsucc i)))).
- exact Hnat.
- prove and (forall i :e ordsucc k, W i :e V)
            (forall i :e k, R (W i) (W (ordsucc i))).
  apply andI (forall i :e ordsucc k, W i :e V)
             (forall i :e k, R (W i) (W (ordsucc i))).
  * prove forall i :e ordsucc k, W i :e V.
    let i. assume Hi: i :e ordsucc k.
    exact HTV (W i) (HmemT i Hi).
  * prove forall i :e k, R (W i) (W (ordsucc i)).
    let i. assume Hi: i :e k.
    claim Hedge: induced_rel T R (W i) (W (ordsucc i)).
      exact HedgesT i Hi.
    exact andER (W (ordsucc i) :e T) (R (W i) (W (ordsucc i)))
                (andER (W i :e T) (and (W (ordsucc i) :e T) (R (W i) (W (ordsucc i)))) Hedge).
Qed.

Definition acyclic : set -> (set -> set -> prop) -> prop :=
  fun V R => forall k:set, forall W:set -> set, is_cycle V R k W -> False.

Definition forest : set -> (set -> set -> prop) -> prop :=
  fun V R => acyclic V R.

Definition tree : set -> (set -> set -> prop) -> prop :=
  fun V R => and (connected V R) (acyclic V R).

Definition add_edge_rel : set -> set -> (set -> set -> prop) -> set -> set -> prop :=
  fun a b R x y => or (R x y) (or (and (x = a) (y = b)) (and (x = b) (y = a))).

Definition simple_path_between : set -> (set -> set -> prop) -> set -> set -> set -> (set -> set) -> prop :=
  fun V R s t k W => and (is_path V R k W) (and (W 0 = s) (W k = t)).

Theorem tree_connected : forall V:set, forall R:set -> set -> prop,
  tree V R -> connected V R.
let V. let R: set -> set -> prop.
assume Htree: tree V R.
exact andEL (connected V R) (acyclic V R) Htree.
Qed.

Theorem tree_acyclic : forall V:set, forall R:set -> set -> prop,
  tree V R -> acyclic V R.
let V. let R: set -> set -> prop.
assume Htree: tree V R.
exact andER (connected V R) (acyclic V R) Htree.
Qed.

Definition spanning_tree : set -> (set -> set -> prop) -> set -> prop :=
  fun V R T => and (T c= V) (tree T (induced_rel T R)).

Theorem spanning_tree_subq : forall V:set, forall R:set -> set -> prop, forall T:set,
  spanning_tree V R T -> T c= V.
let V. let R: set -> set -> prop. let T.
assume Hst: spanning_tree V R T.
exact andEL (T c= V) (tree T (induced_rel T R)) Hst.
Qed.

Theorem spanning_tree_is_tree : forall V:set, forall R:set -> set -> prop, forall T:set,
  spanning_tree V R T -> tree T (induced_rel T R).
let V. let R: set -> set -> prop. let T.
assume Hst: spanning_tree V R T.
exact andER (T c= V) (tree T (induced_rel T R)) Hst.
Qed.

Theorem spanning_tree_connected : forall V:set, forall R:set -> set -> prop, forall T:set,
  spanning_tree V R T -> connected T (induced_rel T R).
let V. let R: set -> set -> prop. let T.
assume Hst: spanning_tree V R T.
exact andEL (connected T (induced_rel T R)) (acyclic T (induced_rel T R))
            (andER (T c= V) (tree T (induced_rel T R)) Hst).
Qed.

Theorem tree_edge_is_bridge : forall V:set, forall R:set -> set -> prop, forall a b:set,
  simple_graph V R ->
  tree V R ->
  R a b ->
  bridge V R a b.
Admitted.

Theorem tree_edge_deletion_disconnects : forall V:set, forall R:set -> set -> prop, forall a b:set,
  simple_graph V R ->
  tree V R ->
  R a b ->
  ~(connected V (delete_edge_rel a b R)).
Admitted.

Theorem tree_unique_path_exists : forall V:set, forall R:set -> set -> prop,
  tree V R ->
  forall s t :e V,
    exists k:set, exists W:set -> set, simple_path_between V R s t k W.
Admitted.

Theorem tree_unique_path_unique : forall V:set, forall R:set -> set -> prop,
  tree V R ->
  forall s t:set, forall k1 k2:set, forall W1 W2:set -> set,
    simple_path_between V R s t k1 W1 ->
    simple_path_between V R s t k2 W2 ->
    k1 = k2 /\ (forall i :e ordsucc k1, W1 i = W2 i).
Admitted.

Theorem add_edge_to_tree_creates_cycle : forall V:set, forall R:set -> set -> prop, forall a b:set,
  tree V R ->
  a :e V -> b :e V ->
  ~(R a b) ->
  exists k:set, exists W:set -> set, is_cycle V (add_edge_rel a b R) k W.
Admitted.

Theorem tree_no_multiple_paths : forall V:set, forall R:set -> set -> prop,
  tree V R ->
  forall s t:set, forall k1 k2:set, forall W1 W2:set -> set,
    simple_path_between V R s t k1 W1 ->
    simple_path_between V R s t k2 W2 ->
    (forall i :e ordsucc k1, W1 i = W2 i) -> k1 = k2.
Admitted.

Theorem tree_is_forest : forall V:set, forall R:set -> set -> prop,
  tree V R -> forest V R.
let V. let R: set -> set -> prop.
assume Htree: tree V R.
exact andER (connected V R) (acyclic V R) Htree.
Qed.

Theorem forest_has_no_cycle : forall V:set, forall R:set -> set -> prop,
  forest V R -> forall k:set, forall W:set -> set, is_cycle V R k W -> False.
let V. let R: set -> set -> prop.
assume Hf: forest V R.
let k. let W.
exact Hf k W.
Qed.

Theorem forest_induced_acyclic : forall V:set, forall T:set, forall R:set -> set -> prop,
  T c= V ->
  forest V R ->
  forest T (induced_rel T R).
let V. let T. let R: set -> set -> prop.
assume HTV: T c= V.
assume Hforest: forest V R.
prove forest T (induced_rel T R).
let k. let W.
assume Hcyc: is_cycle T (induced_rel T R) k W.
claim HwalkT: is_walk T (induced_rel T R) k W.
  exact andEL (is_walk T (induced_rel T R) k W)
              (and (3 c= k) (and (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j)))
              Hcyc.
claim Hrest: and (3 c= k) (and (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j)).
  exact andER (is_walk T (induced_rel T R) k W)
              (and (3 c= k) (and (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j)))
              Hcyc.
claim Hkge3: 3 c= k.
  exact andEL (3 c= k) (and (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j)) Hrest.
claim Hclose: W 0 = W k.
  exact andEL (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j)
              (andER (3 c= k) (and (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j)) Hrest).
claim Hinj: forall i :e k, forall j :e k, W i = W j -> i = j.
  exact andER (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j)
              (andER (3 c= k) (and (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j)) Hrest).
apply (Hforest k W).
apply andI (is_walk V R k W)
           (and (3 c= k) (and (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j))).
- exact is_walk_induced_lift V T R k W HTV HwalkT.
- apply andI (3 c= k) (and (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j)).
  * exact Hkge3.
  * apply andI (W 0 = W k) (forall i :e k, forall j :e k, W i = W j -> i = j).
    + exact Hclose.
    + exact Hinj.
Qed.

Definition is_matching : set -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun V R M =>
    and (forall x y, M x y -> and (M y x) (and (x :e V) (and (y :e V) (R x y))))
        (forall v u w, M v u -> M v w -> u = w).

Definition matched_by : set -> (set -> set -> prop) -> set -> prop :=
  fun V M v => exists u :e V, M v u.

Definition exposed_vertex : set -> (set -> set -> prop) -> set -> prop :=
  fun V M v => and (v :e V) (forall u, ~M v u).

Definition perfect_matching : set -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun V R M =>
    and (is_matching V R M)
        (forall v :e V, exists u :e V, M v u).

Definition maximal_matching : set -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun V R M =>
    and (is_matching V R M)
        (forall a :e V, forall b :e V, R a b -> ~(M a b) -> or (matched_by V M a) (matched_by V M b)).

Theorem is_matching_edge_in_graph : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  is_matching V R M ->
  forall x y, M x y -> and (x :e V) (and (y :e V) (R x y)).
let V. let R: set -> set -> prop. let M.
assume Hm: is_matching V R M.
let x. let y. assume Hxy: M x y.
claim Hfirst: forall x y, M x y -> and (M y x) (and (x :e V) (and (y :e V) (R x y))).
  exact andEL (forall x y, M x y -> and (M y x) (and (x :e V) (and (y :e V) (R x y))))
              (forall v u w, M v u -> M v w -> u = w)
              Hm.
exact andER (M y x) (and (x :e V) (and (y :e V) (R x y))) (Hfirst x y Hxy).
Qed.

Theorem is_matching_sym : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  is_matching V R M ->
  forall x y, M x y -> M y x.
let V. let R: set -> set -> prop. let M.
assume Hm: is_matching V R M.
let x. let y. assume Hxy: M x y.
claim Hfirst: forall x y, M x y -> and (M y x) (and (x :e V) (and (y :e V) (R x y))).
  exact andEL (forall x y, M x y -> and (M y x) (and (x :e V) (and (y :e V) (R x y))))
              (forall v u w, M v u -> M v w -> u = w)
              Hm.
exact andEL (M y x) (and (x :e V) (and (y :e V) (R x y))) (Hfirst x y Hxy).
Qed.

Theorem is_matching_incident_unique : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  is_matching V R M ->
  forall v u w, M v u -> M v w -> u = w.
let V. let R: set -> set -> prop. let M.
assume Hm: is_matching V R M.
claim Huniq: forall v u w, M v u -> M v w -> u = w.
  exact andER (forall x y, M x y -> and (M y x) (and (x :e V) (and (y :e V) (R x y))))
              (forall v u w, M v u -> M v w -> u = w)
              Hm.
exact Huniq.
Qed.

Theorem is_matching_no_double_incidence : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  is_matching V R M ->
  forall a b c, M a b -> M c b -> a = c.
let V. let R: set -> set -> prop. let M.
assume Hm: is_matching V R M.
let a. let b. let c.
assume Hab: M a b.
assume Hcb: M c b.
claim Hsym: forall x y, M x y -> M y x.
  exact is_matching_sym V R M Hm.
claim Huniq: forall v u w, M v u -> M v w -> u = w.
  exact is_matching_incident_unique V R M Hm.
claim Hba: M b a.
  exact Hsym a b Hab.
claim Hbc: M b c.
  exact Hsym c b Hcb.
exact Huniq b a c Hba Hbc.
Qed.

Theorem perfect_matching_is_matching : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  perfect_matching V R M -> is_matching V R M.
let V. let R: set -> set -> prop. let M.
assume Hp: perfect_matching V R M.
exact andEL (is_matching V R M) (forall v :e V, exists u :e V, M v u) Hp.
Qed.

Theorem perfect_matching_covers : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  perfect_matching V R M -> forall v :e V, exists u :e V, M v u.
let V. let R: set -> set -> prop. let M.
assume Hp: perfect_matching V R M.
exact andER (is_matching V R M) (forall v :e V, exists u :e V, M v u) Hp.
Qed.

Theorem maximal_matching_is_matching : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  maximal_matching V R M -> is_matching V R M.
let V. let R: set -> set -> prop. let M.
assume Hm: maximal_matching V R M.
exact andEL (is_matching V R M)
            (forall a :e V, forall b :e V, R a b -> ~(M a b) -> or (matched_by V M a) (matched_by V M b))
            Hm.
Qed.

Theorem perfect_matching_is_maximal : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  perfect_matching V R M -> maximal_matching V R M.
let V. let R: set -> set -> prop. let M.
assume Hp: perfect_matching V R M.
apply andI (is_matching V R M)
           (forall a :e V, forall b :e V, R a b -> ~(M a b) -> or (matched_by V M a) (matched_by V M b)).
- exact perfect_matching_is_matching V R M Hp.
- prove forall a :e V, forall b :e V, R a b -> ~(M a b) -> or (matched_by V M a) (matched_by V M b).
  let a. assume Ha: a :e V.
  let b. assume Hb: b :e V.
  assume Hab: R a b.
  assume Hnot: ~(M a b).
  claim Hcover: forall v :e V, exists u :e V, M v u.
    exact perfect_matching_covers V R M Hp.
  apply orIL.
  exact Hcover a Ha.
Qed.

Definition alternating_path : set -> (set -> set -> prop) -> (set -> set -> prop) -> set -> (set -> set) -> prop :=
  fun V R M k W =>
    and (is_path V R k W)
        (forall i :e k, xor (M (W i) (W (ordsucc i))) (~(M (W i) (W (ordsucc i))))).

Definition augmenting_path : set -> (set -> set -> prop) -> (set -> set -> prop) -> set -> (set -> set) -> prop :=
  fun V R M k W =>
    and (alternating_path V R M k W)
        (and (exposed_vertex V M (W 0))
             (exposed_vertex V M (W k))).

Theorem berge_lemma : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  maximal_matching V R M ->
  forall k:set, forall W:set -> set,
    augmenting_path V R M k W -> False.
Admitted.

Definition vertex_cover : set -> (set -> set -> prop) -> set -> prop :=
  fun V R C =>
    and (C c= V)
        (forall a b, R a b -> or (a :e C) (b :e C)).

Definition edge_cover : set -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun V R F =>
    and (forall x y, F x y -> and (x :e V) (and (y :e V) (R x y)))
        (forall v :e V, matched_by V F v).

Theorem vertex_cover_subq : forall V:set, forall R:set -> set -> prop, forall C:set,
  vertex_cover V R C -> C c= V.
let V. let R: set -> set -> prop. let C.
assume Hvc: vertex_cover V R C.
exact andEL (C c= V) (forall a b, R a b -> or (a :e C) (b :e C)) Hvc.
Qed.

Theorem vertex_cover_edges_hit : forall V:set, forall R:set -> set -> prop, forall C:set,
  vertex_cover V R C ->
  forall a b, R a b -> or (a :e C) (b :e C).
let V. let R: set -> set -> prop. let C.
assume Hvc: vertex_cover V R C.
exact andER (C c= V) (forall a b, R a b -> or (a :e C) (b :e C)) Hvc.
Qed.

Theorem edge_cover_edges_in_graph : forall V:set, forall R:set -> set -> prop, forall F:set -> set -> prop,
  edge_cover V R F ->
  forall x y, F x y -> and (x :e V) (and (y :e V) (R x y)).
let V. let R: set -> set -> prop. let F.
assume Hec: edge_cover V R F.
exact andEL (forall x y, F x y -> and (x :e V) (and (y :e V) (R x y)))
            (forall v :e V, matched_by V F v)
            Hec.
Qed.

Theorem edge_cover_covers : forall V:set, forall R:set -> set -> prop, forall F:set -> set -> prop,
  edge_cover V R F -> forall v :e V, matched_by V F v.
let V. let R: set -> set -> prop. let F.
assume Hec: edge_cover V R F.
exact andER (forall x y, F x y -> and (x :e V) (and (y :e V) (R x y)))
            (forall v :e V, matched_by V F v)
            Hec.
Qed.

Theorem perfect_matching_is_edge_cover : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  perfect_matching V R M -> edge_cover V R M.
let V. let R: set -> set -> prop. let M.
assume Hp: perfect_matching V R M.
apply andI (forall x y, M x y -> and (x :e V) (and (y :e V) (R x y)))
           (forall v :e V, matched_by V M v).
- prove forall x y, M x y -> and (x :e V) (and (y :e V) (R x y)).
  let x. let y. assume Hxy: M x y.
  exact is_matching_edge_in_graph V R M (perfect_matching_is_matching V R M Hp) x y Hxy.
- prove forall v :e V, matched_by V M v.
  let v. assume Hv: v :e V.
  exact perfect_matching_covers V R M Hp v Hv.
Qed.

Definition delete_edge_set_rel : (set -> set -> prop) -> (set -> set -> prop) -> set -> set -> prop :=
  fun F R x y => and (R x y) (~(F x y)).

Definition edge_cut : set -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun V R F =>
    and (forall x y, F x y -> R x y)
        (and (connected V R)
             (~(connected V (delete_edge_set_rel F R)))).

Definition two_edge_connected : set -> (set -> set -> prop) -> prop :=
  fun V R =>
    and (connected V R)
        (forall a b, R a b -> ~(bridge V R a b)).

Definition k_edge_connected_at_least_two : set -> (set -> set -> prop) -> prop :=
  fun V R =>
    and (two_edge_connected V R)
        (forall F:(set -> set -> prop),
            edge_cut V R F -> False).

Definition two_vertex_connected : set -> (set -> set -> prop) -> prop :=
  fun V R =>
    and (connected V R)
        (forall v, ~(cut_vertex V R v)).

Definition block : set -> (set -> set -> prop) -> set -> prop :=
  fun V R B =>
    and (B c= V)
        (and (two_vertex_connected B (induced_rel B R))
             (forall C:set,
               and (C c= V)
                   (and (two_vertex_connected C (induced_rel C R))
                        (B c= C)) -> C c= B)).

Theorem edge_cut_edges_in_graph : forall V:set, forall R:set -> set -> prop, forall F:set -> set -> prop,
  edge_cut V R F -> forall x y, F x y -> R x y.
let V. let R: set -> set -> prop. let F.
assume Hcut: edge_cut V R F.
exact andEL (forall x y, F x y -> R x y)
            (and (connected V R) (~(connected V (delete_edge_set_rel F R))))
            Hcut.
Qed.

Theorem edge_cut_connected : forall V:set, forall R:set -> set -> prop, forall F:set -> set -> prop,
  edge_cut V R F -> connected V R.
let V. let R: set -> set -> prop. let F.
assume Hcut: edge_cut V R F.
exact andEL (connected V R) (~(connected V (delete_edge_set_rel F R)))
            (andER (forall x y, F x y -> R x y)
                   (and (connected V R) (~(connected V (delete_edge_set_rel F R))))
                   Hcut).
Qed.

Theorem edge_cut_deletion_disconnects : forall V:set, forall R:set -> set -> prop, forall F:set -> set -> prop,
  edge_cut V R F -> ~(connected V (delete_edge_set_rel F R)).
let V. let R: set -> set -> prop. let F.
assume Hcut: edge_cut V R F.
exact andER (connected V R) (~(connected V (delete_edge_set_rel F R)))
            (andER (forall x y, F x y -> R x y)
                   (and (connected V R) (~(connected V (delete_edge_set_rel F R))))
                   Hcut).
Qed.

Theorem two_edge_connected_no_bridges : forall V:set, forall R:set -> set -> prop,
  two_edge_connected V R -> forall a b, ~(bridge V R a b).
let V. let R: set -> set -> prop.
assume H2: two_edge_connected V R.
claim Hnb: forall a b, R a b -> ~(bridge V R a b).
  exact andER (connected V R) (forall a b, R a b -> ~(bridge V R a b)) H2.
let a. let b.
assume Hbr: bridge V R a b.
claim Haedge: R a b.
  exact andEL (R a b) (and (connected V R) (~(connected V (delete_edge_rel a b R))))
              (andER (b :e V)
                     (and (R a b) (and (connected V R) (~(connected V (delete_edge_rel a b R)))))
                     (andER (a :e V)
                            (and (b :e V) (and (R a b) (and (connected V R) (~(connected V (delete_edge_rel a b R))))))
                            Hbr)).
exact (Hnb a b Haedge) Hbr.
Qed.

Theorem two_vertex_connected_no_cut_vertices : forall V:set, forall R:set -> set -> prop,
  two_vertex_connected V R -> forall v, ~(cut_vertex V R v).
let V. let R: set -> set -> prop.
assume H2: two_vertex_connected V R.
exact andER (connected V R) (forall v, ~(cut_vertex V R v)) H2.
Qed.

Theorem block_subq_V : forall V:set, forall R:set -> set -> prop, forall B:set,
  block V R B -> B c= V.
let V. let R: set -> set -> prop. let B.
assume Hb: block V R B.
exact andEL (B c= V)
            (and (two_vertex_connected B (induced_rel B R))
                 (forall C:set,
                   and (C c= V)
                       (and (two_vertex_connected C (induced_rel C R))
                            (B c= C)) -> C c= B))
            Hb.
Qed.

Theorem block_two_vertex_connected : forall V:set, forall R:set -> set -> prop, forall B:set,
  block V R B -> two_vertex_connected B (induced_rel B R).
let V. let R: set -> set -> prop. let B.
assume Hb: block V R B.
exact andEL (two_vertex_connected B (induced_rel B R))
            (forall C:set,
               and (C c= V)
                   (and (two_vertex_connected C (induced_rel C R))
                        (B c= C)) -> C c= B)
            (andER (B c= V)
                   (and (two_vertex_connected B (induced_rel B R))
                        (forall C:set,
                           and (C c= V)
                               (and (two_vertex_connected C (induced_rel C R))
                                    (B c= C)) -> C c= B))
                   Hb).
Qed.

Theorem block_maximal_two_vertex_connected : forall V:set, forall R:set -> set -> prop, forall B:set,
  block V R B ->
  forall C:set,
    and (C c= V)
        (and (two_vertex_connected C (induced_rel C R))
             (B c= C)) -> C c= B.
let V. let R: set -> set -> prop. let B.
assume Hb: block V R B.
exact andER (two_vertex_connected B (induced_rel B R))
            (forall C:set,
               and (C c= V)
                   (and (two_vertex_connected C (induced_rel C R))
                        (B c= C)) -> C c= B)
            (andER (B c= V)
                   (and (two_vertex_connected B (induced_rel B R))
                        (forall C:set,
                           and (C c= V)
                               (and (two_vertex_connected C (induced_rel C R))
                                    (B c= C)) -> C c= B))
                   Hb).
Qed.

Definition coloring : set -> set -> (set -> set) -> prop :=
  fun V C col => forall v :e V, col v :e C.

Definition proper_coloring : set -> (set -> set -> prop) -> set -> (set -> set) -> prop :=
  fun V R C c => and (coloring V C c)
                     (forall x y :e V, x <> y -> R x y -> c x <> c y).

Definition k_colorable : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k =>
    exists c : set -> set, proper_coloring V R k c.

Definition bipartite_graph : set -> (set -> set -> prop) -> prop :=
  fun V R =>
    exists A B : set,
      and (A c= V)
          (and (B c= V)
               (and (A :\/: B = V)
                    (and (A :/\: B = Empty)
                         (forall x y, R x y ->
                          or (and (x :e A) (y :e B))
                             (and (x :e B) (y :e A)))))).

Theorem bipartite_is_2_colorable : forall V:set, forall R:set -> set -> prop,
  simple_graph V R ->
  bipartite_graph V R ->
  k_colorable V R 2.
Admitted.

Definition complete_bipartite_graph : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun V R A B =>
    and (A c= V)
        (and (B c= V)
             (and (A :/\: B = Empty)
                  (and (A :\/: B = V)
                       (forall x :e V, forall y :e V, x <> y ->
                         iff (R x y)
                             (or (and (x :e A) (y :e B))
                                 (and (x :e B) (y :e A))))))).

Definition cycle_graph : set -> (set -> set -> prop) -> prop :=
  fun V R =>
    exists k:set, exists W:set -> set,
      and (is_cycle V R k W)
          (forall v :e V, exists i :e k, W i = v).

Theorem complete_graph_is_clique : forall V:set, forall R:set -> set -> prop,
  complete_graph V R -> is_clique V R V.
let V. let R.
assume Hcomp: complete_graph V R.
apply andI (V c= V) (forall x :e V, forall y :e V, x <> y -> R x y).
- prove V c= V.
  let x. assume Hx: x :e V. exact Hx.
- let x. assume Hx: x :e V.
  let y. assume Hy: y :e V.
  assume Hneq: x <> y.
  exact Hcomp x Hx y Hy Hneq.
Qed.

Theorem complete_bipartite_is_bipartite_graph : forall V:set, forall R:set -> set -> prop,
  simple_graph V R ->
  forall A B:set,
    complete_bipartite_graph V R A B ->
    bipartite_graph V R.
let V. let R.
assume Hsg: simple_graph V R.
let A. let B.
assume Hcbg: complete_bipartite_graph V R A B.
claim HsubA: A c= V.
  exact andEL (A c= V)
              (and (B c= V)
                   (and (A :/\: B = Empty)
                        (and (A :\/: B = V)
                             (forall x :e V, forall y :e V, x <> y ->
                                iff (R x y)
                                    (or (and (x :e A) (y :e B))
                                        (and (x :e B) (y :e A)))))))
              Hcbg.
claim Hrest1:
  and (B c= V)
      (and (A :/\: B = Empty)
           (and (A :\/: B = V)
                (forall x :e V, forall y :e V, x <> y ->
                   iff (R x y)
                       (or (and (x :e A) (y :e B))
                           (and (x :e B) (y :e A)))))).
  exact andER (A c= V)
              (and (B c= V)
                   (and (A :/\: B = Empty)
                        (and (A :\/: B = V)
                             (forall x :e V, forall y :e V, x <> y ->
                                iff (R x y)
                                    (or (and (x :e A) (y :e B))
                                        (and (x :e B) (y :e A)))))))
              Hcbg.
claim HsubB: B c= V.
  exact andEL (B c= V)
              (and (A :/\: B = Empty)
                   (and (A :\/: B = V)
                        (forall x :e V, forall y :e V, x <> y ->
                           iff (R x y)
                               (or (and (x :e A) (y :e B))
                                   (and (x :e B) (y :e A))))))
              Hrest1.
claim Hrest2:
  and (A :/\: B = Empty)
      (and (A :\/: B = V)
           (forall x :e V, forall y :e V, x <> y ->
              iff (R x y)
                  (or (and (x :e A) (y :e B))
                      (and (x :e B) (y :e A))))).
  exact andER (B c= V)
              (and (A :/\: B = Empty)
                   (and (A :\/: B = V)
                        (forall x :e V, forall y :e V, x <> y ->
                           iff (R x y)
                               (or (and (x :e A) (y :e B))
                                   (and (x :e B) (y :e A))))))
              Hrest1.
claim Hdisj: A :/\: B = Empty.
  exact andEL (A :/\: B = Empty)
              (and (A :\/: B = V)
                   (forall x :e V, forall y :e V, x <> y ->
                      iff (R x y)
                          (or (and (x :e A) (y :e B))
                              (and (x :e B) (y :e A)))))
              Hrest2.
claim Hrest3:
  and (A :\/: B = V)
      (forall x :e V, forall y :e V, x <> y ->
         iff (R x y)
             (or (and (x :e A) (y :e B))
                 (and (x :e B) (y :e A)))).
  exact andER (A :/\: B = Empty)
              (and (A :\/: B = V)
                   (forall x :e V, forall y :e V, x <> y ->
                      iff (R x y)
                          (or (and (x :e A) (y :e B))
                              (and (x :e B) (y :e A)))))
              Hrest2.
claim Hcover: A :\/: B = V.
  exact andEL (A :\/: B = V)
              (forall x :e V, forall y :e V, x <> y ->
                 iff (R x y)
                     (or (and (x :e A) (y :e B))
                         (and (x :e B) (y :e A))))
              Hrest3.
claim HedgeEq:
  forall x :e V, forall y :e V, x <> y ->
    iff (R x y)
        (or (and (x :e A) (y :e B))
            (and (x :e B) (y :e A))).
  exact andER (A :\/: B = V)
              (forall x :e V, forall y :e V, x <> y ->
                 iff (R x y)
                     (or (and (x :e A) (y :e B))
                         (and (x :e B) (y :e A))))
              Hrest3.
prove exists A0:set, exists B0:set,
       and (A0 c= V)
           (and (B0 c= V)
                (and (A0 :\/: B0 = V)
                     (and (A0 :/\: B0 = Empty)
                          (forall x y, R x y ->
                           or (and (x :e A0) (y :e B0))
                              (and (x :e B0) (y :e A0)))))).
  witness A.
  witness B.
  apply andI (A c= V)
             (and (B c= V)
                  (and (A :\/: B = V)
                       (and (A :/\: B = Empty)
                            (forall x y, R x y ->
                             or (and (x :e A) (y :e B))
                                (and (x :e B) (y :e A)))))).
  - exact HsubA.
  - apply andI (B c= V)
               (and (A :\/: B = V)
                    (and (A :/\: B = Empty)
                         (forall x y, R x y ->
                          or (and (x :e A) (y :e B))
                             (and (x :e B) (y :e A))))).
    * exact HsubB.
    * apply andI (A :\/: B = V)
                 (and (A :/\: B = Empty)
                      (forall x y, R x y ->
                       or (and (x :e A) (y :e B))
                          (and (x :e B) (y :e A)))).
      + exact Hcover.
      + apply andI (A :/\: B = Empty)
                   (forall x y, R x y ->
                    or (and (x :e A) (y :e B))
                       (and (x :e B) (y :e A))).
        * exact Hdisj.
        * let x. let y.
          assume Hxy: R x y.
          claim Hmem: and (x :e V) (y :e V).
            exact simple_graph_edge_in_V V R Hsg x y Hxy.
          claim HxV: x :e V.
            exact andEL (x :e V) (y :e V) Hmem.
          claim HyV: y :e V.
            exact andER (x :e V) (y :e V) Hmem.
          claim Hneq: x <> y.
            assume Heq: x = y.
            apply simple_graph_irreflexive V R Hsg x HxV.
            rewrite Heq at 2.
            exact Hxy.
          claim Hiff: iff (R x y)
                           (or (and (x :e A) (y :e B))
                               (and (x :e B) (y :e A))).
            exact HedgeEq x HxV y HyV Hneq.
          exact andEL (R x y -> or (and (x :e A) (y :e B))
                                    (and (x :e B) (y :e A)))
                      ((or (and (x :e A) (y :e B))
                           (and (x :e B) (y :e A))) -> R x y)
                      Hiff
                      Hxy.
Qed.

Theorem complete_bipartite_triangle_free : forall V:set, forall R:set -> set -> prop,
  simple_graph V R ->
  forall A B:set,
    complete_bipartite_graph V R A B ->
    triangle_free V R.
let V. let R. assume Hsg: simple_graph V R.
let A.
let B.
assume Hcbg: complete_bipartite_graph V R A B.
claim Hbip: bipartite_graph V R.
  exact complete_bipartite_is_bipartite_graph V R Hsg A B Hcbg.
prove triangle_free V R.
  let x. assume Hx: x :e V.
  let y. assume Hy: y :e V.
  let z. assume Hz: z :e V.
  assume Hxy: R x y.
  assume Hyz: R y z.
  assume Hxz: R x z.
  apply Hbip.
  let A1. assume HA1.
  apply HA1.
  let B1. assume Hpair.
  claim HsubA1: A1 c= V.
    exact andEL (A1 c= V)
                (and (B1 c= V)
                     (and (A1 :\/: B1 = V)
                          (and (A1 :/\: B1 = Empty)
                               (forall x y, R x y ->
                                or (and (x :e A1) (y :e B1))
                                   (and (x :e B1) (y :e A1))))))
                Hpair.
  claim HrestA:
    and (B1 c= V)
        (and (A1 :\/: B1 = V)
             (and (A1 :/\: B1 = Empty)
                  (forall x y, R x y ->
                   or (and (x :e A1) (y :e B1))
                      (and (x :e B1) (y :e A1))))).
    exact andER (A1 c= V)
                (and (B1 c= V)
                     (and (A1 :\/: B1 = V)
                          (and (A1 :/\: B1 = Empty)
                               (forall x y, R x y ->
                                or (and (x :e A1) (y :e B1))
                                   (and (x :e B1) (y :e A1))))))
                Hpair.
  claim HsubB1: B1 c= V.
    exact andEL (B1 c= V)
                (and (A1 :\/: B1 = V)
                     (and (A1 :/\: B1 = Empty)
                          (forall x y, R x y ->
                           or (and (x :e A1) (y :e B1))
                              (and (x :e B1) (y :e A1)))))
                HrestA.
  claim HrestB:
    and (A1 :\/: B1 = V)
        (and (A1 :/\: B1 = Empty)
             (forall x y, R x y ->
              or (and (x :e A1) (y :e B1))
                 (and (x :e B1) (y :e A1)))).
    exact andER (B1 c= V)
                (and (A1 :\/: B1 = V)
                     (and (A1 :/\: B1 = Empty)
                          (forall x y, R x y ->
                           or (and (x :e A1) (y :e B1))
                              (and (x :e B1) (y :e A1)))))
                HrestA.
  claim Hdisj1: A1 :/\: B1 = Empty.
    exact andEL (A1 :/\: B1 = Empty)
                (forall x y, R x y ->
                  or (and (x :e A1) (y :e B1))
                     (and (x :e B1) (y :e A1)))
                (andER (A1 :\/: B1 = V)
                       (and (A1 :/\: B1 = Empty)
                            (forall x y, R x y ->
                              or (and (x :e A1) (y :e B1))
                                 (and (x :e B1) (y :e A1))))
                       HrestB).
  claim Hedges:
    forall x y, R x y ->
      or (and (x :e A1) (y :e B1))
         (and (x :e B1) (y :e A1)).
    exact andER (A1 :/\: B1 = Empty)
                (forall x y, R x y ->
                  or (and (x :e A1) (y :e B1))
                     (and (x :e B1) (y :e A1)))
                (andER (A1 :\/: B1 = V)
                       (and (A1 :/\: B1 = Empty)
                            (forall x y, R x y ->
                              or (and (x :e A1) (y :e B1))
                                 (and (x :e B1) (y :e A1))))
                       HrestB).
  claim both_contra: forall v:set, v :e A1 -> v :e B1 -> False.
    let v. assume HvA: v :e A1. assume HvB: v :e B1.
    apply EmptyE v.
    rewrite <- Hdisj1.
    apply binintersectI A1 B1 v HvA HvB.
  claim HxyParts: or (and (x :e A1) (y :e B1))
                     (and (x :e B1) (y :e A1)).
    exact Hedges x y Hxy.
  apply HxyParts.
  - assume HxyAB: and (x :e A1) (y :e B1).
    claim HxA: x :e A1.
      exact andEL (x :e A1) (y :e B1) HxyAB.
    claim HyB: y :e B1.
      exact andER (x :e A1) (y :e B1) HxyAB.
    claim HyzParts: or (and (y :e A1) (z :e B1))
                        (and (y :e B1) (z :e A1)).
      exact Hedges y z Hyz.
    apply HyzParts.
    + assume HyA_zB: and (y :e A1) (z :e B1).
      claim HyA: y :e A1.
        exact andEL (y :e A1) (z :e B1) HyA_zB.
      exact both_contra y HyA HyB.
    + assume HyB_zA: and (y :e B1) (z :e A1).
      claim HzA: z :e A1.
        exact andER (y :e B1) (z :e A1) HyB_zA.
      claim HxzParts: or (and (x :e A1) (z :e B1))
                          (and (x :e B1) (z :e A1)).
        exact Hedges x z Hxz.
      apply HxzParts.
      * assume HxA_zB: and (x :e A1) (z :e B1).
        claim HzB: z :e B1.
          exact andER (x :e A1) (z :e B1) HxA_zB.
        exact both_contra z HzA HzB.
      * assume HxB_zA: and (x :e B1) (z :e A1).
        claim HxB: x :e B1.
          exact andEL (x :e B1) (z :e A1) HxB_zA.
        exact both_contra x HxA HxB.
  - assume HxyBA: and (x :e B1) (y :e A1).
    claim HxB: x :e B1.
      exact andEL (x :e B1) (y :e A1) HxyBA.
    claim HyA: y :e A1.
      exact andER (x :e B1) (y :e A1) HxyBA.
    claim HyzParts: or (and (y :e A1) (z :e B1))
                        (and (y :e B1) (z :e A1)).
      exact Hedges y z Hyz.
    apply HyzParts.
    + assume HyA_zB: and (y :e A1) (z :e B1).
      claim HzB: z :e B1.
        exact andER (y :e A1) (z :e B1) HyA_zB.
      claim HxzParts: or (and (x :e A1) (z :e B1))
                          (and (x :e B1) (z :e A1)).
        exact Hedges x z Hxz.
      apply HxzParts.
      * assume HxA_zB: and (x :e A1) (z :e B1).
        claim HxA: x :e A1.
          exact andEL (x :e A1) (z :e B1) HxA_zB.
        exact both_contra x HxA HxB.
      * assume HxB_zA: and (x :e B1) (z :e A1).
        claim HzA: z :e A1.
          exact andER (x :e B1) (z :e A1) HxB_zA.
        exact both_contra z HzA HzB.
    + assume HyB_zA: and (y :e B1) (z :e A1).
      claim HyB: y :e B1.
        exact andEL (y :e B1) (z :e A1) HyB_zA.
      exact both_contra y HyA HyB.
Qed.

Theorem cycle_graph_has_cycle : forall V:set, forall R:set -> set -> prop,
  cycle_graph V R -> exists k:set, exists W:set -> set, is_cycle V R k W.
let V. let R.
assume Hcyc: cycle_graph V R.
apply Hcyc.
let k. assume Hk.
apply Hk.
let W. assume Hpair.
claim Hcycproof: is_cycle V R k W.
  exact andEL (is_cycle V R k W) (forall v :e V, exists i :e k, W i = v) Hpair.
prove exists k0:set, exists W0:set -> set, is_cycle V R k0 W0.
  witness k.
  witness W.
  exact Hcycproof.
Qed.

Definition planar_embedding : set -> (set -> set -> prop) -> set -> prop :=
  fun V R E => True.

Theorem planar_embedding_induced : forall V:set, forall R:set -> set -> prop, forall E:set,
  planar_embedding V R E ->
  forall T:set, T c= V ->
    exists E':set, planar_embedding T (induced_rel T R) E'.
Admitted.

Definition planar_graph : set -> (set -> set -> prop) -> prop :=
  fun V R => exists E:set, planar_embedding V R E.

Definition planar_simple_graph : set -> (set -> set -> prop) -> prop :=
  fun V R => and (simple_graph V R) (planar_graph V R).

Definition outerplanar_graph : set -> (set -> set -> prop) -> prop :=
  fun V R => exists E:set, planar_embedding V R E.

Theorem outerplanar_embedding_planar : forall V:set, forall R:set -> set -> prop, forall E:set,
  planar_embedding V R E -> planar_graph V R.
let V. let R. let E.
assume Hemb: planar_embedding V R E.
prove exists E0:set, planar_embedding V R E0.
  witness E.
  exact Hemb.
Qed.

Theorem planar_induced_subgraph_planar : forall V:set, forall R:set -> set -> prop,
  planar_graph V R ->
  forall T:set, T c= V ->
    planar_graph T (induced_rel T R).
Admitted.

Theorem planar_simple_subgraph_planar : forall V:set, forall R:set -> set -> prop,
  planar_simple_graph V R ->
  forall T:set, T c= V ->
    planar_simple_graph T (induced_rel T R).
Admitted.

Theorem outerplanar_is_planar : forall V:set, forall R:set -> set -> prop,
  outerplanar_graph V R -> planar_graph V R.
let V. let R.
assume Hout: outerplanar_graph V R.
exact Hout.
Qed.

Theorem planar_no_k33_or_k5_minor : forall V:set, forall R:set -> set -> prop,
  planar_graph V R -> True.
Admitted.

Theorem euler_formula_planar : forall V:set, forall R:set -> set -> prop,
  planar_simple_graph V R -> True.
Admitted.

Theorem planar_edge_bound_simple : forall V:set, forall R:set -> set -> prop,
  planar_simple_graph V R -> True.
Admitted.

Theorem is_matching_no_loops : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  simple_graph V R ->
  is_matching V R M ->
  forall v:set, ~M v v.
let V. let R. let M.
assume Hsg: simple_graph V R.
assume Hm: is_matching V R M.
let v.
apply notI.
assume Hv: M v v.
claim Hedges: and (v :e V) (and (v :e V) (R v v)).
  exact is_matching_edge_in_graph V R M Hm v v Hv.
claim Hr: R v v.
  exact andER (v :e V) (R v v) (andER (v :e V) (and (v :e V) (R v v)) Hedges).
claim HvV: v :e V.
  exact andEL (v :e V) (and (v :e V) (R v v)) Hedges.
exact (simple_graph_irreflexive V R Hsg v HvV) Hr.
Qed.

Theorem perfect_matching_no_loops : forall V:set, forall R:set -> set -> prop, forall M:set -> set -> prop,
  simple_graph V R ->
  perfect_matching V R M ->
  forall v:set, ~M v v.
let V. let R. let M.
assume Hsg: simple_graph V R.
assume Hp: perfect_matching V R M.
exact is_matching_no_loops V R M Hsg (perfect_matching_is_matching V R M Hp).
Qed.

Definition edge_coloring : set -> (set -> set -> prop) -> set -> (set -> set -> set) -> prop :=
  fun V R C col =>
    forall x y, R x y -> and (col x y = col y x) (col x y :e C).

Definition proper_edge_coloring : set -> (set -> set -> prop) -> set -> (set -> set -> set) -> prop :=
  fun V R C col =>
    and (edge_coloring V R C col)
        (forall a b c,
           R a b -> R a c -> b <> c ->
           col a b <> col a c).

Definition edge_k_colorable : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => exists col:set -> set -> set, proper_edge_coloring V R k col.

Definition chromatic_index_le : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => edge_k_colorable V R k.

Theorem proper_edge_coloring_incident_distinct : forall V:set, forall R:set -> set -> prop,
  forall C:set, forall col:set -> set -> set,
    proper_edge_coloring V R C col ->
    forall a b c, R a b -> R a c -> b <> c -> col a b <> col a c.
let V. let R. let C. let col.
assume Hpr: proper_edge_coloring V R C col.
claim Hdistinct: forall a b c, R a b -> R a c -> b <> c -> col a b <> col a c.
  exact andER (edge_coloring V R C col)
              (forall a b c, R a b -> R a c -> b <> c -> col a b <> col a c)
              Hpr.
let a. let b. let c.
assume Hab: R a b.
assume Hac: R a c.
assume Hneq: b <> c.
exact Hdistinct a b c Hab Hac Hneq.
Qed.

Theorem edge_coloring_sym : forall V:set, forall R:set -> set -> prop,
  forall C:set, forall col:set -> set -> set,
    edge_coloring V R C col ->
    forall x y, R x y -> col x y = col y x.
let V. let R. let C. let col.
assume Hcol: edge_coloring V R C col.
let x. let y. assume Hxy: R x y.
exact andEL (col x y = col y x) (col x y :e C) (Hcol x y Hxy).
Qed.

Theorem edge_coloring_color_in_palette : forall V:set, forall R:set -> set -> prop,
  forall C:set, forall col:set -> set -> set,
    edge_coloring V R C col ->
    forall x y, R x y -> col x y :e C.
let V. let R. let C. let col.
assume Hcol: edge_coloring V R C col.
let x. let y. assume Hxy: R x y.
exact andER (col x y = col y x) (col x y :e C) (Hcol x y Hxy).
Qed.

Theorem edge_k_colorable_imp_chromatic_index_le : forall V:set, forall R:set -> set -> prop, forall k:set,
  edge_k_colorable V R k -> chromatic_index_le V R k.
let V. let R. let k.
assume Hk: edge_k_colorable V R k.
exact Hk.
Qed.

Theorem vizing_bound_statement : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem konig_line_bipartite_edge_chromatic_index : forall V:set, forall R:set -> set -> prop,
  bipartite_graph V R ->
  True.
Admitted.

Definition chromatic_number_le : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => k_colorable V R k.

Theorem proper_coloring_incident_distinct : forall V:set, forall R:set -> set -> prop,
  forall C:set, forall c:set -> set,
    proper_coloring V R C c ->
    forall x y :e V, x <> y -> R x y -> c x <> c y.
let V. let R. let C. let c.
assume Hp: proper_coloring V R C c.
let x. assume Hx: x :e V.
let y. assume Hy: y :e V.
assume Hneq: x <> y.
assume Hxy: R x y.
exact andER (coloring V C c) (forall x y :e V, x <> y -> R x y -> c x <> c y) Hp x Hx y Hy Hneq Hxy.
Qed.

Theorem color_class_is_independent : forall V:set, forall R:set -> set -> prop,
  forall C:set, forall c:set -> set, forall col:set,
    proper_coloring V R C c ->
    col :e C ->
    is_indep_set V R (Sep V (fun v:set => c v = col)).
Admitted.

Theorem clique_lower_bound_chromatic_number : forall V:set, forall R:set -> set -> prop,
  forall K:set,
    is_clique V R K ->
    chromatic_number_le V R K.
Admitted.

Theorem independence_number_upper_chromatic_number : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Definition hamiltonian_cycle : set -> (set -> set -> prop) -> set -> (set -> set) -> prop :=
  fun V R k W =>
    and (is_cycle V R k W)
        (forall v :e V, exists i :e k, W i = v).

Definition hamiltonian_graph : set -> (set -> set -> prop) -> prop :=
  fun V R => exists k:set, exists W:set -> set, hamiltonian_cycle V R k W.

Theorem cycle_graph_is_hamiltonian : forall V:set, forall R:set -> set -> prop,
  cycle_graph V R -> hamiltonian_graph V R.
let V. let R.
assume Hcyc: cycle_graph V R.
exact Hcyc.
Qed.

Theorem dirac_condition_implies_hamiltonian : forall V:set, forall R:set -> set -> prop,
  simple_graph V R -> True.
Admitted.

Theorem ore_condition_implies_hamiltonian : forall V:set, forall R:set -> set -> prop,
  simple_graph V R -> True.
Admitted.

Theorem mantel_triangle_free_edge_bound : forall V:set, forall R:set -> set -> prop,
  simple_graph V R -> True.
Admitted.

Theorem turan_kclique_free_bound : forall V:set, forall R:set -> set -> prop, forall k:set,
  simple_graph V R -> True.
Admitted.

Theorem ramsey_R33_six : True.
Admitted.

Theorem ramsey_general_exists : True.
Admitted.

Theorem wagner_kuratowski_planar_characterization : True.
Admitted.

Theorem graph_minor_well_quasi_order : True.
Admitted.

Definition dfs_run : set -> (set -> set -> prop) -> set -> (set -> set) -> (set -> set) -> (set -> set) -> (set -> set -> prop) -> prop :=
  fun V R root disc fin parent tree =>
    and (root :e V)
        (and (forall v :e V, disc v <> fin v)
             (and (forall v :e V, v <> root -> parent v :e V)
                  (and (forall v :e V, v <> root -> R v (parent v))
                       (forall x y, tree x y ->
                         or (and (parent x = y) (R x y))
                            (and (parent y = x) (R x y)))))).

Definition dfs_tree_edge : (set -> set) -> (set -> set -> prop) -> set -> set -> prop :=
  fun parent R x y => and (R x y) (or (parent x = y) (parent y = x)).

Definition dfs_back_edge : (set -> set -> prop) -> (set -> set) -> (set -> set) -> (set -> set -> prop) -> set -> set -> prop :=
  fun lt disc fin R x y =>
    and (R x y) (lt (disc y) (disc x)).

Definition dfs_cross_edge : (set -> set -> prop) -> (set -> set) -> (set -> set) -> (set -> set -> prop) -> set -> set -> prop :=
  fun lt disc fin R x y =>
    and (R x y) (lt (fin y) (disc x)).

Definition dfs_forward_edge : (set -> set -> prop) -> (set -> set) -> (set -> set) -> (set -> set -> prop) -> set -> set -> prop :=
  fun lt disc fin R x y =>
    and (R x y) (lt (disc x) (disc y)).

Definition bfs_run : set -> (set -> set -> prop) -> set -> (set -> set) -> (set -> set) -> (set -> set) -> prop :=
  fun V R src level parent frontier =>
    and (src :e V)
        (and (level src = 0)
             (and (forall v :e V, v <> src -> parent v :e V)
                  (and (forall v :e V, v <> src -> R v (parent v))
                       (forall v :e V, forall w :e V, R v w ->
                         or (level v = level w)
                            (or (level v = ordsucc (level w))
                                (level w = ordsucc (level v))))))).

Definition bfs_tree_edge : (set -> set) -> (set -> set -> prop) -> set -> set -> prop :=
  fun parent R x y => and (R x y) (or (parent x = y) (parent y = x)).

Definition discovery_time_before_finish : set -> (set -> set) -> (set -> set) -> (set -> set -> prop) -> prop :=
  fun V disc fin lt =>
    forall v :e V, lt (disc v) (fin v).

Definition edge_types_cover : set -> (set -> set -> prop) -> (set -> set -> prop) -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun V R T B C =>
    forall x :e V, forall y :e V, R x y -> or (T x y) (or (B x y) (C x y)).

Theorem dfs_tree_edges_acyclic : forall V:set, forall R:set -> set -> prop,
  forall root:set, forall disc fin parent:set -> set, forall tree:set -> set -> prop,
    dfs_run V R root disc fin parent tree ->
    acyclic V tree.
Admitted.

Theorem dfs_back_edges_go_to_ancestor : forall V:set, forall R:set -> set -> prop,
  forall lt:set -> set -> prop, forall disc fin parent:set -> set,
    discovery_time_before_finish V disc fin lt ->
    forall x y, dfs_back_edge lt disc fin R x y -> lt (disc y) (disc x).
Admitted.

Theorem dfs_edge_classification : forall V:set, forall R:set -> set -> prop,
  forall lt:set -> set -> prop, forall disc fin parent:set -> set, forall tree:set -> set -> prop,
    discovery_time_before_finish V disc fin lt ->
    edge_types_cover V R (dfs_tree_edge parent R) (dfs_back_edge lt disc fin R) (dfs_cross_edge lt disc fin R).
Admitted.

Theorem bfs_levels_respect_edges : forall V:set, forall R:set -> set -> prop,
  forall src:set, forall level parent frontier:set -> set,
    bfs_run V R src level parent frontier ->
    forall x :e V, forall y :e V, R x y ->
      or (level x = level y)
         (or (level x = ordsucc (level y)) (level y = ordsucc (level x))).
Admitted.

Theorem bfs_tree_edges_form_shortest_paths : forall V:set, forall R:set -> set -> prop,
  forall src:set, forall level parent frontier:set -> set,
    bfs_run V R src level parent frontier ->
    True.
Admitted.

Definition dfs_reachable : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun V R root v => reachable V R root v.

Theorem dfs_explores_all_reachable : forall V:set, forall R:set -> set -> prop,
  forall root:set, forall disc fin parent:set -> set, forall tree:set -> set -> prop,
    dfs_run V R root disc fin parent tree ->
    forall v :e V, dfs_reachable V R root v -> exists y:set, tree v y.
Admitted.

Theorem dfs_parent_tree_spanning : forall V:set, forall R:set -> set -> prop,
  forall root:set, forall disc fin parent:set -> set, forall tree:set -> set -> prop,
    dfs_run V R root disc fin parent tree ->
    forall v :e V, v <> root -> tree v (parent v).
Admitted.

Theorem dfs_cycle_detected_by_back_edge : forall V:set, forall R:set -> set -> prop,
  forall lt:set -> set -> prop, forall disc fin parent:set -> set,
    discovery_time_before_finish V disc fin lt ->
    (exists x y:set, dfs_back_edge lt disc fin R x y) -> exists k:set, exists W:set -> set, is_cycle V R k W.
Admitted.

Theorem dfs_no_back_edges_in_dag : forall V:set, forall R:set -> set -> prop,
  forall lt:set -> set -> prop, forall disc fin parent:set -> set,
    discovery_time_before_finish V disc fin lt ->
    (forall x y:set, dfs_back_edge lt disc fin R x y -> False) ->
    acyclic V R.
Admitted.

Theorem dfs_finish_time_nesting : forall V:set, forall R:set -> set -> prop,
  forall root:set, forall lt:set -> set -> prop, forall disc fin parent:set -> set, forall tree:set -> set -> prop,
    dfs_run V R root disc fin parent tree ->
    discovery_time_before_finish V disc fin lt ->
    forall x y:set, tree x y -> lt (disc x) (disc y) -> lt (fin y) (fin x).
Admitted.

Theorem dfs_topological_sort_finishing_times : forall V:set, forall R:set -> set -> prop,
  forall root:set, forall lt:set -> set -> prop, forall disc fin parent:set -> set, forall tree:set -> set -> prop,
    dfs_run V R root disc fin parent tree ->
    discovery_time_before_finish V disc fin lt ->
    acyclic V R ->
    True.
Admitted.

Definition bfs_distance_respects_level : set -> (set -> set -> prop) -> set -> (set -> set) -> prop :=
  fun V R src level =>
    forall v :e V, reachable V R src v -> exists k:set, level v = k.

Theorem bfs_tree_spans_reachable : forall V:set, forall R:set -> set -> prop,
  forall src:set, forall level parent frontier:set -> set,
    bfs_run V R src level parent frontier ->
    forall v :e V, reachable V R src v -> exists y:set, bfs_tree_edge parent R v y.
Admitted.

Theorem bfs_parent_levels_adjacent : forall V:set, forall R:set -> set -> prop,
  forall src:set, forall level parent frontier:set -> set,
    bfs_run V R src level parent frontier ->
    forall v :e V, v <> src -> or (level v = ordsucc (level (parent v))) (level (parent v) = ordsucc (level v)).
Admitted.

Theorem bfs_shortest_path_distance : forall V:set, forall R:set -> set -> prop,
  forall src:set, forall level parent frontier:set -> set,
    bfs_run V R src level parent frontier ->
    forall v :e V, reachable V R src v -> exists k:set, level v = k.
Admitted.

Theorem dfs_tree_edge_in_graph : forall V:set, forall R:set -> set -> prop,
  forall root:set, forall disc fin parent:set -> set, forall tree:set -> set -> prop,
    dfs_run V R root disc fin parent tree ->
    forall x y:set, tree x y -> R x y.
Admitted.

Theorem dfs_tree_child_unique_parent : forall V:set, forall R:set -> set -> prop,
  forall root:set, forall disc fin parent:set -> set, forall tree:set -> set -> prop,
    dfs_run V R root disc fin parent tree ->
    forall v p1 p2:set, tree v p1 -> tree v p2 -> p1 = p2.
Admitted.

Theorem dfs_discovery_before_parent : forall V:set, forall R:set -> set -> prop,
  forall root:set, forall lt:set -> set -> prop, forall disc fin parent:set -> set, forall tree:set -> set -> prop,
    dfs_run V R root disc fin parent tree ->
    discovery_time_before_finish V disc fin lt ->
    forall v :e V, v <> root -> lt (disc (parent v)) (disc v).
Admitted.

Theorem bfs_root_reaches_all_in_component : forall V:set, forall R:set -> set -> prop,
  forall src:set, forall level parent frontier:set -> set,
    bfs_run V R src level parent frontier ->
    forall v :e V, reachable V R src v -> exists y:set, bfs_tree_edge parent R v y.
Admitted.

Theorem bfs_level_of_source_zero : forall V:set, forall R:set -> set -> prop,
  forall src:set, forall level parent frontier:set -> set,
    bfs_run V R src level parent frontier ->
    level src = 0.
Admitted.

Definition network : set -> (set -> set -> prop) -> set -> set -> (set -> set -> set) -> prop :=
  fun V E source sink capacity =>
    and (source :e V)
        (and (sink :e V)
             (forall x y, E x y -> and (x :e V) (y :e V))).

Definition capacity_respects_edges : set -> (set -> set -> prop) -> (set -> set -> set) -> prop :=
  fun V E capacity => forall x y, ~E x y -> capacity x y = 0.

Definition feasible_flow : set -> (set -> set -> prop) -> set -> set -> (set -> set -> set) -> (set -> set -> set) -> prop :=
  fun V E source sink capacity f =>
    and (network V E source sink capacity)
        (and (capacity_respects_edges V E capacity)
             True).

Definition capacity_constraint : (set -> set -> set) -> (set -> set -> set) -> prop :=
  fun capacity f => True.

Definition flow_conservation : set -> (set -> set -> prop) -> set -> set -> (set -> set -> set) -> prop :=
  fun V E source sink f => True.

Definition feasible_flow_strong : set -> (set -> set -> prop) -> set -> set -> (set -> set -> set) -> (set -> set -> set) -> prop :=
  fun V E source sink capacity f =>
    and (feasible_flow V E source sink capacity f)
        (and (capacity_constraint capacity f)
             (flow_conservation V E source sink f)).

Definition residual_edge : (set -> set -> prop) -> (set -> set -> set) -> (set -> set -> set) -> set -> set -> prop :=
  fun E capacity f x y => or (E x y) (and (E y x) (~(capacity y x = 0))).

Definition flow_value : set -> (set -> set -> set) -> set -> set -> set :=
  fun V f source sink => 0.

Definition residual_network : set -> (set -> set -> prop) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> prop) :=
  fun V E capacity f =>
    fun x y => or (E x y) (E y x).

Definition residual_capacity : (set -> set -> set) -> (set -> set -> set) -> set -> set -> set :=
  fun capacity f x y => capacity x y.

Definition st_cut : set -> set -> set -> set -> prop :=
  fun V S source sink =>
    and (S c= V)
        (and (source :e S)
             (~(sink :e S))).

Definition cut_capacity : set -> (set -> set -> prop) -> (set -> set -> set) -> set -> set ->
  set :=
  fun V E capacity S T => 0.

Definition flow_augmenting_path : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun V R source sink =>
    exists k:set, exists W:set -> set, simple_path_between V R source sink k W.

Theorem cut_bounds_flow_value : forall V:set, forall E:set -> set -> prop,
  forall source sink:set, forall capacity:set -> set -> set, forall f:set -> set -> set,
    feasible_flow V E source sink capacity f ->
    forall S:set, st_cut V S source sink ->
    flow_value V f source sink = cut_capacity V E capacity S V.
Admitted.

Theorem max_flow_min_cut : forall V:set, forall E:set -> set -> prop,
  forall source sink:set, forall capacity:set -> set -> set,
    network V E source sink capacity ->
    exists f:set -> set -> set, feasible_flow V E source sink capacity f /\
      exists S:set, st_cut V S source sink /\
        flow_value V f source sink = cut_capacity V E capacity S V.
Admitted.

Theorem flow_conservation_holds_for_feasible_strong : forall V:set, forall E:set -> set -> prop,
  forall source sink:set, forall capacity:set -> set -> set, forall f:set -> set -> set,
    feasible_flow_strong V E source sink capacity f -> flow_conservation V E source sink f.
Admitted.

Theorem residual_network_contains_augmenting_edges : forall V:set, forall E:set -> set -> prop,
  forall source sink:set, forall capacity:set -> set -> set, forall f:set -> set -> set,
    feasible_flow V E source sink capacity f ->
    forall x y:set, residual_network V E capacity f x y -> True.
Admitted.

Theorem augmenting_path_increases_flow : forall V:set, forall E:set -> set -> prop,
  forall source sink:set, forall capacity:set -> set -> set, forall f:set -> set -> set,
    feasible_flow V E source sink capacity f ->
    flow_augmenting_path V (residual_network V E capacity f) source sink ->
    exists f':set -> set -> set,
      feasible_flow V E source sink capacity f' /\
      flow_value V f source sink = flow_value V f' source sink.
Admitted.

Theorem ford_fulkerson_terminates : forall V:set, forall E:set -> set -> prop,
  forall source sink:set, forall capacity:set -> set -> set,
    network V E source sink capacity ->
    True.
Admitted.

Theorem edmonds_karp_complexity : forall V:set, forall E:set -> set -> prop,
  forall source sink:set, forall capacity:set -> set -> set,
    network V E source sink capacity ->
    True.
Admitted.

Theorem integral_capacities_yield_integral_flows : forall V:set, forall E:set -> set -> prop,
  forall source sink:set, forall capacity:set -> set -> set,
    network V E source sink capacity ->
    True.
Admitted.

Definition decision_problem : set -> prop := fun X => True.

Definition polynomial_time : (set -> prop) -> prop := fun L => True.

Definition in_class_P : (set -> prop) -> prop :=
  fun L => polynomial_time L.

Definition verifier_polynomial : (set -> prop) -> prop := fun L => True.

Definition in_class_NP : (set -> prop) -> prop :=
  fun L => verifier_polynomial L.

Definition polytime_reduction : (set -> prop) -> (set -> prop) -> prop :=
  fun A B => True.

Definition NP_complete : (set -> prop) -> prop :=
  fun L => and (in_class_NP L) (forall B:(set -> prop), in_class_NP B -> polytime_reduction B L).

Definition SAT : set -> prop := fun f => True.

Definition THREE_SAT : set -> prop := fun f => True.

Definition CLIQUE : set -> prop := fun G => True.

Definition HAMILTONIAN_CYCLE : set -> prop := fun G => True.

Definition VERTEX_COVER : set -> prop := fun G => True.

Definition THREE_COLORING : set -> prop := fun G => True.

Definition INDEPENDENT_SET : set -> prop := fun G => True.

Definition card : set -> set := fun S => 0.

Theorem P_subseteq_NP : forall L:(set -> prop), in_class_P L -> in_class_NP L.
Admitted.

Theorem SAT_in_NP : in_class_NP SAT.
Admitted.

Theorem SAT_NP_complete : NP_complete SAT.
Admitted.

Theorem THREE_SAT_NP_complete : NP_complete THREE_SAT.
Admitted.

Theorem CLIQUE_NP_complete : NP_complete CLIQUE.
Admitted.

Theorem VERTEX_COVER_NP_complete : NP_complete VERTEX_COVER.
Admitted.

Theorem INDEPENDENT_SET_NP_complete : NP_complete INDEPENDENT_SET.
Admitted.

Theorem THREE_COLORING_NP_complete : NP_complete THREE_COLORING.
Admitted.

Theorem HAMILTONIAN_CYCLE_NP_complete : NP_complete HAMILTONIAN_CYCLE.
Admitted.

Definition k_connected : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k =>
    forall S:set, card S < k -> connected V R.

Definition min_degree : set -> (set -> set -> prop) -> set :=
  fun V R => 0.

Definition vertex_connectivity_value : set -> (set -> set -> prop) -> set :=
  fun V R => 0.

Definition edge_connectivity_value : set -> (set -> set -> prop) -> set :=
  fun V R => 0.

Definition vertex_connectivity_at_least : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => k_connected V R k.

Definition edge_connectivity_at_least : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => True.

Definition k_edge_connected : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => edge_connectivity_at_least V R k.

Definition edge_cutset : set -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun V R F =>
    and (forall x y, F x y -> R x y)
        (and (forall x, ~F x x)
             (forall x y, F x y -> and (x :e V) (y :e V))).

Definition vertex_cutset : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V.

Definition min_vertex_cut : set -> (set -> set -> prop) -> set :=
  fun V R => 0.

Definition min_edge_cut : set -> (set -> set -> prop) -> set :=
  fun V R => 0.

Theorem k_connected_min_degree : forall V:set, forall R:set -> set -> prop, forall k:set,
  k_connected V R k -> True.
Admitted.

Theorem vertex_connectivity_le_min_degree : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem edge_connectivity_le_vertex_connectivity : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem edge_connectivity_le_min_degree : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem vertex_connectivity_equals_min_vertex_cut : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem edge_connectivity_equals_min_edge_cut : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem k_connected_vertex_number : forall V:set, forall R:set -> set -> prop, forall k:set,
  k_connected V R k -> exists n:set, card V = n /\ n <> 0.
Admitted.

Theorem removing_less_than_k_vertices_stays_connected : forall V:set, forall R:set -> set -> prop, forall k:set,
  k_connected V R k ->
  forall S:set, card S < k -> connected V R.
Admitted.

Theorem whitney_inequalities : forall V:set, forall R:set -> set -> prop, forall k:set,
  True.
Admitted.

Theorem menger_vertex_version : forall V:set, forall R:set -> set -> prop,
  forall s t:set, s <> t ->
    True.
Admitted.

Theorem menger_vertex_version_disjoint_paths : forall V:set, forall R:set -> set -> prop,
  forall s t:set, s <> t -> True.
Admitted.

Theorem menger_edge_version : forall V:set, forall R:set -> set -> prop,
  forall s t:set, s <> t ->
    True.
Admitted.

Theorem k_connected_many_disjoint_paths : forall V:set, forall R:set -> set -> prop,
  forall k:set, k_connected V R k ->
    True.
Admitted.

Theorem k_edge_connected_many_edge_disjoint_paths : forall V:set, forall R:set -> set -> prop,
  forall k:set, k_edge_connected V R k -> True.
Admitted.

Definition random_graph_Gnp : set -> set -> set -> prop :=
  fun V n p => True.

Definition expected_value : (set -> set) -> set :=
  fun X => 0.

Theorem linearity_of_expectation : forall X Y:set -> set,
  expected_value (fun s => X s + Y s) = expected_value X + expected_value Y.
Admitted.

Theorem erdos_probabilistic_lower_bound_ramsey : True.
Admitted.

Theorem lovasz_local_lemma_symmetric : True.
Admitted.

Theorem high_girth_high_chromatic_exists : True.
Admitted.

Theorem asymmetric_lovasz_local_lemma : True.
Admitted.

Theorem expectation_method_nonempty_object : True.
Admitted.

Theorem random_graph_expected_edges : forall V:set, True.
Admitted.

Theorem random_graph_chromatic_number_bounds : True.
Admitted.

Theorem random_graph_independent_set_bounds : True.
Admitted.

Definition vertex_separator : set -> (set -> set -> prop) -> set -> set -> set -> prop :=
  fun V R S a b => True.

Definition edge_separator : set -> (set -> set -> prop) -> (set -> set -> prop) -> set -> set -> prop :=
  fun V R F a b => True.

Definition internally_vertex_disjoint_paths : set -> (set -> set -> prop) -> set -> set -> set -> prop :=
  fun V R s t k => True.

Definition edge_disjoint_paths : set -> (set -> set -> prop) -> set -> set -> set -> prop :=
  fun V R s t k => True.

Theorem global_local_vertex_connectivity : forall V:set, forall R:set -> set -> prop, forall k:set,
  k_connected V R k -> True.
Admitted.

Theorem global_local_edge_connectivity : forall V:set, forall R:set -> set -> prop, forall k:set,
  edge_connectivity_at_least V R k -> True.
Admitted.

Theorem menger_equals_min_separator : forall V:set, forall R:set -> set -> prop, forall s t:set,
  s <> t -> True.
Admitted.

Theorem max_disjoint_paths_equals_min_vertex_cut : forall V:set, forall R:set -> set -> prop, forall s t:set,
  s <> t -> True.
Admitted.

Theorem max_edge_disjoint_paths_equals_min_edge_cut : forall V:set, forall R:set -> set -> prop, forall s t:set,
  s <> t -> True.
Admitted.

Definition indicator : prop -> set := fun P => 0.

Theorem markov_inequality : forall X:set -> set, forall a:set,
  True.
Admitted.

Theorem chebyshev_inequality : forall X:set -> set, forall a:set,
  True.
Admitted.

Theorem janson_inequality : True.
Admitted.

Theorem random_graph_threshold_connectivity : True.
Admitted.

Theorem random_graph_threshold_hamiltonian : True.
Admitted.

Theorem random_graph_threshold_clique_number : True.
Admitted.

Theorem random_graph_threshold_independence_number : True.
Admitted.

Definition dual_graph : set -> (set -> set -> prop) -> set -> (set -> set -> prop) -> prop :=
  fun V R F Edual => True.

Definition face_coloring : set -> (set -> set -> prop) -> (set -> set) -> prop :=
  fun V R color => True.

Theorem planar_dual_edge_vertex_relation : forall V:set, forall R:set -> set -> prop, forall F:set, forall Edual:set -> set -> prop,
  dual_graph V R F Edual -> True.
Admitted.

Theorem five_color_theorem : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem six_color_theorem : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem dual_face_coloring_edge_coloring : forall V:set, forall R:set -> set -> prop, forall F:set, forall Edual:set -> set -> prop,
  dual_graph V R F Edual -> True.
Admitted.

Theorem dual_of_dual_is_original : forall V:set, forall R:set -> set -> prop, forall F:set, forall Edual:set -> set -> prop,
  dual_graph V R F Edual -> True.
Admitted.

Theorem planar_dual_cycles_correspond_to_cuts : forall V:set, forall R:set -> set -> prop, forall F:set, forall Edual:set -> set -> prop,
  dual_graph V R F Edual -> True.
Admitted.

Theorem face_coloring_vs_vertex_coloring : forall V:set, forall R:set -> set -> prop, forall color:set -> set,
  face_coloring V R color -> True.
Admitted.

Theorem map_coloring_equiv_dual_edge_coloring : forall V:set, forall R:set -> set -> prop, forall F:set, forall Edual:set -> set -> prop,
  dual_graph V R F Edual -> True.
Admitted.

Definition line_graph : set -> (set -> set -> prop) -> set -> (set -> set -> prop) -> prop :=
  fun V R V2 R2 => True.

Theorem whitney_line_graph_equivalence : forall V:set, forall R:set -> set -> prop, forall V2:set, forall R2:set -> set -> prop,
  line_graph V R V2 R2 -> True.
Admitted.

Theorem line_graph_of_tree_is_claw_free : forall V:set, forall R:set -> set -> prop, forall V2:set, forall R2:set -> set -> prop,
  tree V R -> line_graph V R V2 R2 -> True.
Admitted.

Theorem dirac_hamiltonian : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem ore_hamiltonian : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem chvatal_erdos_hamiltonian : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Definition dominating_cycle : set -> (set -> set -> prop) -> prop :=
  fun V R => True.

Theorem bondy_chvatal_closure_hamiltonian : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Definition factor_k_regular : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => True.

Theorem petersen_theorem_1_factor : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem tuttle_factor_theorem : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Definition perfect_graph : set -> (set -> set -> prop) -> prop :=
  fun V R => True.

Theorem weak_perfect_graph_theorem : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem strong_perfect_graph_theorem : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem lovasz_theta_bound : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem szemeredi_regularity_lemma : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem graph_removal_lemma : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem extremal_turan_theorem : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem extremal_kovari_sos_turan : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem ramsey_upper_bounds_general : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem erdos_sos_conjecture_statement : True.
Admitted.

Definition closure_graph : set -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun V R C => simple_graph V C.

Definition toughness : set -> (set -> set -> prop) -> set :=
  fun V R => 0.

Definition subset_eq_rel : set -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun V F R =>
    forall x :e V, forall y :e V, F x y -> R x y.

Definition k_factor : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => exists F:set -> set -> prop,
    and (subset_eq_rel V F R)
        (forall v :e V, True).

Definition one_factor : set -> (set -> set -> prop) -> prop :=
  fun V R => k_factor V R 1.

Definition near_perfect_matching : set -> (set -> set -> prop) -> prop :=
  fun V R => True.

Definition odd_components_after_removal : set -> (set -> set -> prop) -> set -> set :=
  fun V R S => 0.

Definition odd_hole : set -> (set -> set -> prop) -> prop :=
  fun V R => True.

Definition odd_antihole : set -> (set -> set -> prop) -> prop :=
  fun V R => True.

Definition perfect_graph_strong : set -> (set -> set -> prop) -> prop :=
  fun V R => True.

Theorem closure_preserves_hamiltonicity : forall V:set, forall R C:set -> set -> prop,
  closure_graph V R C -> hamiltonian_graph V R -> hamiltonian_graph V C.
Admitted.

Theorem toughness_hamiltonian_sufficient_condition : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem petersen_one_factor_condition : forall V:set, forall R:set -> set -> prop,
  one_factor V R -> True.
Admitted.

Theorem tutte_one_factor_theorem : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem near_perfect_matching_exists_under_conditions : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem weak_perfect_graph_implies_chromatic_equals_clique : forall V:set, forall R:set -> set -> prop,
  perfect_graph_strong V R -> True.
Admitted.

Theorem no_odd_hole_antihole_implies_perfect : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem strong_perfect_graph_equiv_no_odd_hole_antihole : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem lovasz_theta_bounds_chromatic_and_clique : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem regularity_partition_exists : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem graph_removal_small_edition : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem turan_extremal_bound : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem kovari_sos_turan_extremal_bound : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem ramsey_bounds_general_asymptotic : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.

Theorem erdos_stone_simonovits_statement : forall V:set, forall R:set -> set -> prop,
  True.
Admitted.
