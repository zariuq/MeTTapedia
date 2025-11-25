Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Axiom equip_17_without_one : forall v :e 18, equip 17 (18 :\: {v}).

Axiom partition_17_5_implies_12 : forall V N Non:set,
  equip 17 V ->
  N c= V ->
  Non c= V ->
  (forall x :e V, x :e N \/ x :e Non) ->
  (forall x, x :e N -> x /:e Non) ->
  ~(exists T, T c= N /\ equip 6 T) ->
  exists S, S c= Non /\ equip 12 S.

Theorem neighbors_form_indep_set : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  forall v :e 18,
    is_indep_set 18 R {w :e 18 :\: {v} | R v w}.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
let v. assume Hv: v :e 18.
set N := {w :e 18 :\: {v} | R v w}.
prove is_indep_set 18 R N.
prove N c= 18 /\ (forall x :e N, forall y :e N, x <> y -> ~R x y).
apply andI (N c= 18) (forall x :e N, forall y :e N, x <> y -> ~R x y).
- prove N c= 18.
  let w. assume Hw: w :e N.
  apply SepE (18 :\: {v}) (fun z => R v z) w Hw (w :e 18).
  assume Hw18v: w :e 18 :\: {v}.
  assume _: R v w.
  apply setminusE 18 {v} w Hw18v.
  assume Hw18: w :e 18.
  assume _: w /:e {v}.
  exact Hw18.
- prove forall x :e N, forall y :e N, x <> y -> ~R x y.
  let x. assume Hx: x :e N.
  let y. assume Hy: y :e N.
  assume Hneq: x <> y.
  prove ~R x y.
  assume HRxy: R x y.
  claim HRvx: R v x.
    apply SepE (18 :\: {v}) (fun z => R v z) x Hx (R v x).
    assume _: x :e 18 :\: {v}.
    assume H: R v x.
    exact H.
  claim HRvy: R v y.
    apply SepE (18 :\: {v}) (fun z => R v z) y Hy (R v y).
    assume _: y :e 18 :\: {v}.
    assume H: R v y.
    exact H.
  claim Hx18: x :e 18.
    apply SepE (18 :\: {v}) (fun z => R v z) x Hx (x :e 18).
    assume Hx18v: x :e 18 :\: {v}.
    assume _: R v x.
    apply setminusE 18 {v} x Hx18v.
    assume H: x :e 18.
    assume _: x /:e {v}.
    exact H.
  claim Hy18: y :e 18.
    apply SepE (18 :\: {v}) (fun z => R v z) y Hy (y :e 18).
    assume Hy18v: y :e 18 :\: {v}.
    assume _: R v y.
    apply setminusE 18 {v} y Hy18v.
    assume H: y :e 18.
    assume _: y /:e {v}.
    exact H.
  claim HRxv: R x v.
    exact Hsym v x HRvx.
  exact Htf x Hx18 v Hv y Hy18 HRxv HRvy HRxy.
Qed.

Theorem no_6_neighbors : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18,
    ~(exists T, T c= {w :e 18 :\: {v} | R v w} /\ equip 6 T).
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
let v. assume Hv: v :e 18.
set N := {w :e 18 :\: {v} | R v w}.
prove ~(exists T, T c= N /\ equip 6 T).
assume Hex: exists T, T c= N /\ equip 6 T.
apply Hex.
let T. assume HT: T c= N /\ equip 6 T.
prove False.
claim HTN: T c= N.
  exact andEL (T c= N) (equip 6 T) HT.
claim HT6: equip 6 T.
  exact andER (T c= N) (equip 6 T) HT.
claim HN_indep: is_indep_set 18 R N.
  exact neighbors_form_indep_set R Hsym Htf v Hv.
claim HN18: N c= 18.
  exact andEL (N c= 18) (forall x :e N, forall y :e N, x <> y -> ~R x y) HN_indep.
claim HN_edges: forall x :e N, forall y :e N, x <> y -> ~R x y.
  exact andER (N c= 18) (forall x :e N, forall y :e N, x <> y -> ~R x y) HN_indep.
claim HT18: T c= 18.
  let t. assume Ht: t :e T.
  exact HN18 t (HTN t Ht).
apply Hno6 T HT18 HT6.
prove is_indep_set 18 R T.
prove T c= 18 /\ (forall x :e T, forall y :e T, x <> y -> ~R x y).
apply andI (T c= 18) (forall x :e T, forall y :e T, x <> y -> ~R x y).
- exact HT18.
- prove forall x :e T, forall y :e T, x <> y -> ~R x y.
  let x. assume Hx: x :e T.
  let y. assume Hy: y :e T.
  assume Hneq: x <> y.
  exact HN_edges x (HTN x Hx) y (HTN y Hy) Hneq.
Qed.

Theorem setminus_subset_18 : forall v :e 18, 18 :\: {v} c= 18.
let v. assume Hv: v :e 18.
let x. assume Hx: x :e 18 :\: {v}.
apply setminusE 18 {v} x Hx.
assume H18: x :e 18.
assume _: x /:e {v}.
exact H18.
Qed.

Theorem nonneighbors_subset_18 : forall R:set -> set -> prop,
  forall v :e 18, {w :e 18 :\: {v} | ~R v w} c= 18.
let R. let v. assume Hv: v :e 18.
let x. assume Hx: x :e {w :e 18 :\: {v} | ~R v w}.
apply SepE (18 :\: {v}) (fun z => ~R v z) x Hx (x :e 18).
assume Hx18v: x :e 18 :\: {v}.
assume _: ~R v x.
exact setminus_subset_18 v Hv x Hx18v.
Qed.

Theorem neighbors_partition : forall R:set -> set -> prop,
  forall v :e 18, forall x :e 18 :\: {v},
    x :e {w :e 18 :\: {v} | R v w} \/ x :e {w :e 18 :\: {v} | ~R v w}.
let R. let v. assume Hv: v :e 18.
let x. assume Hx: x :e 18 :\: {v}.
prove x :e {w :e 18 :\: {v} | R v w} \/ x :e {w :e 18 :\: {v} | ~R v w}.
apply xm (R v x).
- assume HRvx: R v x.
  apply orIL.
  prove x :e {w :e 18 :\: {v} | R v w}.
  exact SepI (18 :\: {v}) (fun z => R v z) x Hx HRvx.
- assume HnRvx: ~R v x.
  apply orIR.
  prove x :e {w :e 18 :\: {v} | ~R v w}.
  exact SepI (18 :\: {v}) (fun z => ~R v z) x Hx HnRvx.
Qed.

Theorem neighbors_disjoint : forall R:set -> set -> prop,
  forall v :e 18, forall x,
    x :e {w :e 18 :\: {v} | R v w} -> x /:e {w :e 18 :\: {v} | ~R v w}.
let R. let v. assume Hv: v :e 18.
let x. assume Hx: x :e {w :e 18 :\: {v} | R v w}.
prove x /:e {w :e 18 :\: {v} | ~R v w}.
assume HxNon: x :e {w :e 18 :\: {v} | ~R v w}.
claim HRvx: R v x.
  apply SepE (18 :\: {v}) (fun z => R v z) x Hx (R v x).
  assume _: x :e 18 :\: {v}.
  assume H: R v x.
  exact H.
claim HnRvx: ~R v x.
  apply SepE (18 :\: {v}) (fun z => ~R v z) x HxNon (~R v x).
  assume _: x :e 18 :\: {v}.
  assume H: ~R v x.
  exact H.
exact HnRvx HRvx.
Qed.

Theorem neighbors_subset_V : forall R:set -> set -> prop,
  forall v :e 18, {w :e 18 :\: {v} | R v w} c= 18 :\: {v}.
let R. let v. assume Hv: v :e 18.
let x. assume Hx: x :e {w :e 18 :\: {v} | R v w}.
apply SepE (18 :\: {v}) (fun z => R v z) x Hx (x :e 18 :\: {v}).
assume Hx18v: x :e 18 :\: {v}.
assume _: R v x.
exact Hx18v.
Qed.

Theorem nonneighbors_subset_V : forall R:set -> set -> prop,
  forall v :e 18, {w :e 18 :\: {v} | ~R v w} c= 18 :\: {v}.
let R. let v. assume Hv: v :e 18.
let x. assume Hx: x :e {w :e 18 :\: {v} | ~R v w}.
apply SepE (18 :\: {v}) (fun z => ~R v z) x Hx (x :e 18 :\: {v}).
assume Hx18v: x :e 18 :\: {v}.
assume _: ~R v x.
exact Hx18v.
Qed.

Theorem vertex_has_12_nonneighbors : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
let v. assume Hv: v :e 18.
prove exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
set V := 18 :\: {v}.
set N := {w :e V | R v w}.
set Non := {w :e V | ~R v w}.
claim Heq17V: equip 17 V.
  exact equip_17_without_one v Hv.
claim HNV: N c= V.
  exact neighbors_subset_V R v Hv.
claim HNonV: Non c= V.
  exact nonneighbors_subset_V R v Hv.
claim Hpart: forall x :e V, x :e N \/ x :e Non.
  exact neighbors_partition R v Hv.
claim Hdisj: forall x, x :e N -> x /:e Non.
  exact neighbors_disjoint R v Hv.
claim Hno6N: ~(exists T, T c= N /\ equip 6 T).
  exact no_6_neighbors R Hsym Htf Hno6 v Hv.
apply partition_17_5_implies_12 V N Non Heq17V HNV HNonV Hpart Hdisj Hno6N.
let S. assume HS: S c= Non /\ equip 12 S.
claim HSNon: S c= Non.
  exact andEL (S c= Non) (equip 12 S) HS.
claim HS12: equip 12 S.
  exact andER (S c= Non) (equip 12 S) HS.
witness S.
prove S c= 18 /\ equip 12 S /\ (forall t :e S, ~R v t) /\ v /:e S.
apply and4I (S c= 18) (equip 12 S) (forall t :e S, ~R v t) (v /:e S).
- prove S c= 18.
  let s. assume Hs: s :e S.
  claim HsNon: s :e Non.
    exact HSNon s Hs.
  claim HsV: s :e V.
    exact HNonV s HsNon.
  exact setminus_subset_18 v Hv s HsV.
- exact HS12.
- prove forall t :e S, ~R v t.
  let t. assume Ht: t :e S.
  claim HtNon: t :e Non.
    exact HSNon t Ht.
  apply SepE V (fun z => ~R v z) t HtNon (~R v t).
  assume _: t :e V.
  assume H: ~R v t.
  exact H.
- prove v /:e S.
  assume HvS: v :e S.
  claim HvNon: v :e Non.
    exact HSNon v HvS.
  claim HvV: v :e V.
    exact HNonV v HvNon.
  claim Hvnotin: v /:e {v}.
    apply setminusE 18 {v} v HvV.
    assume _: v :e 18.
    assume H: v /:e {v}.
    exact H.
  apply Hvnotin.
  exact SingI v.
Qed.