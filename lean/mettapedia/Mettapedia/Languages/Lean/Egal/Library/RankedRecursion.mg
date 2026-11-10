(** A recipe observes recursive values only at states of smaller natural rank. **)

Definition RankedLocal : set -> (set -> set) -> ((set -> set) -> set -> set) -> prop :=
  fun A rank step => forall x :e A, forall f g : set -> set,
    (forall y :e A, rank y :e rank x -> f y = g y) -> step f x = step g x.

Definition RankedEquations : set -> ((set -> set) -> set -> set) -> (set -> set -> set) -> prop :=
  fun A step fuel => forall k, nat_p k -> forall x :e A,
    fuel (ordsucc k) x = step (fuel k) x.

Theorem RankedFuel_stable : forall A, forall rank : set -> set,
  forall step : (set -> set) -> set -> set, RankedLocal A rank step ->
  forall first second : set -> set -> set,
  RankedEquations A step first -> RankedEquations A step second ->
  forall k, nat_p k -> forall l, nat_p l -> forall x :e A,
    rank x :e k -> rank x :e l -> first k x = second l x.
let A rank step. assume Hlocal: RankedLocal A rank step.
let first second. assume Hfirst: RankedEquations A step first.
assume Hsecond: RankedEquations A step second.
apply nat_ind.
- let l. assume Hl: nat_p l. let x. assume Hx: x :e A.
  assume Hzero: rank x :e 0. assume Hxl: rank x :e l.
  exact FalseE (EmptyE (rank x) Hzero) (first 0 x = second l x).
- let k. assume Hk: nat_p k.
  assume IH: forall l, nat_p l -> forall x :e A,
    rank x :e k -> rank x :e l -> first k x = second l x.
  let l. assume Hl: nat_p l. apply nat_inv l Hl.
  + assume El: l = 0. rewrite El. let x. assume Hx: x :e A.
    assume Hxk: rank x :e ordsucc k. assume Hzero: rank x :e 0.
    exact FalseE (EmptyE (rank x) Hzero) (first (ordsucc k) x = second 0 x).
  + assume Hex: exists j, nat_p j /\ l = ordsucc j.
    apply Hex. let j. assume Hj: nat_p j /\ l = ordsucc j.
    apply Hj. assume Hjn: nat_p j. assume El: l = ordsucc j.
    rewrite El. let x. assume Hx: x :e A.
    assume Hxk: rank x :e ordsucc k. assume Hxj: rank x :e ordsucc j.
    rewrite Hfirst k Hk x Hx. rewrite Hsecond j Hjn x Hx.
    apply Hlocal x Hx (first k) (second j).
    let y. assume Hy: y :e A. assume Hyx: rank y :e rank x.
    exact IH j Hjn y Hy (nat_ordsucc_trans k Hk (rank x) Hxk (rank y) Hyx)
      (nat_ordsucc_trans j Hjn (rank x) Hxj (rank y) Hyx).
Qed.

Definition RankedRead : (set -> set) -> (set -> set -> set) -> set -> set :=
  fun rank fuel x => fuel (ordsucc (rank x)) x.

Theorem RankedRead_equation : forall A, forall rank : set -> set,
  (forall x :e A, nat_p (rank x)) ->
  forall step : (set -> set) -> set -> set, RankedLocal A rank step ->
  forall fuel : set -> set -> set, RankedEquations A step fuel ->
  forall x :e A, RankedRead rank fuel x = step (RankedRead rank fuel) x.
let A rank. assume Hrank: forall x :e A, nat_p (rank x).
let step. assume Hlocal: RankedLocal A rank step.
let fuel. assume Heq: RankedEquations A step fuel.
let x. assume Hx: x :e A.
prove fuel (ordsucc (rank x)) x = step (RankedRead rank fuel) x.
rewrite Heq (rank x) (Hrank x Hx) x Hx.
apply Hlocal x Hx (fuel (rank x)) (RankedRead rank fuel).
let y. assume Hy: y :e A. assume Hyx: rank y :e rank x.
exact RankedFuel_stable A rank step Hlocal fuel fuel Heq Heq
  (rank x) (Hrank x Hx) (ordsucc (rank y)) (nat_ordsucc (rank y) (Hrank y Hy)) y Hy Hyx
  (ordsuccI2 (rank y)).
Qed.

Theorem RankedRead_unique : forall A, forall rank : set -> set,
  (forall x :e A, nat_p (rank x)) ->
  forall step : (set -> set) -> set -> set, RankedLocal A rank step ->
  forall fuel : set -> set -> set, RankedEquations A step fuel ->
  forall function : set -> set,
  (forall x :e A, function x = step function x) ->
  forall x :e A, RankedRead rank fuel x = function x.
let A rank. assume Hrank: forall x :e A, nat_p (rank x).
let step. assume Hlocal: RankedLocal A rank step.
let fuel. assume Heq: RankedEquations A step fuel.
let function. assume Hfunction: forall x :e A, function x = step function x.
claim Hconstant: RankedEquations A step (fun k x => function x).
{ let k. assume Hk: nat_p k. exact Hfunction. }
let x. assume Hx: x :e A.
exact RankedFuel_stable A rank step Hlocal fuel (fun k x => function x) Heq Hconstant
  (ordsucc (rank x)) (nat_ordsucc (rank x) (Hrank x Hx))
  (ordsucc (rank x)) (nat_ordsucc (rank x) (Hrank x Hx)) x Hx
  (ordsuccI2 (rank x)) (ordsuccI2 (rank x)).
Qed.

(** A self-call cannot be justified by assigning every state rank zero. **)
Theorem RankedLocal_self_call_refused :
  ~ RankedLocal {0} (fun x => 0) (fun f x => f x).
assume Hlocal: RankedLocal {0} (fun x => 0) (fun f x => f x).
claim Hempty: forall y :e {0}, 0 :e 0 -> 0 = 1.
{ let y. assume Hy: y :e {0}. assume Hbad: 0 :e 0.
  exact FalseE (EmptyE 0 Hbad) (0 = 1). }
exact neq_0_1 (Hlocal 0 (SingI 0) (fun y => 0) (fun y => 1) Hempty).
Qed.
