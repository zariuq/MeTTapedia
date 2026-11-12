(** Quotient primitives for Type carriers, with the relation represented by
    a set-valued predicate. The equivalence closure is part of the carrier. **)

Definition Lean_Quot : set -> set -> set :=
  fun A relation => LeanRelationQuot A (fun x y => 0 :e relation x y).
Definition Lean_Quot_mk : set -> set -> set -> set :=
  fun A relation x => LeanRelationClass A (fun x y => 0 :e relation x y) x.
Definition Lean_Quot_lift : set -> set -> set -> set -> set -> set -> set :=
  fun A relation B function respect value => LeanQuotLift (fun x => function x) value.

Theorem Lean_Quot_type_In : forall A relation, forall u, nat_p u -> A :e LeanUniv u ->
  Lean_Quot A relation :e LeanUniv u.
let A relation u. assume Hu: nat_p u. assume HA: A :e LeanUniv u.
claim Hpower: Power A :e LeanUniv u.
{ exact ZF_Power_closed (LeanUniv u) (LeanUniv_ZF_closed u Hu) A HA. }
apply ZF_Subq_In (LeanUniv u) (LeanUniv_TransSet u Hu) (LeanUniv_ZF_closed u Hu) (Power A) Hpower.
let value. assume Hvalue: value :e Lean_Quot A relation.
apply ReplE_impred A (LeanQuotClass A (LeanEqvClosure A (fun x y => 0 :e relation x y))) value Hvalue.
let x. assume Hx: x :e A. assume E: value = LeanQuotClass A (LeanEqvClosure A (fun x y => 0 :e relation x y)) x.
rewrite E.
exact PowerI A (LeanQuotClass A (LeanEqvClosure A (fun x y => 0 :e relation x y)) x)
  (Sep_Subq A (LeanEqvClosure A (fun x y => 0 :e relation x y) x)).
Qed.

Theorem Lean_Quot_mk_In : forall A, forall relation :e (Pi_ x :e A, (Pi_ y :e A, LeanProp)),
  forall x :e A, Lean_Quot_mk A relation x :e Lean_Quot A relation.
let A relation. assume Hr: relation :e (Pi_ x :e A, (Pi_ y :e A, LeanProp)).
exact LeanRelationClass_typed A (fun x y => 0 :e relation x y).
Qed.

Theorem Lean_Quot_mk_sound : forall A relation, forall x y :e A,
  0 :e relation x y -> Lean_Quot_mk A relation x = Lean_Quot_mk A relation y.
let A relation. exact LeanRelationClass_sound A (fun x y => 0 :e relation x y).
Qed.

Theorem Lean_Quot_lift_typed : forall A relation B, forall function :e (Pi_ x :e A, B),
  (forall x y :e A, 0 :e relation x y -> function x = function y) ->
  forall respect, forall value :e Lean_Quot A relation,
    Lean_Quot_lift A relation B function respect value :e B.
let A relation B function. assume Hf: function :e (Pi_ x :e A, B).
assume Hrespect: forall x y :e A, 0 :e relation x y -> function x = function y.
let respect.
exact LeanRelationLift_typed A B (fun x y => 0 :e relation x y) (fun x => function x) Hrespect
  (fun x Hx => ap_Pi A (fun _ => B) function x Hf Hx).
Qed.

Theorem Lean_Quot_lift_beta : forall A relation B, forall function :e (Pi_ x :e A, B),
  (forall x y :e A, 0 :e relation x y -> function x = function y) ->
  forall respect, forall x :e A,
    Lean_Quot_lift A relation B function respect (Lean_Quot_mk A relation x) = function x.
let A relation B function. assume Hf: function :e (Pi_ x :e A, B).
assume Hrespect: forall x y :e A, 0 :e relation x y -> function x = function y.
let respect. exact LeanRelationLift_beta A (fun x y => 0 :e relation x y) (fun x => function x) Hrespect.
Qed.
