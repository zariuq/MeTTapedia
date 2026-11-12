(** A quotient lift's erased proof is interpreted by its full respect law. **)

Definition LeanQuotRespect : set -> set -> set -> set -> set :=
  fun A relation B function =>
    Pi_ x :e A, Pi_ y :e A, Pi_ proof :e relation x y, Lean_Eq_Prop B (function x) (function y).

Theorem Lean_Quot_respect_native : forall A relation B function,
  forall respect :e LeanQuotRespect A relation B function,
  forall x y :e A, 0 :e relation x y -> function x = function y.
let A relation B function respect.
assume Hrespect: respect :e LeanQuotRespect A relation B function.
let x. assume Hx: x :e A. let y. assume Hy: y :e A. assume Hxy: 0 :e relation x y.
claim Hfirst: respect x :e (Pi_ y :e A, Pi_ proof :e relation x y, Lean_Eq_Prop B (function x) (function y)).
{ exact ap_Pi A (fun x => Pi_ y :e A, Pi_ proof :e relation x y, Lean_Eq_Prop B (function x) (function y))
    respect x Hrespect Hx. }
claim Hsecond: respect x y :e (Pi_ proof :e relation x y, Lean_Eq_Prop B (function x) (function y)).
{ exact ap_Pi A (fun y => Pi_ proof :e relation x y, Lean_Eq_Prop B (function x) (function y))
    (respect x) y Hfirst Hy. }
exact LeanEq_sound B (function x) (function y) (respect x y 0)
  (ap_Pi (relation x y) (fun _ => Lean_Eq_Prop B (function x) (function y)) (respect x y) 0 Hsecond Hxy).
Qed.

Theorem Lean_Quot_respect_value : forall A, forall relation :e (Pi_ x :e A, Pi_ y :e A, LeanProp),
  forall B function,
  (forall x y :e A, 0 :e relation x y -> function x = function y) ->
  0 :e LeanQuotRespect A relation B function.
let A relation. assume Hr: relation :e (Pi_ x :e A, Pi_ y :e A, LeanProp).
let B function. assume Hrespect: forall x y :e A, 0 :e relation x y -> function x = function y.
prove 0 :e (Pi_ x :e A, Pi_ y :e A, Pi_ proof :e relation x y, Lean_Eq_Prop B (function x) (function y)).
apply Pi_0_In A (fun x => Pi_ y :e A, Pi_ proof :e relation x y, Lean_Eq_Prop B (function x) (function y)).
let x. assume Hx: x :e A.
prove 0 :e (Pi_ y :e A, Pi_ proof :e relation x y, Lean_Eq_Prop B (function x) (function y)).
apply Pi_0_In A (fun y => Pi_ proof :e relation x y, Lean_Eq_Prop B (function x) (function y)).
let y. assume Hy: y :e A.
prove 0 :e (Pi_ proof :e relation x y, Lean_Eq_Prop B (function x) (function y)).
apply Pi_0_In (relation x y) (fun proof => Lean_Eq_Prop B (function x) (function y)).
let proof. assume Hp: proof :e relation x y.
claim Hrelation: relation x y :e LeanProp.
{ exact ap_Pi A (fun _ => LeanProp) (relation x) y
    (ap_Pi A (fun _ => Pi_ y :e A, LeanProp) relation x Hr Hx) Hy. }
claim Hzero: proof = 0.
{ exact cases_1 proof (PowerE 1 (relation x y) Hrelation proof Hp) (fun value => value = 0) (Lean_eq_refl 0). }
exact Lean_Eq_proof_of B (function x) (function y)
  (Hrespect x Hx y Hy (In_eq_l proof 0 (relation x y) Hzero Hp)).
Qed.

Theorem Lean_Quot_lift_In : forall A, forall relation :e (Pi_ x :e A, Pi_ y :e A, LeanProp),
  forall B, forall function :e (Pi_ x :e A, B),
  forall respect :e LeanQuotRespect A relation B function,
  forall value :e Lean_Quot A relation, Lean_Quot_lift A relation B function respect value :e B.
let A relation. assume Hr: relation :e (Pi_ x :e A, Pi_ y :e A, LeanProp).
let B function. assume Hf: function :e (Pi_ x :e A, B).
let respect. assume Hrespect: respect :e LeanQuotRespect A relation B function.
exact Lean_Quot_lift_typed A relation B function Hf
  (Lean_Quot_respect_native A relation B function respect Hrespect) respect.
Qed.

Theorem Lean_Quot_lift_beta_value : forall A, forall relation :e (Pi_ x :e A, Pi_ y :e A, LeanProp),
  forall B, forall function :e (Pi_ x :e A, B),
  forall respect :e LeanQuotRespect A relation B function,
  forall x :e A, Lean_Quot_lift A relation B function respect (Lean_Quot_mk A relation x) = function x.
let A relation. assume Hr: relation :e (Pi_ x :e A, Pi_ y :e A, LeanProp).
let B function. assume Hf: function :e (Pi_ x :e A, B).
let respect. assume Hrespect: respect :e LeanQuotRespect A relation B function.
exact Lean_Quot_lift_beta A relation B function Hf
  (Lean_Quot_respect_native A relation B function respect Hrespect) respect.
Qed.
