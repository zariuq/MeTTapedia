
(** Foundations of Lean's logic that Lean proves from its quotient axiom at
    any universe level.  The reading interprets quotients of carriers in Type
    only, so these are proved here from set theory, and a transported proof
    cites them where Lean's proof does. **)

(** funext at levels u and v: functions equal at every argument are equal.
    Both lie in the product's set of functions, so Pi_ext applies; Lean's
    equation at each argument is the reading's proof of Eq there. **)
Theorem Lean_funext : forall u, nat_p u -> forall v, nat_p v ->
  forall A :e LeanSort u, forall B :e (Pi_ x :e A, LeanSort v),
  forall f :e (Pi_ x :e A, B x), forall g :e (Pi_ x :e A, B x),
  0 :e (Pi_ x :e A, Lean_Eq_Prop (B x) (f x) (g x)) -> 0 :e Lean_Eq_Prop (Pi_ x :e A, B x) f g.
let u. assume Hu: nat_p u. let v. assume Hv: nat_p v.
let A. assume HA: A :e LeanSort u. let B. assume HB: B :e (Pi_ x :e A, LeanSort v).
let f. assume Hf: f :e (Pi_ x :e A, B x).
let g. assume Hg: g :e (Pi_ x :e A, B x).
assume H: 0 :e (Pi_ x :e A, Lean_Eq_Prop (B x) (f x) (g x)).
apply Lean_Eq_proof_of (Pi_ x :e A, B x) f g.
apply Pi_ext A (fun x => B x) f Hf g Hg.
let x. assume Hx: x :e A.
exact LeanEq_sound (B x) (f x) (g x) 0 (Pi_0_ap A (fun x => Lean_Eq_Prop (B x) (f x) (g x)) H x Hx).
Qed.
