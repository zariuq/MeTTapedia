(** The relation identifies both representatives; identity does not respect it. **)
Theorem reject_noninvariant_quotient_lift :
  LeanQuotLift (fun x => x) (LeanQuotClass {0,1} (fun _ _ => True) 0) = 0.
apply LeanQuotLift_beta {0,1} (fun _ _ => True)
  (fun x Hx => TrueI) (fun x => x).
- let x. assume Hx: x :e {0,1}. let y. assume Hy: y :e {0,1}. assume H: True.
  reflexivity.
- exact UPairI1 0 1.
Qed.
