(** The source list-length function descends to permutation classes. **)

Theorem LeanListPerm_length : forall u, nat_p u -> forall A :e LeanUniv u,
  forall xs ys, LeanListPerm A xs ys -> Lean_List_length A xs = Lean_List_length A ys.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
exact LeanListPerm_length_any A.
Qed.

Definition LeanMultisetCard : set -> set -> set :=
  fun A value => LeanQuotLift (Lean_List_length A) value.

Theorem LeanMultisetCard_beta : forall u, nat_p u -> forall A :e LeanUniv u,
  forall xs :e Lean_List A, LeanMultisetCard A (LeanMultisetClass A xs) = Lean_List_length A xs.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
exact LeanMultisetLift_beta A (Lean_List_length A)
  (fun xs Hxs ys Hys Hperm => LeanListPerm_length u Hu A HA xs ys Hperm).
Qed.

Theorem LeanMultisetCard_typed : forall u, nat_p u -> forall A :e LeanUniv u,
  forall value :e LeanMultisetCarrier A, LeanMultisetCard A value :e Lean_Nat.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
exact LeanMultisetLift_typed A Lean_Nat (Lean_List_length A)
  (fun xs Hxs ys Hys Hperm => LeanListPerm_length u Hu A HA xs ys Hperm)
  (Lean_List_length_In A).
Qed.

Theorem LeanMultisetCard_nil : forall u, nat_p u -> forall A :e LeanUniv u,
  LeanMultisetCard A (LeanMultisetClass A (Lean_List_nil_node A)) = LeanNum 0.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
rewrite LeanMultisetCard_beta u Hu A HA (Lean_List_nil_node A) (Lean_List_nil_typed A).
exact Lean_List_length_eq_1 u Hu A HA.
Qed.

Theorem LeanMultisetCard_singleton : forall u, nat_p u -> forall A :e LeanUniv u,
  forall x :e A, LeanMultisetCard A (LeanMultisetClass A (Lean_List_cons_node A x (Lean_List_nil_node A))) = LeanNum 1.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u. let x. assume Hx: x :e A.
rewrite LeanMultisetCard_beta u Hu A HA (Lean_List_cons_node A x (Lean_List_nil_node A))
  (Lean_List_cons_typed A x Hx (Lean_List_nil_node A) (Lean_List_nil_typed A)).
rewrite Lean_List_length_eq_2 u Hu A HA x Hx (Lean_List_nil_node A) (Lean_List_nil_typed A).
rewrite Lean_List_length_eq_1 u Hu A HA.
exact LeanNum_add_eq 0 nat_0 1 nat_1 1 (add_nat_0L 1 nat_1).
Qed.

Theorem LeanMultisetCard_singleton_not_empty : forall u, nat_p u -> forall A :e LeanUniv u,
  forall x :e A, LeanMultisetCard A (LeanMultisetClass A (Lean_List_cons_node A x (Lean_List_nil_node A))) <> LeanNum 0.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u. let x. assume Hx: x :e A.
rewrite LeanMultisetCard_singleton u Hu A HA x Hx.
assume H: LeanNum 1 = LeanNum 0.
exact neq_1_0 (LeanNum_inj 1 nat_1 0 nat_0 H).
Qed.
