(** Multisets as classes of the permutation relation generated from Lean. **)

Definition LeanMultisetCarrier : set -> set :=
  fun A => LeanSetoidQuot (Lean_List A) (LeanListPerm A).

Definition LeanMultisetClass : set -> set -> set :=
  fun A xs => LeanQuotClass (Lean_List A) (LeanListPerm A) xs.

Theorem LeanMultisetClass_typed : forall A, forall xs :e Lean_List A,
  LeanMultisetClass A xs :e LeanMultisetCarrier A.
let A xs. assume Hxs: xs :e Lean_List A.
exact LeanQuotClass_typed (Lean_List A) (LeanListPerm A) xs Hxs.
Qed.

Theorem LeanMultisetClass_sound : forall A, forall xs ys :e Lean_List A,
  LeanListPerm A xs ys -> LeanMultisetClass A xs = LeanMultisetClass A ys.
let A xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
assume Hperm: LeanListPerm A xs ys.
exact LeanQuotClass_sound (Lean_List A) (LeanListPerm A)
  (fun x Hx y Hy H => LeanListPerm_symm A x y H)
  (LeanListPerm_trans A) xs Hxs ys Hys Hperm.
Qed.

Theorem LeanMultisetClass_effective : forall A, forall xs ys :e Lean_List A,
  LeanMultisetClass A xs = LeanMultisetClass A ys -> LeanListPerm A xs ys.
let A xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
exact LeanQuotClass_effective (Lean_List A) (LeanListPerm A)
  (LeanListPerm_refl A) xs Hxs ys Hys.
Qed.

Theorem LeanMultisetClass_swap : forall A, forall x y :e A, forall tail :e Lean_List A,
  LeanMultisetClass A (Lean_List_cons_node A y (Lean_List_cons_node A x tail)) =
  LeanMultisetClass A (Lean_List_cons_node A x (Lean_List_cons_node A y tail)).
let A x. assume Hx: x :e A. let y. assume Hy: y :e A.
let tail. assume Htail: tail :e Lean_List A.
exact LeanMultisetClass_sound A
  (Lean_List_cons_node A y (Lean_List_cons_node A x tail))
  (Lean_List_cons_typed A y Hy (Lean_List_cons_node A x tail) (Lean_List_cons_typed A x Hx tail Htail))
  (Lean_List_cons_node A x (Lean_List_cons_node A y tail))
  (Lean_List_cons_typed A x Hx (Lean_List_cons_node A y tail) (Lean_List_cons_typed A y Hy tail Htail))
  (LeanListPerm_swap A x Hx y Hy tail Htail).
Qed.

Theorem LeanMultisetLift_beta : forall A, forall f:set -> set,
  (forall xs ys :e Lean_List A, LeanListPerm A xs ys -> f xs = f ys) ->
  forall xs :e Lean_List A, LeanQuotLift f (LeanMultisetClass A xs) = f xs.
let A f. assume Hrespect: forall xs ys :e Lean_List A, LeanListPerm A xs ys -> f xs = f ys.
exact LeanQuotLift_beta (Lean_List A) (LeanListPerm A) (LeanListPerm_refl A) f Hrespect.
Qed.

Theorem LeanMultisetLift_typed : forall A B, forall f:set -> set,
  (forall xs ys :e Lean_List A, LeanListPerm A xs ys -> f xs = f ys) ->
  (forall xs :e Lean_List A, f xs :e B) ->
  forall value :e LeanMultisetCarrier A, LeanQuotLift f value :e B.
let A B f. assume Hrespect: forall xs ys :e Lean_List A, LeanListPerm A xs ys -> f xs = f ys.
assume Htyped: forall xs :e Lean_List A, f xs :e B.
exact LeanQuotLift_typed (Lean_List A) B (LeanListPerm A) (LeanListPerm_refl A) f Hrespect Htyped.
Qed.

Theorem LeanMultisetLift_unique : forall A, forall f g:set -> set,
  (forall xs ys :e Lean_List A, LeanListPerm A xs ys -> f xs = f ys) ->
  (forall xs :e Lean_List A, g (LeanMultisetClass A xs) = f xs) ->
  forall value :e LeanMultisetCarrier A, g value = LeanQuotLift f value.
let A f g. assume Hrespect: forall xs ys :e Lean_List A, LeanListPerm A xs ys -> f xs = f ys.
assume Hbeta: forall xs :e Lean_List A, g (LeanMultisetClass A xs) = f xs.
exact LeanQuotLift_unique (Lean_List A) (LeanListPerm A) (LeanListPerm_refl A) f g Hrespect Hbeta.
Qed.
