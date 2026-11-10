(** Characteristic equations of the source-derived, structurally fuelled merge. **)

Definition LeanMergeBudget : set -> set -> set -> set :=
  fun A xs ys => Lean_Nat_succ_node (Lean_Nat_add (Lean_List_length A xs) (Lean_List_length A ys)).

Theorem LeanMergeBudget_unfold : forall A xs ys, LeanMergeBudget A xs ys =
  Lean_Nat_succ_node (Lean_Nat_add (Lean_List_length A xs) (Lean_List_length A ys)).
let A xs ys. reflexivity.
Qed.

Theorem LeanMerge_to_fuel : forall u, nat_p u -> forall A :e LeanUniv u,
  forall xs ys :e Lean_List A, forall le :e (Pi_ x :e A, (Pi_ y :e A, Lean_Bool)),
  Lean_List_merge A xs ys le =
    Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_sourceFuel (LeanMergeBudget A xs ys) A xs ys le.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
let le. assume Hle: le :e (Pi_ x :e A, (Pi_ y :e A, Lean_Bool)).
rewrite Lean_List_merge_unfold A xs ys le.
exact Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_reading_eq_1 u Hu A HA xs Hxs ys Hys le Hle.
Qed.

Theorem LeanMerge_nil_left : forall u, nat_p u -> forall A :e LeanUniv u,
  forall ys :e Lean_List A, forall le :e (Pi_ x :e A, (Pi_ y :e A, Lean_Bool)),
  Lean_List_merge A (Lean_List_nil_node A) ys le = ys.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let ys. assume Hys: ys :e Lean_List A.
let le. assume Hle: le :e (Pi_ x :e A, (Pi_ y :e A, Lean_Bool)).
rewrite Lean_List_merge_unfold A (Lean_List_nil_node A) ys le.
rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_reading_eq_1
  u Hu A HA (Lean_List_nil_node A) (Lean_List_nil_typed A) ys Hys le Hle.
exact Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_sourceFuel_case0
  (Lean_Nat_add (Lean_List_length A (Lean_List_nil_node A)) (Lean_List_length A ys))
  (Lean_Nat_add_In (Lean_List_length A (Lean_List_nil_node A))
    (Lean_List_length_In A (Lean_List_nil_node A) (Lean_List_nil_typed A))
    (Lean_List_length A ys) (Lean_List_length_In A ys Hys))
  u Hu A HA ys Hys le Hle.
Qed.

Theorem LeanMerge_cons_nil : forall u, nat_p u -> forall A :e LeanUniv u,
  forall x :e A, forall xs :e Lean_List A,
  forall le :e (Pi_ a :e A, (Pi_ b :e A, Lean_Bool)),
  Lean_List_merge A (Lean_List_cons_node A x xs) (Lean_List_nil_node A) le = Lean_List_cons_node A x xs.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
let le. assume Hle: le :e (Pi_ a :e A, (Pi_ b :e A, Lean_Bool)).
rewrite Lean_List_merge_unfold A (Lean_List_cons_node A x xs) (Lean_List_nil_node A) le.
rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_reading_eq_1
  u Hu A HA (Lean_List_cons_node A x xs) (Lean_List_cons_typed A x Hx xs Hxs)
  (Lean_List_nil_node A) (Lean_List_nil_typed A) le Hle.
exact Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_sourceFuel_case1_branch1
  (Lean_Nat_add (Lean_List_length A (Lean_List_cons_node A x xs)) (Lean_List_length A (Lean_List_nil_node A)))
  (Lean_Nat_add_In (Lean_List_length A (Lean_List_cons_node A x xs))
    (Lean_List_length_In A (Lean_List_cons_node A x xs) (Lean_List_cons_typed A x Hx xs Hxs))
    (Lean_List_length A (Lean_List_nil_node A)) (Lean_List_length_In A (Lean_List_nil_node A) (Lean_List_nil_typed A)))
  u Hu A HA x Hx xs Hxs le Hle.
Qed.

Theorem LeanMerge_nil_right : forall u, nat_p u -> forall A :e LeanUniv u,
  forall xs :e Lean_List A, forall le :e (Pi_ x :e A, (Pi_ y :e A, Lean_Bool)),
  Lean_List_merge A xs (Lean_List_nil_node A) le = xs.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
exact Lean_List_ind A
  (fun xs => forall le :e (Pi_ x :e A, (Pi_ y :e A, Lean_Bool)),
    Lean_List_merge A xs (Lean_List_nil_node A) le = xs)
  (LeanMerge_nil_left u Hu A HA (Lean_List_nil_node A) (Lean_List_nil_typed A))
  (fun x Hx xs Hxs IH => LeanMerge_cons_nil u Hu A HA x Hx xs Hxs).
Qed.

Theorem Lean_dite_constant : forall A p decision yes no,
  Lean_dite A p decision (fun h :e p => yes) (fun h :e (Pi_ x :e p, Lean_False_Prop) => no) =
  Lean_ite A p decision yes no.
let A p decision yes no. reflexivity.
Qed.

Theorem LeanMerge_length_cons : forall u, nat_p u -> forall A :e LeanUniv u,
  forall x :e A, forall xs :e Lean_List A,
  Lean_List_length A (Lean_List_cons_node A x xs) = Lean_Nat_succ_node (Lean_List_length A xs).
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
rewrite Lean_List_length_eq_2 u Hu A HA x Hx xs Hxs.
rewrite LeanNum_S 0 nat_0. rewrite LeanNum_0.
exact NatAlgebra_add_oneR Lean_Nat_add Lean_Nat_add_In Lean_Nat_add_eq_1 Lean_Nat_add_eq_2
  (Lean_List_length A xs) (Lean_List_length_In A xs Hxs).
Qed.

Theorem LeanMerge_budget_left : forall u, nat_p u -> forall A :e LeanUniv u,
  forall x :e A, forall xs ys :e Lean_List A,
  Lean_Nat_add (Lean_List_length A (Lean_List_cons_node A x xs)) (Lean_List_length A ys) =
    LeanMergeBudget A xs ys.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
rewrite LeanMerge_length_cons u Hu A HA x Hx xs Hxs.
exact NatAlgebra_add_succL Lean_Nat_add Lean_Nat_add_In Lean_Nat_add_eq_1 Lean_Nat_add_eq_2
  (Lean_List_length A xs) (Lean_List_length_In A xs Hxs)
  (Lean_List_length A ys) (Lean_List_length_In A ys Hys).
Qed.

Theorem LeanMerge_budget_right : forall u, nat_p u -> forall A :e LeanUniv u,
  forall xs :e Lean_List A, forall y :e A, forall ys :e Lean_List A,
  Lean_Nat_add (Lean_List_length A xs) (Lean_List_length A (Lean_List_cons_node A y ys)) =
    LeanMergeBudget A xs ys.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let xs. assume Hxs: xs :e Lean_List A. let y. assume Hy: y :e A. let ys. assume Hys: ys :e Lean_List A.
rewrite LeanMerge_length_cons u Hu A HA y Hy ys Hys.
exact Lean_Nat_add_eq_2 (Lean_List_length A xs) (Lean_List_length_In A xs Hxs)
  (Lean_List_length A ys) (Lean_List_length_In A ys Hys).
Qed.

Theorem LeanMerge_cons_cons : forall u, nat_p u -> forall A :e LeanUniv u,
  forall x :e A, forall xs :e Lean_List A, forall y :e A, forall ys :e Lean_List A,
  forall le :e (Pi_ a :e A, (Pi_ b :e A, Lean_Bool)),
  Lean_List_merge A (Lean_List_cons_node A x xs) (Lean_List_cons_node A y ys) le =
    Lean_ite (Lean_List A) (Lean_Eq_Prop Lean_Bool (le x y) Lean_Bool_true_node)
      (Lean_instDecidableEqBool (le x y) Lean_Bool_true_node)
      (Lean_List_cons_node A x (Lean_List_merge A xs (Lean_List_cons_node A y ys) le))
      (Lean_List_cons_node A y (Lean_List_merge A (Lean_List_cons_node A x xs) ys le)).
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
let y. assume Hy: y :e A. let ys. assume Hys: ys :e Lean_List A.
let le. assume Hle: le :e (Pi_ a :e A, (Pi_ b :e A, Lean_Bool)).
claim Hleft: Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_sourceFuel
  (Lean_Nat_add (Lean_List_length A (Lean_List_cons_node A x xs))
    (Lean_List_length A (Lean_List_cons_node A y ys))) A xs (Lean_List_cons_node A y ys) le =
  Lean_List_merge A xs (Lean_List_cons_node A y ys) le.
{ rewrite LeanMerge_budget_left u Hu A HA x Hx xs Hxs
    (Lean_List_cons_node A y ys) (Lean_List_cons_typed A y Hy ys Hys).
  exact eq_sym_i (Lean_List_merge A xs (Lean_List_cons_node A y ys) le)
    (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_sourceFuel
      (LeanMergeBudget A xs (Lean_List_cons_node A y ys)) A xs (Lean_List_cons_node A y ys) le)
    (LeanMerge_to_fuel u Hu A HA xs Hxs (Lean_List_cons_node A y ys)
      (Lean_List_cons_typed A y Hy ys Hys) le Hle). }
claim Hright: Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_sourceFuel
  (Lean_Nat_add (Lean_List_length A (Lean_List_cons_node A x xs))
    (Lean_List_length A (Lean_List_cons_node A y ys))) A (Lean_List_cons_node A x xs) ys le =
  Lean_List_merge A (Lean_List_cons_node A x xs) ys le.
{ rewrite LeanMerge_budget_right u Hu A HA (Lean_List_cons_node A x xs)
    (Lean_List_cons_typed A x Hx xs Hxs) y Hy ys Hys.
  exact eq_sym_i (Lean_List_merge A (Lean_List_cons_node A x xs) ys le)
    (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_sourceFuel
      (LeanMergeBudget A (Lean_List_cons_node A x xs) ys) A (Lean_List_cons_node A x xs) ys le)
    (LeanMerge_to_fuel u Hu A HA (Lean_List_cons_node A x xs)
      (Lean_List_cons_typed A x Hx xs Hxs) ys Hys le Hle). }
rewrite LeanMerge_to_fuel u Hu A HA (Lean_List_cons_node A x xs) (Lean_List_cons_typed A x Hx xs Hxs)
  (Lean_List_cons_node A y ys) (Lean_List_cons_typed A y Hy ys Hys) le Hle.
rewrite LeanMergeBudget_unfold A (Lean_List_cons_node A x xs) (Lean_List_cons_node A y ys).
rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_Merge_sourceFuel_case3
  (Lean_Nat_add (Lean_List_length A (Lean_List_cons_node A x xs))
    (Lean_List_length A (Lean_List_cons_node A y ys)))
  (Lean_Nat_add_In (Lean_List_length A (Lean_List_cons_node A x xs))
    (Lean_List_length_In A (Lean_List_cons_node A x xs) (Lean_List_cons_typed A x Hx xs Hxs))
    (Lean_List_length A (Lean_List_cons_node A y ys))
    (Lean_List_length_In A (Lean_List_cons_node A y ys) (Lean_List_cons_typed A y Hy ys Hys)))
  u Hu A HA le Hle x Hx xs Hxs y Hy ys Hys.
rewrite Hleft. rewrite Hright.
exact Lean_dite_constant (Lean_List A) (Lean_Eq_Prop Lean_Bool (le x y) Lean_Bool_true_node)
  (Lean_instDecidableEqBool (le x y) Lean_Bool_true_node)
  (Lean_List_cons_node A x (Lean_List_merge A xs (Lean_List_cons_node A y ys) le))
  (Lean_List_cons_node A y (Lean_List_merge A (Lean_List_cons_node A x xs) ys le)).
Qed.
