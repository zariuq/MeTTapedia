(** The length of a Lean list, for a type argument that is any set, and its
    invariance under permutation.

    List.length is the generated reading of Lean's definition; the generated
    equation theorems keep Lean's universe binders, so the constructor
    equations are restated here. **)

Theorem LeanListLength_nil : forall A,
  Lean_List_length A (Lean_List_nil_node A) = LeanNum 0.
let A.
prove Lean_List_rec A (LeanNum 0) (Lean_List_length_method1_0 A) (Lean_List_nil_node A) = LeanNum 0.
exact Lean_List_iota0 A (LeanNum 0) (Lean_List_length_method1_0 A).
Qed.

Theorem LeanListLength_cons : forall A, forall x :e A, forall xs :e Lean_List A,
  Lean_List_length A (Lean_List_cons_node A x xs) = Lean_Nat_add (Lean_List_length A xs) (LeanNum 1).
let A x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
prove Lean_List_rec A (LeanNum 0) (Lean_List_length_method1_0 A) (Lean_List_cons_node A x xs) =
  Lean_Nat_add (Lean_List_rec A (LeanNum 0) (Lean_List_length_method1_0 A) xs) (LeanNum 1).
rewrite Lean_List_iota1 A (LeanNum 0) (Lean_List_length_method1_0 A) x Hx xs Hxs.
rewrite Lean_List_length_method1_0_ap A x Hx.
rewrite Lean_List_length_method1_1_ap A x xs Hxs.
rewrite Lean_List_length_method1_2_ap A x xs
  (Lean_List_rec A (LeanNum 0) (Lean_List_length_method1_0 A) xs) (Lean_List_length_In A xs Hxs).
reflexivity.
Qed.

Theorem LeanListPerm_length_any : forall A, forall xs ys,
  LeanListPerm A xs ys -> Lean_List_length A xs = Lean_List_length A ys.
let A.
exact LeanListPerm_observer A Lean_Nat (Lean_List_length A)
  (fun x count => Lean_Nat_add count (LeanNum 1))
  (Lean_List_length_In A) (LeanListLength_cons A)
  (fun x Hx y Hy count Hcount => Lean_eq_refl (Lean_Nat_add (Lean_Nat_add count (LeanNum 1)) (LeanNum 1))).
Qed.
