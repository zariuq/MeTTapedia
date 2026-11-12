(** A theorem that Lean's proof terms cite stands for its own statement only:
    List.Perm.map does not prove that filtering keeps a permutation. **)
Theorem reject_wrong_citation : forall A, forall p :e (Pi_ ux :e A, Lean_Bool),
  forall l1 :e (Lean_List A), forall l2 :e (Lean_List A),
  0 :e (Lean_List_Perm_Prop A l1 l2) ->
  0 :e (Lean_List_Perm_Prop A (Lean_List_filter A p l1) (Lean_List_filter A p l2)).
let A p. assume Hp: p :e (Pi_ ux :e A, Lean_Bool).
let l1. assume H1: l1 :e (Lean_List A). let l2. assume H2: l2 :e (Lean_List A).
assume H: 0 :e (Lean_List_Perm_Prop A l1 l2).
exact Lean_List_Perm_map_proof A Lean_Bool p Hp l1 H1 l2 H2 H.
Qed.
