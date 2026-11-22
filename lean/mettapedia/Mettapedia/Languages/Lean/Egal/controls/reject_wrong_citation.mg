(** A theorem that Lean's proof terms cite stands for its own statement only:
    List.Perm.map at Bool is cited with every argument it requires, and it does not prove
    that filtering keeps a permutation. **)
Theorem reject_wrong_citation : forall l, nat_p l -> forall A :e LeanUniv l, forall p :e (Pi_ ux :e A, Lean_Bool),
  forall l1 :e (Lean_List A), forall l2 :e (Lean_List A),
  0 :e (Lean_List_Perm_Prop A l1 l2) ->
  0 :e (Lean_List_Perm_Prop A (Lean_List_filter A p l1) (Lean_List_filter A p l2)).
let l. assume Hl: nat_p l. let A. assume HA: A :e LeanUniv l.
let p. assume Hp: p :e (Pi_ ux :e A, Lean_Bool).
let l1. assume H1: l1 :e (Lean_List A). let l2. assume H2: l2 :e (Lean_List A).
assume H: 0 :e (Lean_List_Perm_Prop A l1 l2).
exact Lean_List_Perm_map_proof l Hl 0 nat_0 A HA Lean_Bool (Lean_Bool_type_In 0 nat_0) p Hp l1 H1 l2 H2 H.
Qed.
