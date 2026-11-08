(** decide at the canonical element of Decidable p: true when p holds,
    false when it does not. **)

Theorem Lean_decide_DecCanon_true : forall p, 0 :e p -> Lean_Decidable_decide p (Lean_DecCanon p) = Lean_Bool_true_node.
let p. assume H: 0 :e p.
rewrite Lean_Decidable_decide_unfold.
rewrite Lean_DecCanon_rec_true p H.
exact beta p (fun v_x => Lean_Bool_true_node) 0 H.
Qed.

Theorem Lean_decide_DecCanon_false : forall p :e LeanProp, 0 /:e p ->
  Lean_Decidable_decide p (Lean_DecCanon p) = Lean_Bool_false_node.
let p. assume Hp: p :e LeanProp. assume H: 0 /:e p.
rewrite Lean_Decidable_decide_unfold.
rewrite Lean_DecCanon_rec_false p Hp H.
exact beta (Pi_ ux :e p, Lean_False_Prop) (fun v_x => Lean_Bool_false_node) 0 (Lean_refute_0 p Hp H).
Qed.
