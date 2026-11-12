(** An empty left input returns the right list, not an empty list. **)
Theorem reject_wrong_merge_equation : forall u, nat_p u -> forall A :e LeanUniv u,
  forall ys :e Lean_List A, forall le :e (Pi_ x :e A, (Pi_ y :e A, Lean_Bool)),
  Lean_List_merge A (Lean_List_nil_node A) ys le = Lean_List_nil_node A.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let ys. assume Hys: ys :e Lean_List A.
let le. assume Hle: le :e (Pi_ x :e A, (Pi_ y :e A, Lean_Bool)).
exact LeanMerge_nil_left u Hu A HA ys Hys le Hle.
Qed.
