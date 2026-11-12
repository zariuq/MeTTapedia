(** Lean's equations List.merge.eq_1, eq_2 and eq_3, for the reading: the
    characteristic equations of the fuelled merge (Library/Merge.mg), at
    Lean's statements. **)

Theorem LeanMerge_equation_1 : forall l_u_1, nat_p l_u_1 -> forall v_u945 :e LeanUniv l_u_1, forall v_ys :e (Lean_List v_u945), forall v_le :e (Pi_ ux :e v_u945, (Pi_ ux :e v_u945, Lean_Bool)), (Lean_List_merge v_u945 (Lean_List_nil_node v_u945) v_ys v_le) = v_ys.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let ys. assume Hys: ys :e Lean_List A.
let le. assume Hle: le :e (Pi_ x :e A, (Pi_ y :e A, Lean_Bool)).
exact LeanMerge_nil_left u Hu A HA ys Hys le Hle.
Qed.

Theorem LeanMerge_equation_2 : forall l_u_1, nat_p l_u_1 -> forall v_u945 :e LeanUniv l_u_1, forall v_xs :e (Lean_List v_u945), forall v_le :e (Pi_ ux :e v_u945, (Pi_ ux :e v_u945, Lean_Bool)), ((v_xs = (Lean_List_nil_node v_u945)) -> False) -> (Lean_List_merge v_u945 v_xs (Lean_List_nil_node v_u945) v_le) = v_xs.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let xs. assume Hxs: xs :e Lean_List A.
let le. assume Hle: le :e (Pi_ x :e A, (Pi_ y :e A, Lean_Bool)).
assume Hnotnil: xs = Lean_List_nil_node A -> False.
exact LeanMerge_nil_right u Hu A HA xs Hxs le Hle.
Qed.

Theorem LeanMerge_equation_3 : forall l_u_1, nat_p l_u_1 -> forall v_u945 :e LeanUniv l_u_1, forall v_le :e (Pi_ ux :e v_u945, (Pi_ ux :e v_u945, Lean_Bool)), forall v_x :e v_u945, forall v_xs_2 :e (Lean_List v_u945), forall v_y :e v_u945, forall v_ys_2 :e (Lean_List v_u945), (Lean_List_merge v_u945 (Lean_List_cons_node v_u945 v_x v_xs_2) (Lean_List_cons_node v_u945 v_y v_ys_2) v_le) = (Lean_ite (Lean_List v_u945) (Lean_Eq_Prop Lean_Bool (v_le v_x v_y) Lean_Bool_true_node) (Lean_instDecidableEqBool (v_le v_x v_y) Lean_Bool_true_node) (Lean_List_cons_node v_u945 v_x (Lean_List_merge v_u945 v_xs_2 (Lean_List_cons_node v_u945 v_y v_ys_2) v_le)) (Lean_List_cons_node v_u945 v_y (Lean_List_merge v_u945 (Lean_List_cons_node v_u945 v_x v_xs_2) v_ys_2 v_le))).
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let le. assume Hle: le :e (Pi_ a :e A, (Pi_ b :e A, Lean_Bool)).
let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
let y. assume Hy: y :e A. let ys. assume Hys: ys :e Lean_List A.
exact LeanMerge_cons_cons u Hu A HA x Hx xs Hxs y Hy ys Hys le Hle.
Qed.
