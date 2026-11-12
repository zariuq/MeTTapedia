(** Membership through the evidence family generated from Lean's declaration. **)

Definition LeanListMember : set -> set -> set -> prop :=
  fun A value xs => exists witness, witness :e Lean_List_Mem A value xs.

Theorem LeanListMember_to_prop : forall A value xs, LeanListMember A value xs ->
  0 :e Lean_List_Mem_Prop A value xs.
let A value xs. assume H: LeanListMember A value xs.
exact SepI 1 (fun _ => LeanListMember A value xs) 0 In_0_1 H.
Qed.

Theorem LeanListMember_from_prop : forall A value xs,
  0 :e Lean_List_Mem_Prop A value xs -> LeanListMember A value xs.
let A value xs. assume H: 0 :e Lean_List_Mem_Prop A value xs.
exact SepE2 1 (fun _ => LeanListMember A value xs) 0 H.
Qed.

Theorem LeanListMember_head : forall A value, forall xs :e Lean_List A,
  LeanListMember A value (Lean_List_cons_node A value xs).
let A value xs. assume Hxs: xs :e Lean_List A.
exact (fun P H => H (Lean_List_Mem_head_node A value xs) (Lean_List_Mem_head_typed A value xs Hxs)).
Qed.

Theorem LeanListMember_tail : forall A value, forall head :e A, forall xs :e Lean_List A,
  LeanListMember A value xs -> LeanListMember A value (Lean_List_cons_node A head xs).
let A value head. assume Hhead: head :e A. let xs. assume Hxs: xs :e Lean_List A.
assume H: LeanListMember A value xs.
apply H. let witness. assume Hw: witness :e Lean_List_Mem A value xs.
exact (fun P K => K (Lean_List_Mem_tail_node A value head xs witness)
  (Lean_List_Mem_tail_typed A value head Hhead xs Hxs witness Hw)).
Qed.

Theorem LeanListMember_ind : forall A value, forall P : set -> prop,
  (forall xs :e Lean_List A, P (Lean_List_cons_node A value xs)) ->
  (forall head :e A, forall xs :e Lean_List A, LeanListMember A value xs -> P xs ->
    P (Lean_List_cons_node A head xs)) ->
  forall xs, LeanListMember A value xs -> P xs.
let A value P.
assume Hhead: forall xs :e Lean_List A, P (Lean_List_cons_node A value xs).
assume Htail: forall head :e A, forall xs :e Lean_List A, LeanListMember A value xs -> P xs ->
  P (Lean_List_cons_node A head xs).
let xs. assume H: LeanListMember A value xs.
apply H. let witness. assume Hw: witness :e Lean_List_Mem A value xs.
exact Lean_List_Mem_ind A value (fun xs _ => P xs) Hhead
  (fun head Hh tail Ht proof Hp IH => Htail head Hh tail Ht (fun Q K => K proof Hp) IH)
  xs witness Hw.
Qed.

Theorem LeanListMember_not_nil : forall A value, ~ LeanListMember A value (Lean_List_nil_node A).
let A value. assume H: LeanListMember A value (Lean_List_nil_node A).
claim Hnonempty: forall xs, LeanListMember A value xs -> xs <> Lean_List_nil_node A.
{ exact LeanListMember_ind A value (fun xs => xs <> Lean_List_nil_node A)
    (fun xs Hxs E => Lean_List_noconf0_1 A value xs (eq_sym_i (Lean_List_cons_node A value xs) (Lean_List_nil_node A) E))
    (fun head Hh xs Hxs Hmem IH E =>
      Lean_List_noconf0_1 A head xs (eq_sym_i (Lean_List_cons_node A head xs) (Lean_List_nil_node A) E)). }
exact Hnonempty (Lean_List_nil_node A) H (Lean_eq_refl (Lean_List_nil_node A)).
Qed.
