(** Facts about generated families, checked after generated/LeanFamilies.mg. **)

(** The index is enforced: nil is not a vector of successor length. **)
Theorem LeanVec_nil_not_succ : forall A, forall n :e Lean_Nat, Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec_nil_node A /:e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec A (Lean_Nat_succ_node n).
let A n. assume Hn: n :e Lean_Nat. assume H: Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec_nil_node A :e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec A (Lean_Nat_succ_node n).
claim L1: LeanNum 0 = Lean_Nat_succ_node n.
{ exact Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec_one_index A (LeanNum 0) (Lean_Nat_succ_node n) (Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec_nil_node A) (Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec_nil_typed A) H. }
apply Lean_Nat_noconf0_1 n.
rewrite <- L1. rewrite LeanNum_0. reflexivity.
Qed.

(** Fin 1 has the value 0: its guard 0 < 1 is Nat.le 1 1, proved by refl. **)
Theorem LeanFin_zero_of_one :
  Lean_Fin_mk_node (Lean_Nat_succ_node Lean_Nat_zero_node) Lean_Nat_zero_node 0
    :e Lean_Fin (Lean_Nat_succ_node Lean_Nat_zero_node).
claim G: 0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node Lean_Nat_zero_node) (Lean_Nat_succ_node Lean_Nat_zero_node).
{ exact Lean_Nat_le_refl_proof_ok (Lean_Nat_succ_node Lean_Nat_zero_node). }
exact Lean_Fin_mk_typed (Lean_Nat_succ_node Lean_Nat_zero_node) Lean_Nat_zero_node Lean_Nat_zero_typed 0
  (SepI 1 (fun z => z :e Lean_Nat_le_Prop (Lean_Nat_succ_node Lean_Nat_zero_node) (Lean_Nat_succ_node Lean_Nat_zero_node)) 0 In_0_1 G).
Qed.
