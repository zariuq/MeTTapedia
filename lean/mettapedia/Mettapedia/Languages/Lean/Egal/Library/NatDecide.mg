(** Lean's Nat.decLe between numerals at any distance.

   The reading of Nat.decLe is the canonical element of the proposition it
   decides (Lean_Nat_decLe_canonical), so between numerals it is isTrue
   when m <= m + k and isFalse when n < m. **)

Theorem Lean_Nat_decLe_num_true : forall m, nat_p m -> forall k, nat_p k ->
  Lean_Nat_decLe (LeanNum m) (LeanNum (add_nat m k))
    = Lean_Decidable_isTrue_node (Lean_Nat_le_Prop (LeanNum m) (LeanNum (add_nat m k))) 0.
let m. assume Hm: nat_p m. let k. assume Hk: nat_p k.
rewrite Lean_Nat_decLe_canonical (LeanNum m) (LeanNum_In m Hm) (LeanNum (add_nat m k)) (LeanNum_In (add_nat m k) (add_nat_p m Hm k Hk)).
exact Lean_DecCanon_true (Lean_Nat_le_Prop (LeanNum m) (LeanNum (add_nat m k))) (Lean_Nat_le_add_num m Hm k Hk).
Qed.

Theorem Lean_Nat_decLe_num_le : forall m, nat_p m -> forall n, nat_p n -> 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum n) ->
  Lean_Nat_decLe (LeanNum m) (LeanNum n) = Lean_Decidable_isTrue_node (Lean_Nat_le_Prop (LeanNum m) (LeanNum n)) 0.
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n. assume H: 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum n).
rewrite Lean_Nat_decLe_canonical (LeanNum m) (LeanNum_In m Hm) (LeanNum n) (LeanNum_In n Hn).
exact Lean_DecCanon_true (Lean_Nat_le_Prop (LeanNum m) (LeanNum n)) H.
Qed.

Theorem Lean_Nat_decLe_num_false : forall m, nat_p m -> forall n, nat_p n -> n :e m ->
  Lean_Nat_decLe (LeanNum m) (LeanNum n) = Lean_Decidable_isFalse_node (Lean_Nat_le_Prop (LeanNum m) (LeanNum n)) 0.
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n. assume Hnm: n :e m.
rewrite Lean_Nat_decLe_canonical (LeanNum m) (LeanNum_In m Hm) (LeanNum n) (LeanNum_In n Hn).
exact Lean_DecCanon_false (Lean_Nat_le_Prop (LeanNum m) (LeanNum n)) (Lean_Nat_le_num_not m Hm n Hn Hnm).
Qed.

(** dite at a decided proposition: the branch at the erased proof.  The
    branches are any lambdas over the proposition (and its refutations). **)
Theorem Lean_dite_true_ap : forall T, forall P, 0 :e P -> forall F G:set -> set,
  Lean_dite T P (Lean_Decidable_isTrue_node P 0) (fun h :e P => F h) (fun h :e (Pi_ ux :e P, Lean_False_Prop) => G h) = F 0.
let T P. assume HP: 0 :e P. let F G.
rewrite Lean_dite_unfold T P (Lean_Decidable_isTrue_node P 0) (fun h :e P => F h) (fun h :e (Pi_ ux :e P, Lean_False_Prop) => G h).
rewrite Lean_Decidable_iota1 P (fun h :e (Pi_ ux :e P, Lean_False_Prop) => G h) (fun h :e P => F h) 0 HP.
exact beta P F 0 HP.
Qed.

Theorem Lean_dite_false_ap : forall T, forall P :e LeanProp, 0 /:e P -> forall F G:set -> set,
  Lean_dite T P (Lean_Decidable_isFalse_node P 0) (fun h :e P => F h) (fun h :e (Pi_ ux :e P, Lean_False_Prop) => G h) = G 0.
let T P. assume HPp: P :e LeanProp. assume HP: 0 /:e P. let F G.
rewrite Lean_dite_unfold T P (Lean_Decidable_isFalse_node P 0) (fun h :e P => F h) (fun h :e (Pi_ ux :e P, Lean_False_Prop) => G h).
rewrite Lean_Decidable_iota0 P (fun h :e (Pi_ ux :e P, Lean_False_Prop) => G h) (fun h :e P => F h) 0 (Lean_refute_0 P HPp HP).
exact beta (Pi_ ux :e P, Lean_False_Prop) G 0 (Lean_refute_0 P HPp HP).
Qed.

Theorem Lean_ite_true_ap : forall T, forall P, 0 :e P -> forall t e, Lean_ite T P (Lean_Decidable_isTrue_node P 0) t e = t.
let T P. assume HP: 0 :e P. let t e.
rewrite Lean_ite_unfold T P (Lean_Decidable_isTrue_node P 0) t e.
rewrite Lean_Decidable_iota1 P (fun v_x :e (Pi_ ux :e P, Lean_False_Prop) => e) (fun v_x :e P => t) 0 HP.
exact beta P (fun v_x => t) 0 HP.
Qed.

Theorem Lean_ite_false_ap : forall T, forall P :e LeanProp, 0 /:e P -> forall t e, Lean_ite T P (Lean_Decidable_isFalse_node P 0) t e = e.
let T P. assume HPp: P :e LeanProp. assume HP: 0 /:e P. let t e.
rewrite Lean_ite_unfold T P (Lean_Decidable_isFalse_node P 0) t e.
rewrite Lean_Decidable_iota0 P (fun v_x :e (Pi_ ux :e P, Lean_False_Prop) => e) (fun v_x :e P => t) 0 (Lean_refute_0 P HPp HP).
exact beta (Pi_ ux :e P, Lean_False_Prop) (fun v_x => e) 0 (Lean_refute_0 P HPp HP).
Qed.

(** Positive and negative examples. **)
Theorem Lean_Nat_decLe_num_ex : Lean_Nat_decLe (LeanNum 2) (LeanNum (add_nat 2 3))
  = Lean_Decidable_isTrue_node (Lean_Nat_le_Prop (LeanNum 2) (LeanNum (add_nat 2 3))) 0.
exact Lean_Nat_decLe_num_true 2 nat_2 3 (nat_ordsucc 2 nat_2).
Qed.

Theorem Lean_Nat_decLe_num_ex_not : Lean_Nat_decLe (LeanNum 5) (LeanNum 2)
  = Lean_Decidable_isFalse_node (Lean_Nat_le_Prop (LeanNum 5) (LeanNum 2)) 0.
exact Lean_Nat_decLe_num_false 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))) 2 nat_2
  (ordsuccI1 4 2 (ordsuccI1 3 2 (ordsuccI2 2))).
Qed.
