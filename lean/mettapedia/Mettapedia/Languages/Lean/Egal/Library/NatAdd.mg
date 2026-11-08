(** Natural number operations that CeTTa computes natively.

   CeTTa adds two integers directly; Lean's Nat.add is the function read
   from its equation theorems (the generated functions).  The reading of
   numerals carries Egal's own addition of ordinals to it:
   LeanNum m + LeanNum n = LeanNum (m + n).  A computation that adds numerals
   is therefore checked with ordinal arithmetic, as CeTTa computes it. **)

Theorem LeanNum_add : forall m, nat_p m -> forall n, nat_p n ->
  Lean_Nat_add (LeanNum m) (LeanNum n) = LeanNum (add_nat m n).
let m. assume Hm: nat_p m.
apply nat_ind.
- prove Lean_Nat_add (LeanNum m) (LeanNum 0) = LeanNum (add_nat m 0).
  rewrite add_nat_0R m.
  rewrite LeanNum_0.
  exact Lean_Nat_add_eq_1 (LeanNum m) (LeanNum_In m Hm).
- let n. assume Hn: nat_p n.
  assume IH: Lean_Nat_add (LeanNum m) (LeanNum n) = LeanNum (add_nat m n).
  prove Lean_Nat_add (LeanNum m) (LeanNum (ordsucc n)) = LeanNum (add_nat m (ordsucc n)).
  rewrite add_nat_SR m n Hn.
  rewrite LeanNum_S n Hn.
  rewrite LeanNum_S (add_nat m n) (add_nat_p m Hm n Hn).
  rewrite Lean_Nat_add_eq_2 (LeanNum m) (LeanNum_In m Hm) (LeanNum n) (LeanNum_In n Hn).
  rewrite IH.
  reflexivity.
Qed.

(** The form used by computations: the sum k is given, with its ordinal
    proof. **)
Theorem LeanNum_add_eq : forall m, nat_p m -> forall n, nat_p n -> forall k,
  add_nat m n = k -> Lean_Nat_add (LeanNum m) (LeanNum n) = LeanNum k.
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n. let k. assume Hk: add_nat m n = k.
rewrite <- Hk.
exact LeanNum_add m Hm n Hn.
Qed.
