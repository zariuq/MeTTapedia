(** Fuel that is not above the rank of the state does not give the function:
    the fuelled form of Nat.minFacAux at fuel zero is not shown equal to its
    form above the rank, because no rank lies below zero. **)
Theorem reject_insufficient_fuel : forall n, nat_p n -> forall x :e Lean_Nat,
  Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum 0) (LeanNum n) x
    = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc (LeanMinFacAux_rank (LeanNum n) x))) (LeanNum n) x.
let n. assume Hn: nat_p n. let x. assume Hx: x :e Lean_Nat.
claim Hrank: nat_p (LeanMinFacAux_rank (LeanNum n) x).
{ exact LeanNat_ord_nat (Lean_Nat_sub (Lean_Nat_add (LeanNum n) (LeanNum 2)) x)
    (Lean_Nat_sub_In (Lean_Nat_add (LeanNum n) (LeanNum 2))
      (Lean_Nat_add_In (LeanNum n) (LeanNum_In n Hn) (LeanNum 2) (LeanNum_In 2 nat_2)) x Hx). }
exact RankedLayers_stable Lean_Nat (LeanMinFacAux_rank (LeanNum n))
  (fun k y => Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum k) (LeanNum n) y)
  (LeanMinFacAux_layers n Hn)
  0 nat_0 (ordsucc (LeanMinFacAux_rank (LeanNum n) x)) (nat_ordsucc (LeanMinFacAux_rank (LeanNum n) x) Hrank)
  x Hx (ordsuccI2 (LeanMinFacAux_rank (LeanNum n) x)) (ordsuccI2 (LeanMinFacAux_rank (LeanNum n) x)).
Qed.
