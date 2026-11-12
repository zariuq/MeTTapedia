; Proof libraries may use earlier source definitions and justify later ones.
; Their dependencies are part of generation order, not runtime assumptions.
(EgalProofLibrary NaturalDivision
  (Nat.add Nat.mul Nat.sub Nat.div.go Nat.div Nat.modCore.go Nat.modCore Nat.mod
   Nat.decLe Nat.decLt ite dite)
  ("Library/NatAdd.mg" "Library/NatMul.mg" "Library/NatSub.mg"
   "Library/NatDecide.mg" "Library/NatDiv.mg" "Library/Divisibility.mg"))
(EgalTypingUses Nat.decidable_dvd NaturalDivision)
(EgalTypingUses Nat.gcd NaturalDivision)

; The statements remain the exported source equations. The target library
; supplies proofs of those statements after all definitions are available.
(EgalSourceEquationProofs Nat.gcd ("Library/NatGcd.mg")
  ((Nat.gcd.eq_1 "LeanGcd_equation")))

; A cited theorem whose proof uses a proof library is placed after it.
(EgalTypingUses Nat.dvd_iff_mod_eq_zero NaturalDivision)

; Lean's list functions on permuted lists (Library/ListPermFacts.mg), for the
; theorems the multiset operations' proofs cite.
(EgalProofLibrary Permutations (List.length List.map List.filter List.foldr)
  ("Library/ListPermutation.mg" "Library/ListLengthFacts.mg" "Library/ListPermFacts.mg"))
(EgalTypingUses List.Perm.length_eq Permutations)
(EgalTypingUses List.Perm.map Permutations)
(EgalTypingUses List.Perm.filter Permutations)
; Membership and pairwise relations under permutation (Library/ListNodupFacts.mg).
(EgalProofLibrary Nodup () ("Library/ListNodupFacts.mg"))
(EgalTypingUses List.Perm.nodup_iff Permutations)
(EgalTypingUses List.Perm.nodup_iff Nodup)
; Multisets without duplicates (Library/MultisetNodupFacts.mg): after the
; functions it is about, for the theorems the Finset operations' proofs cite.
(EgalProofLibrary MultisetNodup
  (Multiset.Nodup Multiset.ofList Multiset.range Multiset.filter List.range List.filter Decidable.decide Quot.liftOn)
  ("Library/MultisetNodupFacts.mg"))
(EgalTypingUses Multiset.nodup_range Permutations)
(EgalTypingUses Multiset.nodup_range Nodup)
(EgalTypingUses Multiset.nodup_range MultisetNodup)
(EgalTypingUses Multiset.Nodup.filter Permutations)
(EgalTypingUses Multiset.Nodup.filter Nodup)
(EgalTypingUses Multiset.Nodup.filter MultisetNodup)
; Lean's LeftCommutative as a proposition about the operation, and the
; addition of an additive commutative monoid (Library/LeftCommutativeFacts.mg,
; Library/AdditiveFacts.mg), for the theorems Multiset.foldr and Multiset.sum cite.
(EgalProofLibrary LeftCommutative () ("Library/LeftCommutativeFacts.mg"))
(EgalProofLibrary Additive (Add.add AddSemigroup.toAdd AddMonoid.toAddSemigroup AddCommMonoid.toAddMonoid)
  ("Library/AdditiveFacts.mg"))
(EgalTypingUses List.Perm.foldr_eq Permutations)
(EgalTypingUses List.Perm.foldr_eq LeftCommutative)
(EgalTypingUses Multiset.sum._proof_1 LeftCommutative)
(EgalTypingUses Multiset.sum._proof_1 Additive)

; Irreducible natural numbers: Lean's Nat.prime_def_lt' and the decision of a
; numeral's primality (Library/NatPrimality.mg over the arithmetic of
; Library/NatFactors.mg); Lean's order instance on Nat and the shift of a
; bounded quantifier (Library/NatOrderInstance.mg).
(EgalProofLibrary NatFactors () ("Library/NatFactors.mg"))
(EgalProofLibrary NatPrimality (IsUnit Units.val Irreducible Nat.instMonoid Nat.mul Nat.pow)
  ("Library/NatPrimality.mg"))
(EgalProofLibrary NatOrderInstance (LT.lt instLTNat Nat.add Nat.sub Nat.pred Not)
  ("Library/NatOrderInstance.mg" "Library/NatBallFacts.mg"))
(EgalTypingUses Nat.prime_def_lt' NaturalDivision)
(EgalTypingUses Nat.prime_def_lt' NatFactors)
(EgalTypingUses Nat.prime_def_lt' NatPrimality)
(EgalTypingUses Nat.lt_succ_of_lt NaturalDivision)
(EgalTypingUses Nat.lt_succ_of_lt NatFactors)
(EgalTypingUses Nat.lt_succ_of_lt NatPrimality)
(EgalTypingUses Nat.lt_succ_of_lt NatOrderInstance)
(EgalTypingUses Nat.decidableLoHi._proof_1 NaturalDivision)
(EgalTypingUses Nat.decidableLoHi._proof_1 NatFactors)
(EgalTypingUses Nat.decidableLoHi._proof_1 NatPrimality)
(EgalTypingUses Nat.decidableLoHi._proof_1 NatOrderInstance)
(EgalTypingUses Nat.decidableBallLT._proof_7 NaturalDivision)
(EgalTypingUses Nat.decidableBallLT._proof_7 NatFactors)
(EgalTypingUses Nat.decidableBallLT._proof_7 NatPrimality)
(EgalTypingUses Nat.decidableBallLT._proof_7 NatOrderInstance)
(EgalTypingUses Nat.decidableBallLT._proof_3 NaturalDivision)
(EgalTypingUses Nat.decidableBallLT._proof_3 NatFactors)
(EgalTypingUses Nat.decidableBallLT._proof_3 NatPrimality)
(EgalTypingUses Nat.decidableBallLT._proof_3 NatOrderInstance)
(EgalTypingUses Nat.decidableBallLT._proof_8 NaturalDivision)
(EgalTypingUses Nat.decidableBallLT._proof_8 NatFactors)
(EgalTypingUses Nat.decidableBallLT._proof_8 NatPrimality)
(EgalTypingUses Nat.decidableBallLT._proof_8 NatOrderInstance)

; The lengths of the two parts of List.splitAt (Library/ListSplitFacts.mg):
; the halves that Lean's merge sort recurses on have the lengths its
; definition states.
(EgalProofLibrary ListSplit
  (List.splitAt.go List.splitAt List.reverseAux List.reverse List.length Nat.div Nat.add Subtype.val Prod.fst Prod.snd)
  ("Library/ListSplitFacts.mg"))
(EgalTypingUses _private.Init.Data.List.Sort.Basic.0.List.MergeSort.Internal.splitInTwo._proof_3 NaturalDivision)
(EgalTypingUses _private.Init.Data.List.Sort.Basic.0.List.MergeSort.Internal.splitInTwo._proof_3 Permutations)
(EgalTypingUses _private.Init.Data.List.Sort.Basic.0.List.MergeSort.Internal.splitInTwo._proof_3 ListSplit)
(EgalTypingUses _private.Init.Data.List.Sort.Basic.0.List.MergeSort.Internal.splitInTwo._proof_4 NaturalDivision)
(EgalTypingUses _private.Init.Data.List.Sort.Basic.0.List.MergeSort.Internal.splitInTwo._proof_4 Permutations)
(EgalTypingUses _private.Init.Data.List.Sort.Basic.0.List.MergeSort.Internal.splitInTwo._proof_4 ListSplit)

; Lean's equations for functions read through their fuel, and for a decision
; read by its type, proved in Egal.  A decision is determined by the truth of
; its proposition (Library/DecisionTruth.mg); a Lean natural number has an
; ordinal (Library/NatOrdinal.mg); above the rank of a state the fuel no
; longer matters (Library/RankedRecursion.mg).  Each function's library
; follows the functions, with the equations it proves.
(EgalProofLibrary Truth (ite dite Nat.add) ("Library/DecisionTruth.mg" "Library/NatOrdinal.mg"))
(EgalTypingUses Nat.minFacAux NaturalDivision)
(EgalTypingUses Nat.minFacAux NatFactors)
(EgalTypingUses Nat.minFacAux Truth)
(EgalSourceEquationProofs Nat.minFacAux ("Library/MinFacAuxFuel.mg")
  ((Nat.minFacAux.eq_1 "LeanMinFacAux_equation")))
(EgalSourceEquationProofs Nat.primeFactorsList ("Library/PrimeFactorsFuel.mg")
  ((Nat.primeFactorsList.eq_1 "LeanPrimeFactors_equation_1")
   (Nat.primeFactorsList.eq_2 "LeanPrimeFactors_equation_2")
   (Nat.primeFactorsList.eq_3 "LeanPrimeFactors_equation_3")))
(EgalSourceEquationProofs List.merge ("Library/Merge.mg" "Library/MergeEquations.mg")
  ((List.merge.eq_1 "LeanMerge_equation_1")
   (List.merge.eq_2 "LeanMerge_equation_2")
   (List.merge.eq_3 "LeanMerge_equation_3")))
(EgalTypingUses List.mergeSort NaturalDivision)
(EgalTypingUses List.mergeSort NatFactors)
(EgalTypingUses List.mergeSort Truth)
(EgalSourceEquationProofs List.mergeSort ("Library/MergeSortFuel.mg")
  ((List.mergeSort.eq_1 "LeanMergeSort_equation_1")
   (List.mergeSort.eq_2 "LeanMergeSort_equation_2")
   (List.mergeSort.eq_3 "LeanMergeSort_equation_3")))
(EgalTypingUses Nat.decidableBallLT NaturalDivision)
(EgalTypingUses Nat.decidableBallLT NatFactors)
(EgalTypingUses Nat.decidableBallLT Truth)
(EgalSourceEquationProofs Nat.decidableBallLT ("Library/NatBallDecision.mg")
  ((Nat.decidableBallLT.eq_2 "LeanNatBall_decision_step")))
