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
