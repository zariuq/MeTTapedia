import Mettapedia.Logic.PLNInclusionExclusionIdentifiability

/-!
# Multideduction Residual Decomposition (Chapter 9 Positive Core)

This module complements the inclusion-exclusion identifiability no-go results with
an explicit residual decomposition:

- two-term estimate (first two IE terms),
- residual/error term (triple overlap),
- exact union decomposition in `ℤ`,
- assumption-indexed agreement endpoint for corrected estimators.
-/

namespace Mettapedia.Logic.PLNMultideductionResidual

open Mettapedia.Logic.PLNInclusionExclusionIdentifiability

variable {α : Type*} [DecidableEq α]

/-- Two-term inclusion-exclusion estimate (integer form). -/
def twoTermEstimateZ (A B C : Finset α) : ℤ :=
  (ieTerm1 A B C : ℤ) - (ieTerm2 A B C : ℤ)

/-- Residual/error term for three-event union: triple overlap cardinality. -/
def residualZ (A B C : Finset α) : ℤ :=
  ((A ∩ B ∩ C).card : ℤ)

/-- Corrected multideduction estimate with an explicit correction value. -/
def correctedEstimateZ (ξ : ℤ) (A B C : Finset α) : ℤ :=
  twoTermEstimateZ A B C + ξ

theorem unionCard_eq_twoTerm_plus_residualZ (A B C : Finset α) :
    (unionCard A B C : ℤ) = twoTermEstimateZ A B C + residualZ A B C := by
  have hUnionInter :
      ((A ∩ C) ∪ (B ∩ C)) = ((A ∪ B) ∩ C) := by
    ext x
    simp [Finset.mem_union, Finset.mem_inter, or_and_right]
  have hTripleInter :
      ((A ∩ C) ∩ (B ∩ C)) = (A ∩ B ∩ C) := by
    ext x
    simp [Finset.mem_inter, and_left_comm]
  have hUnionAB_C :
      (unionCard A B C : ℤ) + ((((A ∪ B) ∩ C).card : Nat) : ℤ) =
        (((A ∪ B).card : Nat) : ℤ) + ((C.card : Nat) : ℤ) := by
    exact_mod_cast
      (show unionCard A B C + ((A ∪ B) ∩ C).card = (A ∪ B).card + C.card by
        simpa [unionCard, Finset.union_assoc] using
          Finset.card_union_add_card_inter (A ∪ B) C)
  have hUnionAB :
      (((A ∪ B).card : Nat) : ℤ) + (((A ∩ B).card : Nat) : ℤ) =
        ((A.card : Nat) : ℤ) + ((B.card : Nat) : ℤ) := by
    exact_mod_cast (Finset.card_union_add_card_inter A B)
  have hDecomp :
      ((((A ∪ B) ∩ C).card : Nat) : ℤ) + ((((A ∩ B ∩ C).card : Nat) : ℤ)) =
        (((A ∩ C).card : Nat) : ℤ) + (((B ∩ C).card : Nat) : ℤ) := by
    have h : ((A ∩ C) ∪ (B ∩ C)).card + ((A ∩ C) ∩ (B ∩ C)).card
        = (A ∩ C).card + (B ∩ C).card :=
      Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
    have hNat : ((A ∪ B) ∩ C).card + (A ∩ B ∩ C).card
        = (A ∩ C).card + (B ∩ C).card := by
      simpa [hUnionInter, hTripleInter] using h
    exact_mod_cast
      hNat
  set u : ℤ := (unionCard A B C : ℤ)
  set x : ℤ := ((((A ∪ B) ∩ C).card : Nat) : ℤ)
  set abU : ℤ := (((A ∪ B).card : Nat) : ℤ)
  set c : ℤ := ((C.card : Nat) : ℤ)
  set ab : ℤ := (((A ∩ B).card : Nat) : ℤ)
  set a : ℤ := ((A.card : Nat) : ℤ)
  set b : ℤ := ((B.card : Nat) : ℤ)
  set t : ℤ := ((((A ∩ B ∩ C).card : Nat) : ℤ))
  set ac : ℤ := (((A ∩ C).card : Nat) : ℤ)
  set bc : ℤ := (((B ∩ C).card : ℤ))
  have h1 : u + x = abU + c := by simpa [u, x, abU, c] using hUnionAB_C
  have h2 : abU + ab = a + b := by simpa [abU, ab, a, b] using hUnionAB
  have h3 : x + t = ac + bc := by simpa [x, t, ac, bc] using hDecomp
  have hGoal : u = (a + b + c) - (ab + ac + bc) + t := by
    linarith
  have hTerm1 : (ieTerm1 A B C : ℤ) = a + b + c := by
    simp [ieTerm1, a, b, c, add_assoc, add_left_comm, add_comm]
  have hTerm2 : (ieTerm2 A B C : ℤ) = ab + ac + bc := by
    simp [ieTerm2, ab, ac, bc, add_assoc]
  calc
    (unionCard A B C : ℤ) = u := by simp [u]
    _ = (a + b + c) - (ab + ac + bc) + t := hGoal
    _ = (ieTerm1 A B C : ℤ) - (ieTerm2 A B C : ℤ) + ((A ∩ B ∩ C).card : ℤ) := by
      simp [hTerm1, hTerm2, t]
    _ = twoTermEstimateZ A B C + residualZ A B C := by
      simp [twoTermEstimateZ, residualZ]

/-- Assumption-indexed residual correction: index `i` supplies correction `ξ i`. -/
def ResidualAssumption {I : Type*} (ξ : I → ℤ) (i : I)
    (A B C : Finset α) : Prop :=
  ξ i = residualZ A B C

/-- Assumption-indexed agreement endpoint:
if the indexed correction equals the residual, corrected estimate matches exact union. -/
theorem correctedEstimate_agrees_of_residualAssumption
    {I : Type*} (ξ : I → ℤ) (i : I) (A B C : Finset α)
    (hξ : ResidualAssumption ξ i A B C) :
    (unionCard A B C : ℤ) = correctedEstimateZ (ξ i) A B C := by
  have hExact := unionCard_eq_twoTerm_plus_residualZ (A := A) (B := B) (C := C)
  have hξ' : residualZ A B C = ξ i := by
    simpa [ResidualAssumption] using hξ.symm
  simpa [correctedEstimateZ, hξ'] using hExact

/-- A simple repeated-deduction+revision-style corrected estimator wrapper. -/
def repeatedDeductionRevisionEstimateZ {I : Type*}
    (ξ : I → ℤ) (i : I) (A B C : Finset α) : ℤ :=
  correctedEstimateZ (ξ i) A B C

/-- Agreement theorem for the repeated-deduction+revision wrapper under the indexed
residual assumption. -/
theorem repeatedDeductionRevision_agrees_of_residualAssumption
    {I : Type*} (ξ : I → ℤ) (i : I) (A B C : Finset α)
    (hξ : ResidualAssumption ξ i A B C) :
    (unionCard A B C : ℤ) = repeatedDeductionRevisionEstimateZ ξ i A B C := by
  simpa [repeatedDeductionRevisionEstimateZ] using
    correctedEstimate_agrees_of_residualAssumption (ξ := ξ) (i := i) (A := A) (B := B) (C := C) hξ

/-! ## Indexed n-way residual decomposition -/

/-- Union cardinality of an indexed finite family of events. -/
def unionCardN (n : Nat) (E : Fin n → Finset α) : Nat :=
  (Finset.univ.biUnion E).card

/-- First IE term for an indexed family: sum of singleton masses. -/
def ieTerm1N (n : Nat) (E : Fin n → Finset α) : Nat :=
  Finset.univ.sum (fun i => (E i).card)

/-- Upper-triangular index pairs `(i,j)` with `i < j`. -/
def pairIndexSet (n : Nat) : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter (fun ij => ij.1 < ij.2)

/-- Second IE term for an indexed family: sum over pairwise intersections. -/
def ieTerm2N (n : Nat) (E : Fin n → Finset α) : Nat :=
  (pairIndexSet n).sum (fun ij => ((E ij.1 ∩ E ij.2).card))

/-- Two-term estimate for indexed families, in `ℤ`. -/
def twoTermEstimateNZ (n : Nat) (E : Fin n → Finset α) : ℤ :=
  (ieTerm1N n E : ℤ) - (ieTerm2N n E : ℤ)

/-- Residual/error term for indexed families:
exact union mass minus two-term estimate. -/
def residualNZ (n : Nat) (E : Fin n → Finset α) : ℤ :=
  (unionCardN n E : ℤ) - twoTermEstimateNZ n E

/-- Corrected indexed-family estimate with explicit correction `ξ`. -/
def correctedEstimateNZ (ξ : ℤ) (n : Nat) (E : Fin n → Finset α) : ℤ :=
  twoTermEstimateNZ n E + ξ

theorem unionCardN_eq_twoTerm_plus_residualNZ (n : Nat) (E : Fin n → Finset α) :
    (unionCardN n E : ℤ) = twoTermEstimateNZ n E + residualNZ n E := by
  unfold residualNZ
  linarith

/-- Indexed residual assumption: correction index `i` supplies the residual. -/
def ResidualAssumptionN {I : Type*} (ξ : I → ℤ) (i : I)
    (n : Nat) (E : Fin n → Finset α) : Prop :=
  ξ i = residualNZ n E

theorem correctedEstimateN_agrees_of_residualAssumptionN
    {I : Type*} (ξ : I → ℤ) (i : I) (n : Nat) (E : Fin n → Finset α)
    (hξ : ResidualAssumptionN ξ i n E) :
    (unionCardN n E : ℤ) = correctedEstimateNZ (ξ i) n E := by
  have hExact := unionCardN_eq_twoTerm_plus_residualNZ (n := n) (E := E)
  have hξ' : residualNZ n E = ξ i := by
    simpa [ResidualAssumptionN] using hξ.symm
  simpa [correctedEstimateNZ, hξ'] using hExact

/-- Repeated deduction+revision wrapper for indexed families. -/
def repeatedDeductionRevisionEstimateNZ {I : Type*}
    (ξ : I → ℤ) (i : I) (n : Nat) (E : Fin n → Finset α) : ℤ :=
  correctedEstimateNZ (ξ i) n E

theorem repeatedDeductionRevisionN_agrees_of_residualAssumptionN
    {I : Type*} (ξ : I → ℤ) (i : I) (n : Nat) (E : Fin n → Finset α)
    (hξ : ResidualAssumptionN ξ i n E) :
    (unionCardN n E : ℤ) = repeatedDeductionRevisionEstimateNZ ξ i n E := by
  simpa [repeatedDeductionRevisionEstimateNZ] using
    correctedEstimateN_agrees_of_residualAssumptionN (ξ := ξ) (i := i) (n := n) (E := E) hξ

/-! ## Preservation of no-universal-`ξ` behavior (constant correction) -/

open scoped Classical

theorem no_universal_constant_correction :
    ¬ ∃ ξ : ℤ,
        ∀ A B C : Finset Omega,
          (unionCard A B C : ℤ) = correctedEstimateZ ξ A B C := by
  intro h
  rcases h with ⟨ξ, hξ⟩
  have h1 := hξ A1 B1 C1
  have h2 := hξ A2 B2 C2
  rcases first_model_values with ⟨hT11, hT21, _, hU1Nat⟩
  rcases second_model_values with ⟨hT12, hT22, _, hU2Nat⟩
  have hA1 : correctedEstimateZ ξ A1 B1 C1 = 3 + ξ := by
    unfold correctedEstimateZ twoTermEstimateZ
    simp [hT11, hT21]
  have hA2 : correctedEstimateZ ξ A2 B2 C2 = 3 + ξ := by
    unfold correctedEstimateZ twoTermEstimateZ
    simp [hT12, hT22]
  have hU1 : (unionCard A1 B1 C1 : ℤ) = 4 := by
    exact_mod_cast hU1Nat
  have hU2 : (unionCard A2 B2 C2 : ℤ) = 3 := by
    exact_mod_cast hU2Nat
  have hEq1 : (4 : ℤ) = 3 + ξ := by
    simpa [hU1, hA1] using h1
  have hEq2 : (3 : ℤ) = 3 + ξ := by
    simpa [hU2, hA2] using h2
  linarith

theorem no_single_additive_correction_for_both_models_preserved :
    ¬ ∃ xi : Nat,
        unionCard A1 B1 C1 = ieTwoTermApprox A1 B1 C1 + xi
          ∧ unionCard A2 B2 C2 = ieTwoTermApprox A2 B2 C2 + xi :=
  no_single_additive_correction_for_both_models

end Mettapedia.Logic.PLNMultideductionResidual
