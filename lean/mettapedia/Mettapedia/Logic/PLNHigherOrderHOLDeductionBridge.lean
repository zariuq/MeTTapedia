import Mettapedia.Logic.PLNHigherOrderHOLCredalBridge
import Mettapedia.Logic.PLNDeductionITVBridge
import Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge

/-!
# Higher-Order HOL Deduction Bridge

This file connects the higher-order ProbHOL strength surface to the
no-independence PLN deduction interval.  It does not introduce another
deduction semantics: the traditional point formula is transported through the
five HOL premise strengths, then checked against the full admissible-allocation
interval from `PLNDeductionITVBridge`.
-/

namespace Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Probabilistic
open Mettapedia.Logic.PLNHigherOrderHOLCredalBridge
open Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge
open Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge
open Mettapedia.Logic.PLNFirstOrder

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

/-- View the point PLN deduction formula as a five-input finite rule.

The coordinates are, in order:
`P(A)`, `P(B)`, `P(C)`, `P(B | A)`, and `P(C | B)`.
The output is still the traditional point formula; the interval theorem below
records when this point is admitted by the full no-independence credal envelope.
-/
noncomputable def deductionAsFinite5 (xs : Fin 5 → ℝ) : ℝ :=
  Mettapedia.Logic.PLNDeduction.simpleDeductionStrengthFormula
    (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)

@[simp] theorem deductionAsFinite5_eq
    (xs : Fin 5 → ℝ) :
    deductionAsFinite5 xs =
      Mettapedia.Logic.PLNDeduction.simpleDeductionStrengthFormula
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) :=
  rfl

/-- The five-input point deduction rule is contained in the normalized
full-allocation deduction interval whenever its branch allocation is
admissible.

This is the generic finite-rule seam used by higher-order consumers.  It reuses
the interval theorem from `PLNDeductionITVBridge`; it does not assume
conditional independence for free and it does not claim monotonicity of the
point deduction formula on the whole unit cube. -/
theorem deductionAsFinite5_mem_normalized_allocationJointTypedITV
    (xs : Fin 5 → ℝ)
    (hpA : 0 < xs 0)
    (hpB_small : xs 1 ≤ 0.99)
    (hFeas :
      Mettapedia.Logic.PLNDeduction.DeductionBranchFeasibility
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4))
    (h_consist :
      Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency
          (xs 0) (xs 1) (xs 3) ∧
        Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency
          (xs 1) (xs 2) (xs 4))
    (ht_lower :
      Mettapedia.Logic.PLNDeduction.deductionBBranchLower
          (xs 0) (xs 1) (xs 3) (xs 4) ≤
        (xs 0) * (xs 3) * (xs 4))
    (ht_upper :
      (xs 0) * (xs 3) * (xs 4) ≤
        Mettapedia.Logic.PLNDeduction.deductionBBranchUpper
          (xs 0) (xs 1) (xs 3) (xs 4))
    (hu_lower :
      Mettapedia.Logic.PLNDeduction.deductionNotBBranchLower
          (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) ≤
        (xs 0) * (1 - xs 3) *
          Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal
            (xs 1) (xs 2) (xs 4))
    (hu_upper :
      (xs 0) * (1 - xs 3) *
          Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal
            (xs 1) (xs 2) (xs 4) ≤
        Mettapedia.Logic.PLNDeduction.deductionNotBBranchUpper
          (xs 0) (xs 1) (xs 2) (xs 3) (xs 4))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let joint :=
      Mettapedia.Logic.PLNDeduction.deductionAllocationJointTypedITV
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) hFeas credibility hc
    joint.lower / (xs 0) ≤ deductionAsFinite5 xs ∧
      deductionAsFinite5 xs ≤ joint.upper / (xs 0) := by
  simpa [deductionAsFinite5] using
    Mettapedia.Logic.PLNDeduction.simpleDeductionStrengthFormula_mem_normalized_allocationJointTypedITV
      (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)
      hpA hpB_small hFeas h_consist
      ht_lower ht_upper hu_lower hu_upper credibility hc

/-- Bundle the admissibility side conditions for a five-coordinate PLN
deduction input.

This wrapper keeps later HO consumers from reproving or restating the
first-order no-independence side conditions.  It is only a packaging of the
same hypotheses used by `deductionAsFinite5_mem_normalized_allocationJointTypedITV`;
it does not add a new deduction semantics. -/
structure DeductionCoordinateAdmissibility (xs : Fin 5 → ℝ) : Prop where
  hpA : 0 < xs 0
  hpB_small : xs 1 ≤ 0.99
  hFeas :
    Mettapedia.Logic.PLNDeduction.DeductionBranchFeasibility
      (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)
  h_consist :
    Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency
        (xs 0) (xs 1) (xs 3) ∧
      Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency
        (xs 1) (xs 2) (xs 4)
  ht_lower :
    Mettapedia.Logic.PLNDeduction.deductionBBranchLower
        (xs 0) (xs 1) (xs 3) (xs 4) ≤
      (xs 0) * (xs 3) * (xs 4)
  ht_upper :
    (xs 0) * (xs 3) * (xs 4) ≤
      Mettapedia.Logic.PLNDeduction.deductionBBranchUpper
        (xs 0) (xs 1) (xs 3) (xs 4)
  hu_lower :
    Mettapedia.Logic.PLNDeduction.deductionNotBBranchLower
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) ≤
      (xs 0) * (1 - xs 3) *
        Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal
          (xs 1) (xs 2) (xs 4)
  hu_upper :
    (xs 0) * (1 - xs 3) *
        Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal
          (xs 1) (xs 2) (xs 4) ≤
      Mettapedia.Logic.PLNDeduction.deductionNotBBranchUpper
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)

/-- Packaged form of the generic deduction-interval theorem. -/
theorem deductionAsFinite5_mem_normalized_allocationJointTypedITV_of_admissible
    (xs : Fin 5 → ℝ)
    (h : DeductionCoordinateAdmissibility xs)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let joint :=
      Mettapedia.Logic.PLNDeduction.deductionAllocationJointTypedITV
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) h.hFeas credibility hc
    joint.lower / (xs 0) ≤ deductionAsFinite5 xs ∧
      deductionAsFinite5 xs ≤ joint.upper / (xs 0) :=
  deductionAsFinite5_mem_normalized_allocationJointTypedITV
    xs h.hpA h.hpB_small h.hFeas h.h_consist
    h.ht_lower h.ht_upper h.hu_lower h.hu_upper credibility hc

/-- Apply the five-input point deduction formula to HOL formula strengths inside
one hierarchical state. -/
noncomputable def credalHOLFormulaDeductionPointValue
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin 5 → ClosedFormula Const) : ℝ :=
  deductionAsFinite5 (fun j => credalHOLFormulaValue H (φ j))

@[simp] theorem credalHOLFormulaDeductionPointValue_eq
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin 5 → ClosedFormula Const) :
    credalHOLFormulaDeductionPointValue H φ =
      Mettapedia.Logic.PLNDeduction.simpleDeductionStrengthFormula
        (credalHOLFormulaValue H (φ 0))
        (credalHOLFormulaValue H (φ 1))
        (credalHOLFormulaValue H (φ 2))
        (credalHOLFormulaValue H (φ 3))
        (credalHOLFormulaValue H (φ 4)) :=
  rfl

/-- Same-completion HOL deduction transport: the point deduction value computed
from five HOL formula strengths is inside the full admissible-allocation
deduction interval under the same explicit admissibility hypotheses as the
first-order interval theorem.

This is the higher-order consumer seam for Jewel-1: HOL supplies the five
strength coordinates, while `PLNDeductionITVBridge` supplies the honest
no-independence credal interval. -/
theorem credalHOLFormulaDeductionPointValue_mem_normalized_allocationJointTypedITV
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin 5 → ClosedFormula Const)
    (hpA : 0 < credalHOLFormulaValue H (φ 0))
    (hpB_small : credalHOLFormulaValue H (φ 1) ≤ 0.99)
    (hFeas :
      Mettapedia.Logic.PLNDeduction.DeductionBranchFeasibility
        (credalHOLFormulaValue H (φ 0))
        (credalHOLFormulaValue H (φ 1))
        (credalHOLFormulaValue H (φ 2))
        (credalHOLFormulaValue H (φ 3))
        (credalHOLFormulaValue H (φ 4)))
    (h_consist :
      Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency
          (credalHOLFormulaValue H (φ 0))
          (credalHOLFormulaValue H (φ 1))
          (credalHOLFormulaValue H (φ 3)) ∧
        Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency
          (credalHOLFormulaValue H (φ 1))
          (credalHOLFormulaValue H (φ 2))
          (credalHOLFormulaValue H (φ 4)))
    (ht_lower :
      Mettapedia.Logic.PLNDeduction.deductionBBranchLower
          (credalHOLFormulaValue H (φ 0))
          (credalHOLFormulaValue H (φ 1))
          (credalHOLFormulaValue H (φ 3))
          (credalHOLFormulaValue H (φ 4)) ≤
        (credalHOLFormulaValue H (φ 0)) *
          (credalHOLFormulaValue H (φ 3)) *
          (credalHOLFormulaValue H (φ 4)))
    (ht_upper :
      (credalHOLFormulaValue H (φ 0)) *
          (credalHOLFormulaValue H (φ 3)) *
          (credalHOLFormulaValue H (φ 4)) ≤
        Mettapedia.Logic.PLNDeduction.deductionBBranchUpper
          (credalHOLFormulaValue H (φ 0))
          (credalHOLFormulaValue H (φ 1))
          (credalHOLFormulaValue H (φ 3))
          (credalHOLFormulaValue H (φ 4)))
    (hu_lower :
      Mettapedia.Logic.PLNDeduction.deductionNotBBranchLower
          (credalHOLFormulaValue H (φ 0))
          (credalHOLFormulaValue H (φ 1))
          (credalHOLFormulaValue H (φ 2))
          (credalHOLFormulaValue H (φ 3))
          (credalHOLFormulaValue H (φ 4)) ≤
        (credalHOLFormulaValue H (φ 0)) *
          (1 - credalHOLFormulaValue H (φ 3)) *
          Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal
            (credalHOLFormulaValue H (φ 1))
            (credalHOLFormulaValue H (φ 2))
            (credalHOLFormulaValue H (φ 4)))
    (hu_upper :
      (credalHOLFormulaValue H (φ 0)) *
          (1 - credalHOLFormulaValue H (φ 3)) *
          Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal
            (credalHOLFormulaValue H (φ 1))
            (credalHOLFormulaValue H (φ 2))
            (credalHOLFormulaValue H (φ 4)) ≤
        Mettapedia.Logic.PLNDeduction.deductionNotBBranchUpper
          (credalHOLFormulaValue H (φ 0))
          (credalHOLFormulaValue H (φ 1))
          (credalHOLFormulaValue H (φ 2))
          (credalHOLFormulaValue H (φ 3))
          (credalHOLFormulaValue H (φ 4)))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let joint :=
      Mettapedia.Logic.PLNDeduction.deductionAllocationJointTypedITV
        (credalHOLFormulaValue H (φ 0))
        (credalHOLFormulaValue H (φ 1))
        (credalHOLFormulaValue H (φ 2))
        (credalHOLFormulaValue H (φ 3))
        (credalHOLFormulaValue H (φ 4))
        hFeas credibility hc
    joint.lower / (credalHOLFormulaValue H (φ 0)) ≤
        credalHOLFormulaDeductionPointValue H φ ∧
      credalHOLFormulaDeductionPointValue H φ ≤
        joint.upper / (credalHOLFormulaValue H (φ 0)) := by
  simpa [credalHOLFormulaDeductionPointValue] using
    deductionAsFinite5_mem_normalized_allocationJointTypedITV
      (fun j => credalHOLFormulaValue H (φ j))
      hpA hpB_small hFeas h_consist
      ht_lower ht_upper hu_lower hu_upper credibility hc

/-! ## ProbHOL predicate-sentence consumers -/

/-- Five Kyburg-flattened predicate-implication sentence strengths used as PLN
deduction coordinates inside one hierarchical state.

Each coordinate is the precise ProbHOL readout of the closed HOL sentence
`∀ x, p x -> q x`.  This is the generic probabilistic predicate seam below
the planner/benchmark layer: planners may later package these coordinates, but
the deduction consumer itself only depends on the shared ProbHOL formula value.
-/
noncomputable def hierarchicalPredicateImplicationDeductionCoordinates
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ) :
    Fin 5 → ℝ :=
  fun j =>
    credalHOLFormulaValue H
      (predicateImpFormula (Base := Base) (Const := Const) σ
        (links j).1 (links j).2)

theorem hierarchicalPredicateImplicationDeductionCoordinates_nonneg
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ)
    (j : Fin 5) :
    0 ≤ hierarchicalPredicateImplicationDeductionCoordinates
      (Base := Base) (Const := Const) H σ links j :=
  credalHOLFormulaValue_nonneg
    (Base := Base) (Const := Const) H
    (predicateImpFormula (Base := Base) (Const := Const) σ
      (links j).1 (links j).2)

theorem hierarchicalPredicateImplicationDeductionCoordinates_le_one
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ)
    (j : Fin 5) :
    hierarchicalPredicateImplicationDeductionCoordinates
      (Base := Base) (Const := Const) H σ links j ≤ 1 :=
  credalHOLFormulaValue_le_one
    (Base := Base) (Const := Const) H
    (predicateImpFormula (Base := Base) (Const := Const) σ
      (links j).1 (links j).2)

/-- Point PLN deduction value computed from five flattened predicate-implication
sentence strengths. -/
noncomputable def hierarchicalPredicateImplicationDeductionPointValue
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ) : ℝ :=
  deductionAsFinite5
    (hierarchicalPredicateImplicationDeductionCoordinates
      (Base := Base) (Const := Const) H σ links)

@[simp] theorem hierarchicalPredicateImplicationDeductionPointValue_eq
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ) :
    hierarchicalPredicateImplicationDeductionPointValue
      (Base := Base) (Const := Const) H σ links =
      deductionAsFinite5
        (hierarchicalPredicateImplicationDeductionCoordinates
          (Base := Base) (Const := Const) H σ links) :=
  rfl

/-- Same-hierarchical-state predicate-implication deduction transport into the
full no-independence interval.

This theorem is intentionally only a transport theorem: the predicate
implication coordinates come from ProbHOL/Kyburg-flattened HOL sentences, and
the interval is the existing full admissible-allocation deduction interval.
It does not introduce a planner-specific deduction semantics. -/
theorem hierarchicalPredicateImplicationDeductionPointValue_mem_normalized_allocationJointTypedITV
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ)
    (h :
      DeductionCoordinateAdmissibility
        (hierarchicalPredicateImplicationDeductionCoordinates
          (Base := Base) (Const := Const) H σ links))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let xs :=
      hierarchicalPredicateImplicationDeductionCoordinates
        (Base := Base) (Const := Const) H σ links
    let joint :=
      Mettapedia.Logic.PLNDeduction.deductionAllocationJointTypedITV
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) h.hFeas credibility hc
    joint.lower / (xs 0) ≤
        hierarchicalPredicateImplicationDeductionPointValue
          (Base := Base) (Const := Const) H σ links ∧
      hierarchicalPredicateImplicationDeductionPointValue
          (Base := Base) (Const := Const) H σ links ≤
        joint.upper / (xs 0) := by
  simpa [hierarchicalPredicateImplicationDeductionPointValue] using
    deductionAsFinite5_mem_normalized_allocationJointTypedITV_of_admissible
      (hierarchicalPredicateImplicationDeductionCoordinates
        (Base := Base) (Const := Const) H σ links)
      h credibility hc

/-- Five Kyburg-flattened predicate-equivalence sentence strengths used as PLN
deduction coordinates inside one hierarchical state.

These coordinates are the probabilistic sibling of predicate similarity:
`predicateIffFormula` is the closed HOL sentence expressing mutual inheritance.
-/
noncomputable def hierarchicalPredicateSimilarityDeductionCoordinates
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ) :
    Fin 5 → ℝ :=
  fun j =>
    credalHOLFormulaValue H
      (predicateIffFormula (Base := Base) (Const := Const) σ
        (links j).1 (links j).2)

theorem hierarchicalPredicateSimilarityDeductionCoordinates_nonneg
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ)
    (j : Fin 5) :
    0 ≤ hierarchicalPredicateSimilarityDeductionCoordinates
      (Base := Base) (Const := Const) H σ links j :=
  credalHOLFormulaValue_nonneg
    (Base := Base) (Const := Const) H
    (predicateIffFormula (Base := Base) (Const := Const) σ
      (links j).1 (links j).2)

theorem hierarchicalPredicateSimilarityDeductionCoordinates_le_one
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ)
    (j : Fin 5) :
    hierarchicalPredicateSimilarityDeductionCoordinates
      (Base := Base) (Const := Const) H σ links j ≤ 1 :=
  credalHOLFormulaValue_le_one
    (Base := Base) (Const := Const) H
    (predicateIffFormula (Base := Base) (Const := Const) σ
      (links j).1 (links j).2)

/-- Point PLN deduction value computed from five flattened predicate-equivalence
sentence strengths. -/
noncomputable def hierarchicalPredicateSimilarityDeductionPointValue
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ) : ℝ :=
  deductionAsFinite5
    (hierarchicalPredicateSimilarityDeductionCoordinates
      (Base := Base) (Const := Const) H σ links)

@[simp] theorem hierarchicalPredicateSimilarityDeductionPointValue_eq
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ) :
    hierarchicalPredicateSimilarityDeductionPointValue
      (Base := Base) (Const := Const) H σ links =
      deductionAsFinite5
        (hierarchicalPredicateSimilarityDeductionCoordinates
          (Base := Base) (Const := Const) H σ links) :=
  rfl

/-- Same-hierarchical-state predicate-similarity deduction transport into the
full no-independence interval.

The similarity coordinates are read as closed HOL equivalence sentences through
ProbHOL/Kyburg flattening, then consumed by the already-proven deduction
interval. -/
theorem hierarchicalPredicateSimilarityDeductionPointValue_mem_normalized_allocationJointTypedITV
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (links :
      Fin 5 →
        UnaryPredicate (Base := Base) (Const := Const) σ ×
          UnaryPredicate (Base := Base) (Const := Const) σ)
    (h :
      DeductionCoordinateAdmissibility
        (hierarchicalPredicateSimilarityDeductionCoordinates
          (Base := Base) (Const := Const) H σ links))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let xs :=
      hierarchicalPredicateSimilarityDeductionCoordinates
        (Base := Base) (Const := Const) H σ links
    let joint :=
      Mettapedia.Logic.PLNDeduction.deductionAllocationJointTypedITV
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) h.hFeas credibility hc
    joint.lower / (xs 0) ≤
        hierarchicalPredicateSimilarityDeductionPointValue
          (Base := Base) (Const := Const) H σ links ∧
      hierarchicalPredicateSimilarityDeductionPointValue
          (Base := Base) (Const := Const) H σ links ≤
        joint.upper / (xs 0) := by
  simpa [hierarchicalPredicateSimilarityDeductionPointValue] using
    deductionAsFinite5_mem_normalized_allocationJointTypedITV_of_admissible
      (hierarchicalPredicateSimilarityDeductionCoordinates
        (Base := Base) (Const := Const) H σ links)
      h credibility hc

/-! ## Predicate inheritance / similarity consumers -/

/-- Five finite-vocabulary predicate-inheritance strengths used as PLN
deduction coordinates.

Each coordinate is an existing full extensional/intensional inheritance
strength between two vocabulary predicates. -/
noncomputable def predicateVocabularyFullInheritanceDeductionCoordinates
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred) : Fin 5 → ℝ :=
  fun j =>
    predicateVocabularyFullInheritanceStrength
      (Base := Base) (Const := Const) M σ decode
      (links j).1 (links j).2

theorem predicateVocabularyFullInheritanceDeductionCoordinates_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred) (j : Fin 5) :
    0 ≤ predicateVocabularyFullInheritanceDeductionCoordinates
      (Base := Base) (Const := Const) M σ decode links j :=
  predicateVocabularyFullInheritanceStrength_nonneg
    (Base := Base) (Const := Const) M σ decode
    (links j).1 (links j).2

theorem predicateVocabularyFullInheritanceDeductionCoordinates_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred) (j : Fin 5) :
    predicateVocabularyFullInheritanceDeductionCoordinates
      (Base := Base) (Const := Const) M σ decode links j ≤ 1 :=
  predicateVocabularyFullInheritanceStrength_le_one
    (Base := Base) (Const := Const) M σ decode
    (links j).1 (links j).2

/-- Point PLN deduction value computed from five existing full-inheritance
strengths on a finite predicate vocabulary. -/
noncomputable def predicateVocabularyFullInheritanceDeductionPointValue
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred) : ℝ :=
  deductionAsFinite5
    (predicateVocabularyFullInheritanceDeductionCoordinates
      (Base := Base) (Const := Const) M σ decode links)

@[simp] theorem predicateVocabularyFullInheritanceDeductionPointValue_eq
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred) :
    predicateVocabularyFullInheritanceDeductionPointValue
      (Base := Base) (Const := Const) M σ decode links =
      deductionAsFinite5
        (predicateVocabularyFullInheritanceDeductionCoordinates
          (Base := Base) (Const := Const) M σ decode links) :=
  rfl

/-- Finite-vocabulary full-inheritance deduction transport into the
no-independence interval.

This is the systems-facing predicate-inheritance consumer: the coordinates
come from the shared extensional/intensional inheritance machinery, and the
interval is the already-proved full admissible-allocation deduction interval. -/
theorem predicateVocabularyFullInheritanceDeductionPointValue_mem_normalized_allocationJointTypedITV
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred)
    (h :
      DeductionCoordinateAdmissibility
        (predicateVocabularyFullInheritanceDeductionCoordinates
          (Base := Base) (Const := Const) M σ decode links))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let xs :=
      predicateVocabularyFullInheritanceDeductionCoordinates
        (Base := Base) (Const := Const) M σ decode links
    let joint :=
      Mettapedia.Logic.PLNDeduction.deductionAllocationJointTypedITV
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) h.hFeas credibility hc
    joint.lower / (xs 0) ≤
        predicateVocabularyFullInheritanceDeductionPointValue
          (Base := Base) (Const := Const) M σ decode links ∧
      predicateVocabularyFullInheritanceDeductionPointValue
          (Base := Base) (Const := Const) M σ decode links ≤
        joint.upper / (xs 0) := by
  simpa [predicateVocabularyFullInheritanceDeductionPointValue] using
    deductionAsFinite5_mem_normalized_allocationJointTypedITV_of_admissible
      (predicateVocabularyFullInheritanceDeductionCoordinates
        (Base := Base) (Const := Const) M σ decode links)
      h credibility hc

/-- Five finite-vocabulary predicate-similarity strengths used as PLN
deduction coordinates. -/
noncomputable def predicateVocabularySimilarityDeductionCoordinates
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred) : Fin 5 → ℝ :=
  fun j =>
    predicateVocabularySimilarityStrength
      (Base := Base) (Const := Const) M σ decode
      (links j).1 (links j).2

theorem predicateVocabularySimilarityDeductionCoordinates_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred) (j : Fin 5) :
    0 ≤ predicateVocabularySimilarityDeductionCoordinates
      (Base := Base) (Const := Const) M σ decode links j :=
  predicateVocabularySimilarityStrength_nonneg
    (Base := Base) (Const := Const) M σ decode
    (links j).1 (links j).2

theorem predicateVocabularySimilarityDeductionCoordinates_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred) (j : Fin 5) :
    predicateVocabularySimilarityDeductionCoordinates
      (Base := Base) (Const := Const) M σ decode links j ≤ 1 :=
  predicateVocabularySimilarityStrength_le_one
    (Base := Base) (Const := Const) M σ decode
    (links j).1 (links j).2

/-- Point PLN deduction value computed from five existing finite-vocabulary
similarity strengths. -/
noncomputable def predicateVocabularySimilarityDeductionPointValue
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred) : ℝ :=
  deductionAsFinite5
    (predicateVocabularySimilarityDeductionCoordinates
      (Base := Base) (Const := Const) M σ decode links)

@[simp] theorem predicateVocabularySimilarityDeductionPointValue_eq
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred) :
    predicateVocabularySimilarityDeductionPointValue
      (Base := Base) (Const := Const) M σ decode links =
      deductionAsFinite5
        (predicateVocabularySimilarityDeductionCoordinates
          (Base := Base) (Const := Const) M σ decode links) :=
  rfl

/-- Finite-vocabulary similarity deduction transport into the no-independence
interval.

The similarity coordinates are themselves built by the existing `2inh2sim`
consumer over full predicate inheritance, so this theorem remains a transport
layer over established WM-PLN machinery rather than a new similarity calculus. -/
theorem predicateVocabularySimilarityDeductionPointValue_mem_normalized_allocationJointTypedITV
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (links : Fin 5 → Pred × Pred)
    (h :
      DeductionCoordinateAdmissibility
        (predicateVocabularySimilarityDeductionCoordinates
          (Base := Base) (Const := Const) M σ decode links))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let xs :=
      predicateVocabularySimilarityDeductionCoordinates
        (Base := Base) (Const := Const) M σ decode links
    let joint :=
      Mettapedia.Logic.PLNDeduction.deductionAllocationJointTypedITV
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) h.hFeas credibility hc
    joint.lower / (xs 0) ≤
        predicateVocabularySimilarityDeductionPointValue
          (Base := Base) (Const := Const) M σ decode links ∧
      predicateVocabularySimilarityDeductionPointValue
          (Base := Base) (Const := Const) M σ decode links ≤
        joint.upper / (xs 0) := by
  simpa [predicateVocabularySimilarityDeductionPointValue] using
    deductionAsFinite5_mem_normalized_allocationJointTypedITV_of_admissible
      (predicateVocabularySimilarityDeductionCoordinates
        (Base := Base) (Const := Const) M σ decode links)
      h credibility hc

/-- Package the five predicate endpoints expected by PLN deduction:
`A`, `B`, `C`, `A -> B`, and `B -> C`.

The endpoint names are intentionally semantic rather than syntactic: the last
two arguments are the predicate-level quantities whose QFM strengths are read
as the directed inheritance/conditional-strength coordinates. -/
def predicateDeductionEndpointQuintuple
    (σ : Ty Base)
    (pA pB pC pAB pBC :
      UnaryPredicate (Base := Base) (Const := Const) σ) :
    Fin 5 → UnaryPredicate (Base := Base) (Const := Const) σ :=
  fun j =>
    if j = 0 then pA else
      if j = 1 then pB else
        if j = 2 then pC else
          if j = 3 then pAB else pBC

/-- Five QFM-universal predicate strengths used as the coordinates for the
point PLN deduction formula. -/
noncomputable def credalPredicateQFMForAllDeductionCoordinates
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (pA pB pC pAB pBC :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) : Fin 5 → ℝ :=
  fun j =>
    credalPredicateQFMForAllCapacityValue
      (Base := Base) (Const := Const) M σ νs
      ((predicateDeductionEndpointQuintuple
        (Base := Base) (Const := Const) σ pA pB pC pAB pBC) j)
      k

/-- Predicate/QFM universal point deduction value for one
capacity/reference-class completion. -/
noncomputable def credalPredicateQFMForAllDeductionPointValue
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (pA pB pC pAB pBC :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) : ℝ :=
  deductionAsFinite5
    (credalPredicateQFMForAllDeductionCoordinates
      (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k)

/-- Predicate/QFM universal deduction transport into the full
admissible-allocation interval.

The theorem is intentionally hypothesis-explicit: it says the QFM endpoint
strengths can be consumed by the no-independence deduction interval when they
meet the same branch-feasibility and consistency conditions as the first-order
deduction theorem. -/
theorem credalPredicateQFMForAllDeductionPointValue_mem_normalized_allocationJointTypedITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (pA pB pC pAB pBC :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ)
    (hpA :
      0 <
        (credalPredicateQFMForAllDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
    (hpB_small :
      (credalPredicateQFMForAllDeductionCoordinates
        (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1 ≤
        0.99)
    (hFeas :
      Mettapedia.Logic.PLNDeduction.DeductionBranchFeasibility
        ((credalPredicateQFMForAllDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
        ((credalPredicateQFMForAllDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
        ((credalPredicateQFMForAllDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
        ((credalPredicateQFMForAllDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3)
        ((credalPredicateQFMForAllDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (h_consist :
      Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3) ∧
        Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (ht_lower :
      Mettapedia.Logic.PLNDeduction.deductionBBranchLower
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4) ≤
        ((credalPredicateQFMForAllDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0) *
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3) *
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (ht_upper :
      ((credalPredicateQFMForAllDeductionCoordinates
        (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0) *
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3) *
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4) ≤
        Mettapedia.Logic.PLNDeduction.deductionBBranchUpper
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (hu_lower :
      Mettapedia.Logic.PLNDeduction.deductionNotBBranchLower
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4) ≤
        ((credalPredicateQFMForAllDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0) *
          (1 - (credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3) *
          Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal
            ((credalPredicateQFMForAllDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
            ((credalPredicateQFMForAllDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
            ((credalPredicateQFMForAllDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (hu_upper :
      ((credalPredicateQFMForAllDeductionCoordinates
        (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0) *
          (1 - (credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3) *
          Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal
            ((credalPredicateQFMForAllDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
            ((credalPredicateQFMForAllDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
            ((credalPredicateQFMForAllDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4) ≤
        Mettapedia.Logic.PLNDeduction.deductionNotBBranchUpper
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3)
          ((credalPredicateQFMForAllDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let xs :=
      credalPredicateQFMForAllDeductionCoordinates
        (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k
    let joint :=
      Mettapedia.Logic.PLNDeduction.deductionAllocationJointTypedITV
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) hFeas credibility hc
    joint.lower / (xs 0) ≤
        credalPredicateQFMForAllDeductionPointValue
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k ∧
      credalPredicateQFMForAllDeductionPointValue
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k ≤
        joint.upper / (xs 0) := by
  simpa [credalPredicateQFMForAllDeductionPointValue] using
    deductionAsFinite5_mem_normalized_allocationJointTypedITV
      (credalPredicateQFMForAllDeductionCoordinates
        (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k)
      hpA hpB_small hFeas h_consist
      ht_lower ht_upper hu_lower hu_upper credibility hc

/-- Five QFM-existential predicate strengths used as the coordinates for the
point PLN deduction formula. -/
noncomputable def credalPredicateQFMThereExistsDeductionCoordinates
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (pA pB pC pAB pBC :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) : Fin 5 → ℝ :=
  fun j =>
    credalPredicateQFMThereExistsCapacityValue
      (Base := Base) (Const := Const) M σ νs
      ((predicateDeductionEndpointQuintuple
        (Base := Base) (Const := Const) σ pA pB pC pAB pBC) j)
      k

/-- Predicate/QFM existential point deduction value for one
capacity/reference-class completion. -/
noncomputable def credalPredicateQFMThereExistsDeductionPointValue
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (pA pB pC pAB pBC :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) : ℝ :=
  deductionAsFinite5
    (credalPredicateQFMThereExistsDeductionCoordinates
      (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k)

/-- Predicate/QFM existential deduction transport into the full
admissible-allocation interval. -/
theorem credalPredicateQFMThereExistsDeductionPointValue_mem_normalized_allocationJointTypedITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (pA pB pC pAB pBC :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ)
    (hpA :
      0 <
        (credalPredicateQFMThereExistsDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
    (hpB_small :
      (credalPredicateQFMThereExistsDeductionCoordinates
        (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1 ≤
        0.99)
    (hFeas :
      Mettapedia.Logic.PLNDeduction.DeductionBranchFeasibility
        ((credalPredicateQFMThereExistsDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
        ((credalPredicateQFMThereExistsDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
        ((credalPredicateQFMThereExistsDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
        ((credalPredicateQFMThereExistsDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3)
        ((credalPredicateQFMThereExistsDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (h_consist :
      Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3) ∧
        Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (ht_lower :
      Mettapedia.Logic.PLNDeduction.deductionBBranchLower
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4) ≤
        ((credalPredicateQFMThereExistsDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0) *
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3) *
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (ht_upper :
      ((credalPredicateQFMThereExistsDeductionCoordinates
        (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0) *
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3) *
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4) ≤
        Mettapedia.Logic.PLNDeduction.deductionBBranchUpper
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (hu_lower :
      Mettapedia.Logic.PLNDeduction.deductionNotBBranchLower
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4) ≤
        ((credalPredicateQFMThereExistsDeductionCoordinates
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0) *
          (1 - (credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3) *
          Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal
            ((credalPredicateQFMThereExistsDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
            ((credalPredicateQFMThereExistsDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
            ((credalPredicateQFMThereExistsDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (hu_upper :
      ((credalPredicateQFMThereExistsDeductionCoordinates
        (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0) *
          (1 - (credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3) *
          Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal
            ((credalPredicateQFMThereExistsDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
            ((credalPredicateQFMThereExistsDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
            ((credalPredicateQFMThereExistsDeductionCoordinates
              (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4) ≤
        Mettapedia.Logic.PLNDeduction.deductionNotBBranchUpper
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 0)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 1)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 2)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 3)
          ((credalPredicateQFMThereExistsDeductionCoordinates
            (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k) 4))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let xs :=
      credalPredicateQFMThereExistsDeductionCoordinates
        (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k
    let joint :=
      Mettapedia.Logic.PLNDeduction.deductionAllocationJointTypedITV
        (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) hFeas credibility hc
    joint.lower / (xs 0) ≤
        credalPredicateQFMThereExistsDeductionPointValue
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k ∧
      credalPredicateQFMThereExistsDeductionPointValue
          (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k ≤
        joint.upper / (xs 0) := by
  simpa [credalPredicateQFMThereExistsDeductionPointValue] using
    deductionAsFinite5_mem_normalized_allocationJointTypedITV
      (credalPredicateQFMThereExistsDeductionCoordinates
        (Base := Base) (Const := Const) M σ νs pA pB pC pAB pBC k)
      hpA hpB_small hFeas h_consist
      ht_lower ht_upper hu_lower hu_upper credibility hc

/-! ## Concrete deduction-interval canaries

These small cases mirror the runnable CeTTa witness
`tests/test_wmpln_deduction_interval_canary.metta`.  They are deliberately
hand-computable: the Lean facts below expose the already-proven Frechet endpoint
machinery through the higher-order five-coordinate seam, rather than asserting
new deduction semantics.
-/

section ConcreteCanaries

open Mettapedia.Logic.PLNDeduction

/-- A collapsed deduction case: the no-independence interval is the point
`[1/2, 1/2]`. -/
noncomputable def collapsedDeductionCanaryCoordinates : Fin 5 → ℝ :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ), (1 : ℝ), (1 / 2 : ℝ)]

/-- An open deduction case: the same marginals leave the conclusion interval
as the full `[0, 1]`. -/
noncomputable def openDeductionCanaryCoordinates : Fin 5 → ℝ :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- An asymmetric no-independence case: the conclusion interval is
`[1/2, 1]`. -/
noncomputable def asymmetricDeductionCanaryCoordinates : Fin 5 → ℝ :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ), (3 / 4 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ)]

theorem collapsedDeductionCanary_feasible :
    DeductionBranchFeasibility
      (collapsedDeductionCanaryCoordinates 0)
      (collapsedDeductionCanaryCoordinates 1)
      (collapsedDeductionCanaryCoordinates 2)
      (collapsedDeductionCanaryCoordinates 3)
      (collapsedDeductionCanaryCoordinates 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [collapsedDeductionCanaryCoordinates, deductionJointAB,
      deductionJointBC]

theorem openDeductionCanary_feasible :
    DeductionBranchFeasibility
      (openDeductionCanaryCoordinates 0)
      (openDeductionCanaryCoordinates 1)
      (openDeductionCanaryCoordinates 2)
      (openDeductionCanaryCoordinates 3)
      (openDeductionCanaryCoordinates 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [openDeductionCanaryCoordinates, deductionJointAB,
      deductionJointBC]

theorem asymmetricDeductionCanary_feasible :
    DeductionBranchFeasibility
      (asymmetricDeductionCanaryCoordinates 0)
      (asymmetricDeductionCanaryCoordinates 1)
      (asymmetricDeductionCanaryCoordinates 2)
      (asymmetricDeductionCanaryCoordinates 3)
      (asymmetricDeductionCanaryCoordinates 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [asymmetricDeductionCanaryCoordinates, deductionJointAB,
      deductionJointBC]

noncomputable def collapsedDeductionCanaryITV :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  deductionCredalStrengthITV
    (collapsedDeductionCanaryCoordinates 0)
    (collapsedDeductionCanaryCoordinates 1)
    (collapsedDeductionCanaryCoordinates 2)
    (collapsedDeductionCanaryCoordinates 3)
    (collapsedDeductionCanaryCoordinates 4)
    (by norm_num [collapsedDeductionCanaryCoordinates])
    collapsedDeductionCanary_feasible
    1
    (by norm_num)

noncomputable def openDeductionCanaryITV :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  deductionCredalStrengthITV
    (openDeductionCanaryCoordinates 0)
    (openDeductionCanaryCoordinates 1)
    (openDeductionCanaryCoordinates 2)
    (openDeductionCanaryCoordinates 3)
    (openDeductionCanaryCoordinates 4)
    (by norm_num [openDeductionCanaryCoordinates])
    openDeductionCanary_feasible
    1
    (by norm_num)

noncomputable def asymmetricDeductionCanaryITV :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  deductionCredalStrengthITV
    (asymmetricDeductionCanaryCoordinates 0)
    (asymmetricDeductionCanaryCoordinates 1)
    (asymmetricDeductionCanaryCoordinates 2)
    (asymmetricDeductionCanaryCoordinates 3)
    (asymmetricDeductionCanaryCoordinates 4)
    (by norm_num [asymmetricDeductionCanaryCoordinates])
    asymmetricDeductionCanary_feasible
    1
    (by norm_num)

theorem collapsedDeductionCanary_pointValue :
    deductionAsFinite5 collapsedDeductionCanaryCoordinates = 1 / 2 := by
  norm_num [deductionAsFinite5, collapsedDeductionCanaryCoordinates,
    simpleDeductionStrengthFormula, conditionalProbabilityConsistency,
    smallestIntersectionProbability, largestIntersectionProbability]

theorem openDeductionCanary_pointValue :
    deductionAsFinite5 openDeductionCanaryCoordinates = 1 / 2 := by
  norm_num [deductionAsFinite5, openDeductionCanaryCoordinates,
    simpleDeductionStrengthFormula, conditionalProbabilityConsistency,
    smallestIntersectionProbability, largestIntersectionProbability]

theorem asymmetricDeductionCanary_pointValue :
    deductionAsFinite5 asymmetricDeductionCanaryCoordinates = 3 / 4 := by
  norm_num [deductionAsFinite5, asymmetricDeductionCanaryCoordinates,
    simpleDeductionStrengthFormula, conditionalProbabilityConsistency,
    smallestIntersectionProbability, largestIntersectionProbability]

theorem collapsedDeductionCanaryITV_lower :
    collapsedDeductionCanaryITV.lower = 1 / 2 := by
  norm_num [collapsedDeductionCanaryITV, collapsedDeductionCanaryCoordinates,
    deductionCredalStrengthITV, deductionCredalStrengthLower,
    deductionCredalJointLower, deductionBBranchLower,
    deductionNotBBranchLower, deductionJointAB, deductionJointBC]

theorem collapsedDeductionCanaryITV_upper :
    collapsedDeductionCanaryITV.upper = 1 / 2 := by
  norm_num [collapsedDeductionCanaryITV, collapsedDeductionCanaryCoordinates,
    deductionCredalStrengthITV, deductionCredalStrengthUpper,
    deductionCredalJointUpper, deductionBBranchUpper,
    deductionNotBBranchUpper, deductionJointAB, deductionJointBC]

theorem collapsedDeductionCanaryITV_width :
    collapsedDeductionCanaryITV.width = 0 := by
  norm_num [Mettapedia.Logic.PLNIndefiniteTruth.ITV.width,
    collapsedDeductionCanaryITV_lower, collapsedDeductionCanaryITV_upper]

theorem openDeductionCanaryITV_lower :
    openDeductionCanaryITV.lower = 0 := by
  norm_num [openDeductionCanaryITV, openDeductionCanaryCoordinates,
    deductionCredalStrengthITV, deductionCredalStrengthLower,
    deductionCredalJointLower, deductionBBranchLower,
    deductionNotBBranchLower, deductionJointAB, deductionJointBC]

theorem openDeductionCanaryITV_upper :
    openDeductionCanaryITV.upper = 1 := by
  norm_num [openDeductionCanaryITV, openDeductionCanaryCoordinates,
    deductionCredalStrengthITV, deductionCredalStrengthUpper,
    deductionCredalJointUpper, deductionBBranchUpper,
    deductionNotBBranchUpper, deductionJointAB, deductionJointBC]

theorem openDeductionCanaryITV_width :
    openDeductionCanaryITV.width = 1 := by
  norm_num [Mettapedia.Logic.PLNIndefiniteTruth.ITV.width,
    openDeductionCanaryITV_lower, openDeductionCanaryITV_upper]

theorem asymmetricDeductionCanaryITV_lower :
    asymmetricDeductionCanaryITV.lower = 1 / 2 := by
  norm_num [asymmetricDeductionCanaryITV, asymmetricDeductionCanaryCoordinates,
    deductionCredalStrengthITV, deductionCredalStrengthLower,
    deductionCredalJointLower, deductionBBranchLower,
    deductionNotBBranchLower, deductionJointAB, deductionJointBC]

theorem asymmetricDeductionCanaryITV_upper :
    asymmetricDeductionCanaryITV.upper = 1 := by
  norm_num [asymmetricDeductionCanaryITV, asymmetricDeductionCanaryCoordinates,
    deductionCredalStrengthITV, deductionCredalStrengthUpper,
    deductionCredalJointUpper, deductionBBranchUpper,
    deductionNotBBranchUpper, deductionJointAB, deductionJointBC]

theorem asymmetricDeductionCanaryITV_width :
    asymmetricDeductionCanaryITV.width = 1 / 2 := by
  norm_num [Mettapedia.Logic.PLNIndefiniteTruth.ITV.width,
    asymmetricDeductionCanaryITV_lower, asymmetricDeductionCanaryITV_upper]

theorem collapsedDeductionCanary_pointValue_mem_itv :
    collapsedDeductionCanaryITV.lower ≤
        deductionAsFinite5 collapsedDeductionCanaryCoordinates ∧
      deductionAsFinite5 collapsedDeductionCanaryCoordinates ≤
        collapsedDeductionCanaryITV.upper := by
  rw [collapsedDeductionCanaryITV_lower, collapsedDeductionCanaryITV_upper,
    collapsedDeductionCanary_pointValue]
  norm_num

theorem openDeductionCanary_pointValue_mem_itv :
    openDeductionCanaryITV.lower ≤
        deductionAsFinite5 openDeductionCanaryCoordinates ∧
      deductionAsFinite5 openDeductionCanaryCoordinates ≤
        openDeductionCanaryITV.upper := by
  rw [openDeductionCanaryITV_lower, openDeductionCanaryITV_upper,
    openDeductionCanary_pointValue]
  norm_num

theorem asymmetricDeductionCanary_pointValue_mem_itv :
    asymmetricDeductionCanaryITV.lower ≤
        deductionAsFinite5 asymmetricDeductionCanaryCoordinates ∧
      deductionAsFinite5 asymmetricDeductionCanaryCoordinates ≤
        asymmetricDeductionCanaryITV.upper := by
  rw [asymmetricDeductionCanaryITV_lower, asymmetricDeductionCanaryITV_upper,
    asymmetricDeductionCanary_pointValue]
  norm_num

end ConcreteCanaries

end Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge
