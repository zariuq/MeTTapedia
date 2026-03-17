import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.HOL.LogicalInduction.Market
import Mettapedia.Logic.HOL.WorldModel

/-!
# Dynamic WM-Facing View of HOL Belief Days

This module provides the thin WM-facing view of a single logical-induction day.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), belief dynamics should be
layered on top of logical syntax and a deductive process, not confused with
semantic truth in Henkin models.

Accordingly:

- `HOL/Semantics/Henkin.lean` remains the truth layer,
- `HOL/WorldModel.lean` remains the static semantic WM lens,
- this file only interprets a *belief day* as WM-facing evidence/strength about
  closed HOL formula codes.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Positive mass contributed by a unit-interval rational price. -/
noncomputable def priceMass (p : Price01) : ℝ≥0∞ :=
  ENNReal.ofReal ((p : Rat) : Real)

/-- Complementary negative mass contributed by a unit-interval rational price. -/
noncomputable def priceComplement (p : Price01) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - ((p : Rat) : Real))

/-- WM-facing evidence extracted from a single belief day about a coded formula. -/
noncomputable def beliefEvidence
    (B : BeliefDay Const)
    (φ : ClosedFormulaCode Const) : BinaryEvidence :=
  ⟨priceMass (B φ), priceComplement (B φ)⟩

/-- WM-facing belief strength for a coded formula on one day. -/
noncomputable def dayQueryStrength
    (B : BeliefDay Const)
    (φ : ClosedFormulaCode Const) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (beliefEvidence (Const := Const) B φ)

theorem beliefEvidence_total_one
    (B : BeliefDay Const)
    (φ : ClosedFormulaCode Const) :
    (beliefEvidence (Const := Const) B φ).total = 1 := by
  have hp0 : 0 ≤ (((B φ : Price01) : Rat) : Real) := by
    exact_mod_cast (B φ).zero_le
  have hp1 : (((B φ : Price01) : Rat) : Real) ≤ 1 := by
    exact_mod_cast (B φ).le_one
  have hcomp : 0 ≤ 1 - (((B φ : Price01) : Rat) : Real) := by
    linarith
  simp [beliefEvidence, BinaryEvidence.total, priceMass, priceComplement]
  rw [← ENNReal.ofReal_add hp0 hcomp]
  ring_nf
  simp

theorem dayQueryStrength_eq_priceMass
    (B : BeliefDay Const)
    (φ : ClosedFormulaCode Const) :
    dayQueryStrength (Const := Const) B φ = priceMass (B φ) := by
  unfold dayQueryStrength BinaryEvidence.toStrength
  rw [beliefEvidence_total_one (Const := Const) B φ]
  simp [beliefEvidence, priceMass]

theorem dayQueryStrength_eq_price
    (B : BeliefDay Const)
    (φ : ClosedFormulaCode Const) :
    dayQueryStrength (Const := Const) B φ =
      ENNReal.ofReal (((B φ : Price01) : Rat) : Real) := by
  simpa [priceMass] using dayQueryStrength_eq_priceMass (Const := Const) B φ

theorem dayQueryStrength_ext
    (B₁ B₂ : BeliefDay Const)
    (φ : ClosedFormulaCode Const)
    (hφ : B₁ φ = B₂ φ) :
    dayQueryStrength (Const := Const) B₁ φ =
      dayQueryStrength (Const := Const) B₂ φ := by
  simp [dayQueryStrength_eq_price, hφ]

/-- The dynamic price layer is extensional in the market day, not in Henkin
model truth. This theorem is intentionally trivial: it marks the architectural
separation between semantic truth and belief dynamics. -/
theorem dayQueryStrength_independent_of_henkin_truth
    (B : BeliefDay Const)
    (φ : ClosedFormulaCode Const)
    (_M _N : HenkinModel Base Const) :
    dayQueryStrength (Const := Const) B φ =
      dayQueryStrength (Const := Const) B φ := rfl

end Mettapedia.Logic.HOL.LogicalInduction
