import Mettapedia.Algorithms.QuantitativeCheckers
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace Mettapedia.Logic.HardBEST

open scoped BigOperators

section Generic

variable {β : Type*}

/-- Generic WR/WOR transport inequality through a surrogate law `q`. -/
lemma sum_abs_wr_wor_patternMass_toReal_le_of_surrogate
    (patternSet : Finset β)
    (wrMass q worMass : β → ℝ)
    (εW εPC : ℝ)
    (hwr_q : ∑ p ∈ patternSet, |wrMass p - q p| ≤ εW)
    (hq_wor : ∑ p ∈ patternSet, |q p - worMass p| ≤ εPC) :
    ∑ p ∈ patternSet, |wrMass p - worMass p| ≤ εW + εPC := by
  have hpoint :
      ∀ p : β,
        |wrMass p - worMass p| ≤ |wrMass p - q p| + |q p - worMass p| := by
    intro p
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (abs_sub_le (wrMass p) (q p) (worMass p))
  calc
    ∑ p ∈ patternSet, |wrMass p - worMass p|
        ≤ ∑ p ∈ patternSet, (|wrMass p - q p| + |q p - worMass p|) := by
          refine Finset.sum_le_sum ?_
          intro p hp
          exact hpoint p
    _ = (∑ p ∈ patternSet, |wrMass p - q p|) +
          (∑ p ∈ patternSet, |q p - worMass p|) := by
            simp [Finset.sum_add_distrib]
    _ ≤ εW + εPC := add_le_add hwr_q hq_wor

/-- HardBEST-specific adapter:
turn a per-pattern rational certificate into the exact surrogate→WOR inequality shape. -/
theorem hq_wor_of_certificate
    (patternSet : Finset β)
    (q worMass : β → ℝ)
    (C : ℚ) (R : ℕ)
    (hcert :
      ∃ f g : β → ℚ,
        (∀ p, p ∈ patternSet → q p = (f p : ℝ)) ∧
        (∀ p, p ∈ patternSet → worMass p = (g p : ℝ)) ∧
        Mettapedia.Algorithms.finiteL1RateChecker patternSet f g C (R : ℚ) = true) :
    (∑ p ∈ patternSet, |q p - worMass p|) ≤ (C : ℝ) / (R : ℝ) := by
  exact Mettapedia.Algorithms.hardBEST_patternRateBound_of_exists_certificate
    (patternSet := patternSet) (wrMass := q) (worMass := worMass) (C := C) (R := R) hcert

/-- Certified version of the WR/WOR surrogate transport step. -/
theorem sum_abs_wr_wor_patternMass_toReal_le_of_surrogate_certified
    (patternSet : Finset β)
    (wrMass q worMass : β → ℝ)
    (εW : ℝ) (C : ℚ) (R : ℕ)
    (hwr_q : ∑ p ∈ patternSet, |wrMass p - q p| ≤ εW)
    (hcert :
      ∃ f g : β → ℚ,
        (∀ p, p ∈ patternSet → q p = (f p : ℝ)) ∧
        (∀ p, p ∈ patternSet → worMass p = (g p : ℝ)) ∧
        Mettapedia.Algorithms.finiteL1RateChecker patternSet f g C (R : ℚ) = true) :
    ∑ p ∈ patternSet, |wrMass p - worMass p| ≤ εW + (C : ℝ) / (R : ℝ) := by
  have hq_wor :
      (∑ p ∈ patternSet, |q p - worMass p|) ≤ (C : ℝ) / (R : ℝ) :=
    hq_wor_of_certificate (patternSet := patternSet) (q := q) (worMass := worMass)
      (C := C) (R := R) hcert
  exact sum_abs_wr_wor_patternMass_toReal_le_of_surrogate
    (patternSet := patternSet) (wrMass := wrMass) (q := q) (worMass := worMass)
    (εW := εW) (εPC := (C : ℝ) / (R : ℝ)) hwr_q hq_wor

/-- State-family form of the certified surrogate transport step.
This is the active replacement for plugging per-state rational certificates into
WR/WOR pattern-rate obligations without reviving archived modules. -/
theorem sum_abs_wr_wor_patternMass_toReal_le_of_surrogate_certified_family
    {σ : Type*}
    (patternSet : σ → Finset β)
    (wrMass q worMass : σ → β → ℝ)
    (εW : σ → ℝ)
    (C : ℚ)
    (R : σ → ℕ)
    (hwr_q :
      ∀ s, ∑ p ∈ patternSet s, |wrMass s p - q s p| ≤ εW s)
    (hcert :
      ∀ s, ∃ f g : β → ℚ,
        (∀ p, p ∈ patternSet s → q s p = (f p : ℝ)) ∧
        (∀ p, p ∈ patternSet s → worMass s p = (g p : ℝ)) ∧
        Mettapedia.Algorithms.finiteL1RateChecker (patternSet s) f g C ((R s : ℕ) : ℚ) = true) :
    ∀ s,
      ∑ p ∈ patternSet s, |wrMass s p - worMass s p| ≤
        εW s + (C : ℝ) / (R s : ℝ) := by
  intro s
  exact
    sum_abs_wr_wor_patternMass_toReal_le_of_surrogate_certified
      (patternSet := patternSet s)
      (wrMass := wrMass s)
      (q := q s)
      (worMass := worMass s)
      (εW := εW s)
      (C := C)
      (R := R s)
      (hwr_q := hwr_q s)
      (hcert := hcert s)

end Generic

section RebuildPath

variable {σ β : Type*}

/-- Minimal active quantitative payload for BEST-style WR/WOR pattern-rate bounds. -/
structure QuantitativeCore where
  patternSet : σ → Finset β
  wrMass : σ → β → ℝ
  surrogateMass : σ → β → ℝ
  worMass : σ → β → ℝ
  returnsToStart : σ → ℕ

/-- Statewise rational certificate interface for surrogate→WOR transport. -/
def CertifiedSurrogateWOR
    (core : QuantitativeCore (σ := σ) (β := β))
    (Cpc : ℚ) : Prop :=
  ∀ s, ∃ f g : β → ℚ,
    (∀ p, p ∈ core.patternSet s → core.surrogateMass s p = (f p : ℝ)) ∧
    (∀ p, p ∈ core.patternSet s → core.worMass s p = (g p : ℝ)) ∧
    Mettapedia.Algorithms.finiteL1RateChecker
      (core.patternSet s) f g Cpc ((core.returnsToStart s : ℕ) : ℚ) = true

/-- Core certified transport theorem:
if WR→surrogate is bounded and surrogate→WOR has checker-verified certificates,
then WR→WOR is bounded with the combined rate term. -/
theorem wr_wor_patternRate_of_certified_surrogate
    (core : QuantitativeCore (σ := σ) (β := β))
    (Cpc : ℚ)
    (εW : σ → ℝ)
    (hwr :
      ∀ s,
        ∑ p ∈ core.patternSet s, |core.wrMass s p - core.surrogateMass s p| ≤ εW s)
    (hcert : CertifiedSurrogateWOR (core := core) Cpc) :
    ∀ s,
      ∑ p ∈ core.patternSet s, |core.wrMass s p - core.worMass s p| ≤
        εW s + (Cpc : ℝ) / (core.returnsToStart s : ℝ) := by
  intro s
  exact
    sum_abs_wr_wor_patternMass_toReal_le_of_surrogate_certified
      (patternSet := core.patternSet s)
      (wrMass := core.wrMass s)
      (q := core.surrogateMass s)
      (worMass := core.worMass s)
      (εW := εW s)
      (C := Cpc)
      (R := core.returnsToStart s)
      (hwr_q := hwr s)
      (hcert := hcert s)

/-- Archive-style large-`R` wrapper name on the active rebuilt surface.
This mirrors the old route-A shape while consuming certified checkers. -/
theorem largeR_wr_wor_patternRate_of_canonicalWRSurrogate_largeR_certified
    (core : QuantitativeCore (σ := σ) (β := β))
    (Cw : ℝ) (Cpc : ℚ)
    (hwr :
      ∀ s,
        ∑ p ∈ core.patternSet s, |core.wrMass s p - core.surrogateMass s p| ≤
          Cw / (core.returnsToStart s : ℝ))
    (hcert : CertifiedSurrogateWOR (core := core) Cpc) :
    ∀ s,
      ∑ p ∈ core.patternSet s, |core.wrMass s p - core.worMass s p| ≤
        (Cw + (Cpc : ℝ)) / (core.returnsToStart s : ℝ) := by
  intro s
  have hmain :=
    wr_wor_patternRate_of_certified_surrogate
      (core := core)
      (Cpc := Cpc)
      (εW := fun t => Cw / (core.returnsToStart t : ℝ))
      hwr
      hcert
      s
  have hdiv :
      Cw / (core.returnsToStart s : ℝ) + (Cpc : ℝ) / (core.returnsToStart s : ℝ) =
        (Cw + (Cpc : ℝ)) / (core.returnsToStart s : ℝ) := by
    ring
  simpa [hdiv] using hmain

end RebuildPath

section LocalDemo

private def demoPatternSet : Finset (Fin 1) := {0}
private def demoWrMass : Fin 1 → ℝ := fun _ => (1 / 3 : ℚ)
private def demoQ : Fin 1 → ℝ := fun _ => (1 / 3 : ℚ)
private def demoWorMass : Fin 1 → ℝ := fun _ => (1 / 3 : ℚ)
private def demoF : Fin 1 → ℚ := fun _ => (1 / 3 : ℚ)
private def demoG : Fin 1 → ℚ := fun _ => (1 / 3 : ℚ)
private def demoBadF : Fin 1 → ℚ := fun _ => (1 : ℚ)
private def demoBadG : Fin 1 → ℚ := fun _ => (0 : ℚ)

private lemma demo_hwr_q :
    (∑ p ∈ demoPatternSet, |demoWrMass p - demoQ p|) ≤ (0 : ℝ) := by
  simp [demoPatternSet, demoWrMass, demoQ]

private lemma demo_hcheck_true :
    Mettapedia.Algorithms.finiteL1RateChecker demoPatternSet demoF demoG 0 (1 : ℚ) = true := by
  unfold Mettapedia.Algorithms.finiteL1RateChecker Algorithms.Quantitative.finiteL1RateCheckerList
  refine Algorithms.Quantitative.checker_true_of_prop ?_
  constructor
  · norm_num
  · simp [Algorithms.Quantitative.finiteL1RatList, Algorithms.Quantitative.ratAbs,
      demoPatternSet, demoF, demoG]

/-- Local certificate stub (`f,g,C,R`) that discharges the surrogate→WOR step. -/
private lemma demo_hcert :
    ∃ f g : Fin 1 → ℚ,
      (∀ p, p ∈ demoPatternSet → demoQ p = (f p : ℝ)) ∧
      (∀ p, p ∈ demoPatternSet → demoWorMass p = (g p : ℝ)) ∧
      Mettapedia.Algorithms.finiteL1RateChecker demoPatternSet f g 0 (1 : ℚ) = true := by
  refine ⟨demoF, demoG, ?_, ?_, ?_⟩
  · intro p hp
    simp [demoQ, demoF]
  · intro p hp
    simp [demoWorMass, demoG]
  · simpa using demo_hcheck_true

/-- Same-shape real obligation discharges from `hwr_q + certificate`. -/
theorem demo_real_obligation_discharged :
    (∑ p ∈ demoPatternSet, |demoWrMass p - demoWorMass p|) ≤
      (0 : ℝ) + (0 : ℝ) / (1 : ℝ) := by
  simpa using
    (sum_abs_wr_wor_patternMass_toReal_le_of_surrogate_certified
      (patternSet := demoPatternSet)
      (wrMass := demoWrMass) (q := demoQ) (worMass := demoWorMass)
      (εW := 0) (C := 0) (R := 1) demo_hwr_q demo_hcert)

/-- Negative guard: a bad certificate is rejected by the checker. -/
theorem demo_guard_checker_false :
    Mettapedia.Algorithms.finiteL1RateChecker demoPatternSet demoBadF demoBadG 0 (1 : ℚ) = false := by
  unfold Mettapedia.Algorithms.finiteL1RateChecker Algorithms.Quantitative.finiteL1RateCheckerList
  refine Algorithms.Quantitative.checker_false_of_not_prop ?_
  intro h
  rcases h with ⟨_, hle⟩
  have hsum :
      Algorithms.Quantitative.finiteL1RatList demoPatternSet.toList demoBadF demoBadG = 1 := by
    simp [Algorithms.Quantitative.finiteL1RatList, Algorithms.Quantitative.ratAbs,
      demoPatternSet, demoBadF, demoBadG]
  have : (1 : ℚ) ≤ 0 := by simpa [hsum] using hle
  exact (by norm_num : ¬ ((1 : ℚ) ≤ 0)) this

/-- Negative guard in inequality form: checker-false blocks a false-positive rate claim. -/
theorem demo_guard_rejects_bad_rate_claim :
    ¬ (0 < (1 : ℚ) ∧
      Mettapedia.Algorithms.finiteL1Rat demoPatternSet demoBadF demoBadG ≤ (0 : ℚ) / (1 : ℚ)) := by
  exact Mettapedia.Algorithms.not_finiteL1Rate_of_checker_false
    (s := demoPatternSet) (f := demoBadF) (g := demoBadG) (C := 0) (R := (1 : ℚ))
    demo_guard_checker_false

end LocalDemo

end Mettapedia.Logic.HardBEST
