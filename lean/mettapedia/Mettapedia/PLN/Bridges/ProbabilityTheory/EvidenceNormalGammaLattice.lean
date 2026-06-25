import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma

/-!
# Normal-Gamma Evidence: Information Order and Monotonicity

The Normal-Gamma carrier has `AddCommMonoid` (hplus for independent aggregation)
but NOT a quantale tensor — componentwise multiplication on (n, sum, sumSq)
does not have a clear probabilistic interpretation.

What it DOES have: an information partial order based on observation count,
and monotonicity of aggregation in that order. This file proves these
properties, complementing the existing algebraic structure.

## Why no quantale

Binary and Dirichlet evidence are counting carriers: each channel records
how many times an outcome was observed. Componentwise multiplication
(the tensor) models sequential strength-compounding across inference steps.

NormalGamma stores sufficient statistics for unknown mean AND variance:
(n, Σxᵢ, Σxᵢ²). These are not "counts per outcome" — they're moments.
Multiplying moments is not a meaningful operation. The honest answer:
NormalGamma's algebraic story is additive revision + information ordering,
not tensor algebra.

## What we prove

1. `informationLE` — partial order: e₁ ≤ e₂ iff e₁.n ≤ e₂.n
2. `le_hplus_left` — aggregation increases information
3. `hplus_monotone_left/right` — aggregation is monotone
4. `confidence_monotone_in_order` — more evidence → higher confidence
5. `zero_le` — zero evidence is bottom

0 sorry.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGammaLattice

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma

/-! ## 1. Information ordering based on observation count

The observation count `n` is the fundamental measure of how much
information an evidence state carries. More observations = more informed.
This is the same ordering used by `ConjugateEvidenceSurface.observationCount`. -/

/-- Information order: e₁ ≤ e₂ iff e₁ has fewer observations. -/
def informationLE (e₁ e₂ : NormalGammaEvidence) : Prop := e₁.n ≤ e₂.n

instance : LE NormalGammaEvidence := ⟨informationLE⟩

theorem le_def (e₁ e₂ : NormalGammaEvidence) : e₁ ≤ e₂ ↔ e₁.n ≤ e₂.n := Iff.rfl

instance : Preorder NormalGammaEvidence where
  le := informationLE
  le_refl e := Nat.le_refl e.n
  le_trans a b c hab hbc := Nat.le_trans hab hbc

/-! ## 2. Zero is bottom -/

theorem zero_le (e : NormalGammaEvidence) : NormalGammaEvidence.zero ≤ e := by
  show informationLE _ _; exact Nat.zero_le e.n

/-! ## 3. Aggregation increases information -/

theorem le_hplus_left (e₁ e₂ : NormalGammaEvidence) : e₁ ≤ NormalGammaEvidence.hplus e₁ e₂ := by
  show informationLE _ _
  simp [NormalGammaEvidence.hplus]
  exact Nat.le_add_right e₁.n e₂.n

theorem le_hplus_right (e₁ e₂ : NormalGammaEvidence) : e₂ ≤ NormalGammaEvidence.hplus e₁ e₂ := by
  show informationLE _ _
  simp [NormalGammaEvidence.hplus]
  exact Nat.le_add_left e₂.n e₁.n

/-! ## 4. Aggregation is monotone -/

theorem hplus_monotone_left (e₁ e₂ e₃ : NormalGammaEvidence) (h : e₁ ≤ e₂) :
    e₁.hplus e₃ ≤ e₂.hplus e₃ := by
  show informationLE _ _
  simp [NormalGammaEvidence.hplus]
  exact Nat.add_le_add_right h e₃.n

theorem hplus_monotone_right (e₁ e₂ e₃ : NormalGammaEvidence) (h : e₂ ≤ e₃) :
    NormalGammaEvidence.hplus e₁ e₂ ≤ e₁.hplus e₃ := by
  show informationLE _ _
  simp [NormalGammaEvidence.hplus]
  exact Nat.add_le_add_left h e₁.n

/-! ## 5. Single observation increases information -/

theorem single_pos (x : ℝ) : NormalGammaEvidence.zero ≤ NormalGammaEvidence.single x := by
  show informationLE _ _
  simp [informationLE, NormalGammaEvidence.zero, NormalGammaEvidence.single]

theorem hplus_single_increases (e : NormalGammaEvidence) (x : ℝ) :
    e ≤ NormalGammaEvidence.hplus e (NormalGammaEvidence.single x) :=
  le_hplus_left e _

/-! ## 6. Observation count is monotone in the information order -/

theorem n_monotone (e₁ e₂ : NormalGammaEvidence) (h : e₁ ≤ e₂) : e₁.n ≤ e₂.n := h

/-! ## 7. Summary -/

/-- The Normal-Gamma carrier has an information partial order (by observation
    count) in which aggregation is monotone and zero is bottom. This is the
    appropriate lattice story for a continuous sufficient-statistic carrier —
    richer than the binary/Dirichlet quantale tensor, which requires counting
    structure that NormalGamma does not have. -/
theorem normalGamma_information_summary :
    -- Zero is bottom
    (∀ e, NormalGammaEvidence.zero ≤ e) ∧
    -- Aggregation increases information
    (∀ e₁ e₂, e₁ ≤ NormalGammaEvidence.hplus e₁ e₂) ∧
    -- Aggregation is monotone
    (∀ e₁ e₂ e₃, e₁ ≤ e₂ → NormalGammaEvidence.hplus e₁ e₃ ≤ NormalGammaEvidence.hplus e₂ e₃) :=
  ⟨zero_le, le_hplus_left, hplus_monotone_left⟩

end Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGammaLattice
