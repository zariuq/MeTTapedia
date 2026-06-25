import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
import Mettapedia.PLN.Evidence.BinaryEvidence
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.ENNReal.Basic

/-!
# Dirichlet Evidence Quantale & Heyting Extension

Extends the quantale and Heyting algebra structures from binary evidence
(`BinaryEvidence = ℝ≥0∞ × ℝ≥0∞`) to k-ary Dirichlet evidence
(`DirichletEv k = Fin k → ℝ≥0∞`).

## Key result

The quantale tensor, complete lattice, and Frame (complete Heyting algebra)
structures transfer from binary to Dirichlet via Pi-type instances:
- `ℝ≥0∞` has `CompleteLinearOrder` → `Frame` (from mathlib)
- `Fin k → ℝ≥0∞` inherits `Frame` from `Pi.instFrame`
- Coordinatewise multiplication gives the tensor product
- The binary case (k=2) recovers `BinaryEvidence` exactly

This closes the limitation noted in the book (Ch 5, line 2145):
"[tensor and Heyting] do not yet extend to other carriers."

## References

- BinaryEvidence.lean: binary quantale (~130 theorems, 0 sorry)
- EvidenceDirichlet.lean: Dirichlet evidence with Bayesian update (~40 theorems, 0 sorry)
- Green et al., "Provenance Semirings", PODS 2007 (quantale structure)

0 sorry.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichletQuantale

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet

/-! ## 1. The Dirichlet evidence type

`DirichletEv k` is `Fin k → ℝ≥0∞`: k channels of extended non-negative reals.
All algebraic structure comes from Pi-type instances over `ℝ≥0∞`. -/

abbrev DirichletEv (k : ℕ) := Fin k → ℝ≥0∞

/-! ## 2. Algebraic instances (all inherited from Pi + ℝ≥0∞)

`ℝ≥0∞` has `CompleteLinearOrder` → `CompletelyDistribLattice` → `Frame`.
`Fin k → ℝ≥0∞` inherits all of these from `Pi.instFrame` etc. -/

-- These are all inferInstance — the instances exist from mathlib
noncomputable example (k : ℕ) : CompleteLattice (DirichletEv k) := inferInstance
noncomputable example (k : ℕ) : Order.Frame (DirichletEv k) := inferInstance
noncomputable example (k : ℕ) : AddCommMonoid (DirichletEv k) := inferInstance
noncomputable example (k : ℕ) : CommMonoid (DirichletEv k) := inferInstance

/-! ## 3. Tensor product = coordinatewise multiplication

The tensor `e₁ * e₂` gives `(e₁ * e₂) i = e₁ i * e₂ i`.
This models sequential evidence composition along inference chains. -/

theorem tensor_apply (e₁ e₂ : DirichletEv k) (i : Fin k) :
    (e₁ * e₂) i = e₁ i * e₂ i := rfl

theorem tensor_comm (e₁ e₂ : DirichletEv k) : e₁ * e₂ = e₂ * e₁ :=
  mul_comm e₁ e₂

theorem tensor_assoc (e₁ e₂ e₃ : DirichletEv k) :
    e₁ * e₂ * e₃ = e₁ * (e₂ * e₃) :=
  mul_assoc e₁ e₂ e₃

theorem tensor_one (e : DirichletEv k) : e * 1 = e :=
  mul_one e

/-! ## 4. Hplus = coordinatewise addition

The hplus `e₁ + e₂` gives `(e₁ + e₂) i = e₁ i + e₂ i`.
This models independent evidence aggregation (parallel composition). -/

theorem hplus_apply (e₁ e₂ : DirichletEv k) (i : Fin k) :
    (e₁ + e₂) i = e₁ i + e₂ i := rfl

theorem hplus_comm (e₁ e₂ : DirichletEv k) : e₁ + e₂ = e₂ + e₁ :=
  add_comm e₁ e₂

theorem hplus_assoc (e₁ e₂ e₃ : DirichletEv k) :
    e₁ + e₂ + e₃ = e₁ + (e₂ + e₃) :=
  add_assoc e₁ e₂ e₃

/-! ## 5. Lattice operations = coordinatewise min/max -/

theorem inf_apply (e₁ e₂ : DirichletEv k) (i : Fin k) :
    (e₁ ⊓ e₂) i = min (e₁ i) (e₂ i) := rfl

theorem sup_apply (e₁ e₂ : DirichletEv k) (i : Fin k) :
    (e₁ ⊔ e₂) i = max (e₁ i) (e₂ i) := rfl

/-! ## 6. Bridge to MultiEvidence k -/

/-- Embed discrete Dirichlet counts into the continuous carrier. -/
noncomputable def embedMulti (e : MultiEvidence k) : DirichletEv k :=
  fun i => ↑(e.counts i)

/-- Embedding preserves hplus (coordinatewise addition). -/
theorem embedMulti_add (e₁ e₂ : MultiEvidence k) :
    embedMulti (MultiEvidence.hplus e₁ e₂) = embedMulti e₁ + embedMulti e₂ := by
  funext i; simp [embedMulti, MultiEvidence.hplus, Nat.cast_add]

/-! ## 7. Binary equivalence at k=2

At k=2, `DirichletEv 2 = Fin 2 → ℝ≥0∞` is isomorphic to `BinaryEvidence`.
The isomorphism preserves both tensor (multiplication) and hplus (addition). -/

/-- Convert DirichletEv 2 to BinaryEvidence. -/
noncomputable def toBinaryEvidence (e : DirichletEv 2) : BinaryEvidence :=
  ⟨e 0, e 1⟩

/-- Convert BinaryEvidence to DirichletEv 2. -/
noncomputable def ofBinaryEvidence (b : BinaryEvidence) : DirichletEv 2 :=
  fun i => if i = 0 then b.pos else b.neg

theorem toBinaryEvidence_ofBinaryEvidence (b : BinaryEvidence) :
    toBinaryEvidence (ofBinaryEvidence b) = b := by
  simp [toBinaryEvidence, ofBinaryEvidence]

theorem toBinaryEvidence_mul (e₁ e₂ : DirichletEv 2) :
    (toBinaryEvidence (e₁ * e₂)).pos = (toBinaryEvidence e₁).pos * (toBinaryEvidence e₂).pos ∧
    (toBinaryEvidence (e₁ * e₂)).neg = (toBinaryEvidence e₁).neg * (toBinaryEvidence e₂).neg := by
  exact ⟨rfl, rfl⟩

theorem toBinaryEvidence_add (e₁ e₂ : DirichletEv 2) :
    (toBinaryEvidence (e₁ + e₂)).pos = (toBinaryEvidence e₁).pos + (toBinaryEvidence e₂).pos ∧
    (toBinaryEvidence (e₁ + e₂)).neg = (toBinaryEvidence e₁).neg + (toBinaryEvidence e₂).neg := by
  exact ⟨rfl, rfl⟩

/-! ## 8. Total evidence and per-channel strength -/

/-- Total evidence across all channels. -/
noncomputable def totalEvidence (e : DirichletEv k) : ℝ≥0∞ :=
  ∑ i, e i

/-- Per-channel strength: proportion of total evidence in channel i. -/
noncomputable def channelStrength (e : DirichletEv k) (i : Fin k) : ℝ≥0∞ :=
  e i / totalEvidence e

/-! ## 9. Summary -/

/-- The Dirichlet evidence carrier inherits Frame (complete Heyting algebra)
    from `ℝ≥0∞`'s `CompleteLinearOrder` via `Pi.instFrame`. This means
    meet distributes over arbitrary joins — the Heyting implication exists
    and satisfies the residuation law. -/
noncomputable example (k : ℕ) : Order.Frame (DirichletEv k) := inferInstance

end Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichletQuantale
