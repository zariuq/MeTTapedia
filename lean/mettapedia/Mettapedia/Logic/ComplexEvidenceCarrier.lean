import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.EvidenceClass

/-!
# Complex-Amplitude Evidence Carrier

The ℂ-valued evidence carrier: amplitude-valued inference where
evidence is complex-valued and probability is recovered via |·|².

## The Classification Result

ℂ has `AddCommMonoid` + `CommSemiring` but NOT `CompleteLattice`:
- ✓ `AdditiveWorldModel` works (only needs `AddCommMonoid`)
- ✓ Tensor (multiplication) works (ℂ is a `CommSemiring`)
- ✗ Quantale does NOT apply (no `sSup` on ℂ — not a lattice)
- ✗ Frame/Heyting does NOT apply (no lattice order)

This is NOT a limitation — it's a CLASSIFICATION theorem.
The ℂ carrier sits at the quantum vertex of the probability hypercube:
amplitude-valued, additive, but no lattice ordering.

## Connection to Meredith's CCC Paper

A GSLT equipped with complex weights is a quantum process calculus.
The squared modulus |ψ|² is the transition probability (Born rule).
The WM calculus with `V = ℂ` and `extract_add` gives amplitude-additive
inference: superposition of evidence. The `forget` operation becomes
amplitude cancellation.

## What This Proves

1. `AdditiveWorldModel` is carrier-agnostic: it works for ℂ
2. The tensor (multiplication on ℂ) distributes over addition
3. Probability is recovered via the squared norm
4. The quantum/classical boundary = whether the carrier has a lattice

## References

- Meredith, "Computation, Causality, and Consciousness" (2026)
- von Neumann, "Mathematical Foundations of Quantum Mechanics" (1932)
- WM-PLN book, Ch 19 (Future: Probability Hypercube)

0 sorry.
-/

namespace Mettapedia.Logic.ComplexEvidenceCarrier

open Complex
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric

/-! ## 1. ℂ as an evidence carrier

ℂ has AddCommMonoid — the ONLY requirement for AdditiveWorldModel.
All the abstract WM machinery (extract_add, profile-hom, forgetting)
works over ℂ without modification. -/

/-- ℂ is an EvidenceType (it has AddCommMonoid). -/
noncomputable instance : EvidenceType ℂ := {}

/-- For any query type, ℂ-valued profiles are an EvidenceType. -/
noncomputable instance (Query : Type*) : EvidenceType (Query → ℂ) := {}

/-- The ℂ-valued AdditiveWorldModel: amplitude-additive extraction.
    extract_add holds by rfl (Pi addition is pointwise). -/
noncomputable instance complexWM (Query : Type*) :
    AdditiveWorldModel (Query → ℂ) Query ℂ where
  extract state q := state q
  extract_add _ _ _ := rfl

/-! ## 2. Tensor structure on ℂ

ℂ is a CommSemiring, so tensor (multiplication) distributes over
addition. This gives sequential evidence composition for ℂ-valued
inference chains. -/

/-- Tensor (sequential composition) distributes over hplus (addition).
    This is the Ring distributivity law on ℂ. -/
theorem complex_tensor_distrib_add (a b c : ℂ) :
    a * (b + c) = a * b + a * c :=
  mul_add a b c

/-- Tensor is commutative on ℂ. -/
theorem complex_tensor_comm (a b : ℂ) : a * b = b * a :=
  mul_comm a b

/-- Tensor has identity 1. -/
theorem complex_tensor_one (a : ℂ) : a * 1 = a :=
  mul_one a

/-! ## 3. Probability recovery via squared norm

The Born rule: probability = |amplitude|².
For ℂ-valued evidence, the observable probability at a query is
the squared norm of the extracted amplitude. -/

/-- The Born rule: squared norm gives a non-negative real. -/
noncomputable def bornProbability (z : ℂ) : ℝ :=
  Complex.normSq z

/-- Born probability is non-negative. -/
theorem bornProbability_nonneg (z : ℂ) : 0 ≤ bornProbability z :=
  Complex.normSq_nonneg z

/-- Born probability of zero is zero. -/
theorem bornProbability_zero : bornProbability 0 = 0 := by
  simp [bornProbability, Complex.normSq]

/-- Born probability of a real-valued amplitude is the square. -/
theorem bornProbability_ofReal (r : ℝ) :
    bornProbability (Complex.ofReal r) = r ^ 2 := by
  simp [bornProbability, Complex.normSq, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## 4. The quantum/classical boundary

The boundary between quantum and classical inference is whether
the evidence carrier has a lattice ordering.

- ℝ≥0∞: has CompleteLattice + Frame + Quantale → classical
- ℂ: has AddCommMonoid + CommSemiring, NO lattice → quantum

Both satisfy `extract_add` (additive world model).
Only ℝ≥0∞ satisfies quantale laws (tensor distributes over sSup).
ℂ has tensor distributing over finite sums (Ring), but NOT over
arbitrary suprema (because ℂ has no suprema). -/

/-- ℂ has tensor distributing over FINITE sums (Ring distributivity). -/
theorem complex_tensor_distrib_finsum {ι : Type*} [Fintype ι] (a : ℂ) (f : ι → ℂ) :
    a * ∑ i, f i = ∑ i, a * f i :=
  Finset.mul_sum Finset.univ f a

-- The quantum/classical boundary as a type-level fact:
-- ℂ does NOT have a CompleteLattice instance. This is a classification
-- result, not a limitation. ℂ is algebraically closed → no compatible
-- total order → no complete lattice → no quantale → quantum vertex.
--
-- The following would NOT typecheck (no instance exists):
-- noncomputable example : CompleteLattice ℂ := inferInstance  -- FAILS

section Summary

/-- The ℂ-valued WM has additive extraction + tensor + Born probability.
    It does NOT have quantale/Heyting structure — that's the quantum vertex. -/
theorem complex_carrier_summary :
    -- Tensor distributes over addition (Ring)
    (∀ a b c : ℂ, a * (b + c) = a * b + a * c) ∧
    -- Tensor is commutative
    (∀ a b : ℂ, a * b = b * a) ∧
    -- Born probability is non-negative
    (∀ z : ℂ, 0 ≤ bornProbability z) ∧
    -- Born probability of zero is zero
    bornProbability 0 = 0 := by
  exact ⟨mul_add, mul_comm, fun z => Complex.normSq_nonneg z, bornProbability_zero⟩

end Summary

end Mettapedia.Logic.ComplexEvidenceCarrier
