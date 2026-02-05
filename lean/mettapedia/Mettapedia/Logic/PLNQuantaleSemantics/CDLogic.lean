import Mettapedia.Logic.PLNQuantaleSemantics.PBit

/-!
# CD (Constructible Duality) Logic Operations

This file formalizes Goertzel's CD logic operations from the paper
"Paraconsistent Foundations for Probabilistic Reasoning, Programming and
Concept Learning" (arXiv:2012.14474).

## Key Operations

1. **CD Negation** (cdNeg): Swaps positive and negative evidence
2. **CD Tensor** (cdTensor): Multiplicative conjunction (coordinatewise ×)
3. **CD Par** (cdPar): Additive disjunction (coordinatewise +)

## References

- Goertzel et al., "Paraconsistent Foundations..." (arXiv:2012.14474)
- Girard, "Linear Logic" (1987)
-/

namespace Mettapedia.Logic.PLNQuantaleSemantics.CDLogic

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open scoped ENNReal

/-! ## CD Negation

The fundamental duality operation: swap positive and negative evidence.
-/

/-- CD Negation: swap positive and negative evidence -/
def cdNeg (e : Evidence) : Evidence := ⟨e.neg, e.pos⟩

/-- CD negation notation -/
prefix:100 "∼" => cdNeg

/-- CD negation is an involution: ∼∼e = e -/
theorem cdNeg_involution (e : Evidence) : ∼(∼e) = e := by
  simp only [cdNeg]

/-- CD negation swaps true and false corners -/
theorem cdNeg_pTrue : ∼pTrue = pFalse := by
  simp only [cdNeg, pTrue, pFalse]

theorem cdNeg_pFalse : ∼pFalse = pTrue := by
  simp only [cdNeg, pTrue, pFalse]

/-- CD negation preserves neither -/
theorem cdNeg_pNeither : ∼pNeither = pNeither := by
  simp only [cdNeg, pNeither]

/-- CD negation preserves both -/
theorem cdNeg_pBoth : ∼pBoth = pBoth := by
  simp only [cdNeg, pBoth]

/-- CD negation reverses the truth quadrant -/
theorem cdNeg_isTrue_iff_isFalse (e : Evidence) : PBit.isTrue (∼e) ↔ PBit.isFalse e := by
  simp only [cdNeg, PBit.isTrue, PBit.isFalse]
  constructor <;> (intro ⟨h1, h2⟩; exact ⟨h2, h1⟩)

theorem cdNeg_isFalse_iff_isTrue (e : Evidence) : PBit.isFalse (∼e) ↔ PBit.isTrue e := by
  simp only [cdNeg, PBit.isTrue, PBit.isFalse]
  constructor <;> (intro ⟨h1, h2⟩; exact ⟨h2, h1⟩)

/-- CD negation preserves the "neither" status -/
theorem cdNeg_isNeither_iff (e : Evidence) : PBit.isNeither (∼e) ↔ PBit.isNeither e := by
  simp only [cdNeg, PBit.isNeither]
  constructor <;> (intro ⟨h1, h2⟩; exact ⟨h2, h1⟩)

/-- CD negation preserves the "both" status -/
theorem cdNeg_isBoth_iff (e : Evidence) : PBit.isBoth (∼e) ↔ PBit.isBoth e := by
  simp only [cdNeg, PBit.isBoth]
  constructor <;> (intro ⟨h1, h2⟩; exact ⟨h2, h1⟩)

/-! ## CD Tensor (Multiplicative Conjunction)

The tensor product ⊗ is coordinatewise multiplication.
-/

/-- CD Tensor: coordinatewise multiplication -/
noncomputable def cdTensor (a b : Evidence) : Evidence := a * b

/-- CD tensor notation -/
infixl:70 " ⊙ " => cdTensor

/-- CD tensor is commutative -/
theorem cdTensor_comm (a b : Evidence) : a ⊙ b = b ⊙ a :=
  Evidence.tensor_comm a b

/-- CD tensor is associative -/
theorem cdTensor_assoc (a b c : Evidence) : (a ⊙ b) ⊙ c = a ⊙ (b ⊙ c) :=
  Evidence.tensor_assoc a b c

/-- Evidence.one is the tensor unit -/
theorem cdTensor_one (a : Evidence) : a ⊙ Evidence.one = a :=
  Evidence.tensor_one a

theorem one_cdTensor (a : Evidence) : Evidence.one ⊙ a = a :=
  Evidence.one_tensor a

/-! ## CD Par (Additive Disjunction)

The par operation ⅋ is coordinatewise addition.
This corresponds to combining independent evidence.
-/

/-- CD Par: coordinatewise addition (independent evidence combination) -/
noncomputable def cdPar (a b : Evidence) : Evidence := a + b

/-- CD par notation -/
infixl:65 " ⅋ " => cdPar

/-- CD par is commutative -/
theorem cdPar_comm (a b : Evidence) : a ⅋ b = b ⅋ a :=
  Evidence.hplus_comm a b

/-- CD par is associative -/
theorem cdPar_assoc (a b c : Evidence) : (a ⅋ b) ⅋ c = a ⅋ (b ⅋ c) :=
  Evidence.hplus_assoc a b c

/-- Evidence.zero is the par unit -/
theorem cdPar_zero (a : Evidence) : a ⅋ Evidence.zero = a :=
  Evidence.hplus_zero a

theorem zero_cdPar (a : Evidence) : Evidence.zero ⅋ a = a :=
  Evidence.zero_hplus a

/-! ## CD Negation and Lattice Operations -/

/-- CD negation swaps inf components -/
theorem cdNeg_inf (a b : Evidence) : ∼(a ⊓ b) = (∼a) ⊓ (∼b) := rfl

/-- CD negation swaps sup components -/
theorem cdNeg_sup (a b : Evidence) : ∼(a ⊔ b) = (∼a) ⊔ (∼b) := rfl

/-! ## Tensor Distributes over Join (Quantale Law)

This is the key quantale property: ⊗ distributes over ⊔.
-/

/-- Helper: multiplication distributes over max for ENNReal -/
theorem ENNReal_mul_max (a b c : ℝ≥0∞) : a * max b c = max (a * b) (a * c) := by
  rcases le_total b c with hbc | hcb
  · simp only [max_eq_right hbc, max_eq_right (mul_le_mul_left' hbc a)]
  · simp only [max_eq_left hcb, max_eq_left (mul_le_mul_left' hcb a)]

/-- Tensor distributes over binary join -/
theorem cdTensor_sup_left (a b c : Evidence) :
    a ⊙ (b ⊔ c) = (a ⊙ b) ⊔ (a ⊙ c) := by
  simp only [cdTensor, Evidence.tensor_def]
  ext
  · -- pos component: a.pos * max b.pos c.pos = max (a.pos * b.pos) (a.pos * c.pos)
    exact ENNReal_mul_max a.pos b.pos c.pos
  · -- neg component
    exact ENNReal_mul_max a.neg b.neg c.neg

theorem cdTensor_sup_right (a b c : Evidence) :
    (a ⊔ b) ⊙ c = (a ⊙ c) ⊔ (b ⊙ c) := by
  rw [cdTensor_comm, cdTensor_sup_left, cdTensor_comm a c, cdTensor_comm b c]

/-! ## Summary

This file establishes:

1. **CD Negation** (∼): Involutive swap of pos/neg
   - ∼∼e = e (involution)
   - Swaps true/false, preserves neither/both

2. **CD Tensor** (⊙): Multiplicative conjunction (coordinatewise ×)
   - Commutative, associative
   - Unit is Evidence.one = ⟨1, 1⟩
   - Distributes over join (quantale law)

3. **CD Par** (⅋): Additive disjunction (coordinatewise +)
   - Commutative, associative
   - Unit is Evidence.zero = ⟨0, 0⟩
   - Corresponds to independent evidence aggregation

4. **Lattice preservation**: CD negation preserves meet/join structure
-/

end Mettapedia.Logic.PLNQuantaleSemantics.CDLogic
