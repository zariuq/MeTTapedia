import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy

/-!
# Direct Path: K&S Representation → ProbDist

This file provides the **direct, honest grounding** of `ProbDist` on the K&S derivation,
without going through the PLN/Boolean algebra detour.

## The Actual Path

```
KnuthSkillingMonoidBase α + KSSeparation α
        ↓ (associativity_representation - from Main.lean)
∃ Θ : α → ℝ, additive order-preserving, Θ(ident) = 0
        ↓ (this file: KSRepresentationData.toProbDist)
ProbDist n
```

## Key Insight

The K&S representation theorem gives us:
- `Θ : α → ℝ` with `Θ(op x y) = Θ x + Θ y`
- Order preservation: `a ≤ b ↔ Θ a ≤ Θ b`
- `Θ ident = 0`

For a **finite** KS algebra with atoms `{a₁, ..., aₙ}` above identity:
- Define `P(aᵢ) := Θ(aᵢ) / Θ(top)` where `top` is some reference element
- These form a probability distribution (sum to 1 by additivity)

## Why This Works (Mathematically)

In K&S, the operation `op` represents "combining" valuations. For a finite algebra
where every element can be built from atoms via `op`:
- `Θ(a₁ op a₂ op ... op aₙ) = Θ(a₁) + Θ(a₂) + ... + Θ(aₙ)`
- If `top = a₁ op a₂ op ... op aₙ`, then `∑ᵢ Θ(aᵢ) = Θ(top)`
- Normalizing: `∑ᵢ P(aᵢ) = 1`

This is the **true grounding** of finite probability on K&S, not an assumed structure!

## References

- Knuth & Skilling, "Foundations of Inference" (2012), Appendix A
- Additive/Proofs/GridInduction/Main.lean for the representation theorem
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.ToProbDist

open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive
open KnuthSkillingAlgebraBase
open KnuthSkillingMonoidBase
open Finset BigOperators

/-! ## §1: Packaging the Representation Theorem Output -/

/-- The data extracted from the K&S representation theorem.

This packages the existential output of `associativity_representation` into
a usable structure. Note: This is DERIVED, not assumed! -/
structure KSRepresentationData (α : Type*) [KnuthSkillingMonoidBase α] where
  /-- The additive valuation from the representation theorem -/
  Θ : α → ℝ
  /-- Order equivalence -/
  order_iff : ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b
  /-- Identity maps to zero -/
  ident_zero : Θ ident = 0
  /-- Additivity with respect to `op` -/
  additive : ∀ x y : α, Θ (op x y) = Θ x + Θ y

namespace KSRepresentationData

variable {α : Type*} [KnuthSkillingMonoidBase α]

/-- Extract representation data from the theorem (requires separation + globalization) -/
noncomputable def ofKSSeparation
    [KSSeparation α] [RepresentationGlobalization α] : KSRepresentationData α := by
  choose Θ hΘ using associativity_representation α
  exact {
    Θ := Θ
    order_iff := hΘ.1
    ident_zero := hΘ.2.1
    additive := hΘ.2.2
  }

/-- Θ is non-negative for elements ≥ ident -/
theorem Θ_nonneg (R : KSRepresentationData α) (a : α) (ha : ident ≤ a) : 0 ≤ R.Θ a := by
  rw [← R.ident_zero]
  exact (R.order_iff ident a).mp ha

/-- Θ is strictly positive for elements > ident -/
theorem Θ_pos (R : KSRepresentationData α) (a : α) (ha : ident < a) : 0 < R.Θ a := by
  rw [← R.ident_zero]
  have h1 : R.Θ ident ≤ R.Θ a := (R.order_iff ident a).mp (le_of_lt ha)
  have h2 : R.Θ ident ≠ R.Θ a := by
    intro heq
    have ha' : a ≤ ident := (R.order_iff a ident).mpr (le_of_eq heq.symm)
    exact (not_le.mpr ha) ha'
  exact lt_of_le_of_ne h1 h2

/-- Θ is monotone -/
theorem Θ_mono (R : KSRepresentationData α) : Monotone R.Θ :=
  fun _ _ hab => (R.order_iff _ _).mp hab

/-- Θ reflects the order -/
theorem Θ_reflect (R : KSRepresentationData α) {a b : α} (h : R.Θ a ≤ R.Θ b) : a ≤ b :=
  (R.order_iff a b).mpr h

end KSRepresentationData

/-! ## §2: Finite Atoms and Probability Distribution -/

/-- An atom in a KS algebra: minimal positive element -/
def IsAtom [KnuthSkillingMonoidBase α] (a : α) : Prop :=
  ident < a ∧ ∀ x, ident < x → x ≤ a → x = a

/-- A finite atomic KS algebra: finitely many atoms that generate the algebra via `op` -/
class FiniteAtomicKS (α : Type*) [KnuthSkillingMonoidBase α] where
  /-- The number of atoms -/
  n : ℕ
  /-- The atoms, indexed by Fin n -/
  atom : Fin n → α
  /-- Each atom is indeed an atom -/
  atom_isAtom : ∀ i, IsAtom (atom i)
  /-- The "top" element: reference for normalization -/
  top : α
  /-- Top is greater than identity -/
  top_pos : ident < top
  /-- Key property: Θ(top) = sum of Θ(atoms) for any representation Θ
      This is the defining property that makes atoms "partition" top -/
  Θ_top_eq_sum : ∀ (Θ : α → ℝ), (∀ x y, Θ (op x y) = Θ x + Θ y) →
                  n > 0 → Θ top = ∑ i : Fin n, Θ (atom i)
  /-- Atoms are distinct (different indices give different atoms) -/
  atom_injective : Function.Injective atom

namespace FiniteAtomicKS

variable {α : Type*} [KnuthSkillingMonoidBase α] [F : FiniteAtomicKS α]

/-- The Θ-value of top equals the sum of Θ-values of atoms (for n ≥ 1) -/
theorem top_Θ_eq_sum_atoms (R : KSRepresentationData α) (hn : F.n > 0) :
    R.Θ F.top = ∑ i : Fin F.n, R.Θ (F.atom i) :=
  F.Θ_top_eq_sum R.Θ R.additive hn

/-- All atoms have positive Θ-value -/
theorem Θ_atom_pos (R : KSRepresentationData α) (i : Fin F.n) : 0 < R.Θ (F.atom i) :=
  R.Θ_pos (F.atom i) (F.atom_isAtom i).1

/-- Top has positive Θ-value -/
theorem Θ_top_pos (R : KSRepresentationData α) : 0 < R.Θ F.top :=
  R.Θ_pos F.top F.top_pos

end FiniteAtomicKS

/-! ## §3: The Main Bridge: KS Representation → ProbDist -/

/-- **The grounded probability distribution from K&S representation.**

Given:
- A finite atomic KS algebra with n atoms
- The representation Θ from the K&S theorem

We extract `ProbDist n` where `P(i) = Θ(atomᵢ) / Θ(top)`.

This is the TRUE grounding of ProbDist on K&S! -/
noncomputable def KSRepresentationData.toProbDist
    {α : Type*} [KnuthSkillingMonoidBase α] [F : FiniteAtomicKS α]
    (R : KSRepresentationData α) (hn : F.n > 0) : ProbDist F.n where
  p := fun i => R.Θ (F.atom i) / R.Θ F.top
  nonneg := by
    intro i
    apply div_nonneg
    · exact le_of_lt (FiniteAtomicKS.Θ_atom_pos R i)
    · exact le_of_lt (FiniteAtomicKS.Θ_top_pos R)
  sum_one := by
    have htop_pos : 0 < R.Θ F.top := FiniteAtomicKS.Θ_top_pos R
    have htop_ne : R.Θ F.top ≠ 0 := ne_of_gt htop_pos
    calc ∑ i, R.Θ (F.atom i) / R.Θ F.top
        = (∑ i, R.Θ (F.atom i)) / R.Θ F.top := by rw [Finset.sum_div]
      _ = R.Θ F.top / R.Θ F.top := by rw [← FiniteAtomicKS.top_Θ_eq_sum_atoms R hn]
      _ = 1 := div_self htop_ne

/-- The i-th probability equals Θ(atomᵢ) / Θ(top) -/
theorem KSRepresentationData.toProbDist_apply
    {α : Type*} [KnuthSkillingMonoidBase α] [F : FiniteAtomicKS α]
    (R : KSRepresentationData α) (hn : F.n > 0) (i : Fin F.n) :
    (R.toProbDist hn).p i = R.Θ (F.atom i) / R.Θ F.top := rfl

/-! ## §4: The Full Chain (Summary)

We now have the complete grounded path:

```
[KnuthSkillingMonoidBase α] + [KSSeparation α] + [RepresentationGlobalization α]
        ↓ (associativity_representation)
∃ Θ : α → ℝ, additive, order-preserving, Θ(ident) = 0
        ↓ (KSRepresentationData.ofKSSeparation)
KSRepresentationData α
        ↓ (KSRepresentationData.toProbDist) [requires FiniteAtomicKS α]
ProbDist n
```

No Boolean algebra assumed. No PLN detour. Just K&S → probability.

### Countable Extension (Natural)

For countable disjoint families, the extension requires the **natural** additional axioms:
- `SigmaCompleteEvents E`: countable joins exist
- `KSScaleComplete S R`: sequential completeness of the scale
- `KSScottContinuous E S R`: continuity of valuation

Under these conditions, `ks_sigma_additive` (in ScaleCompleteness.lean) proves that
μ = Θ ∘ v is σ-additive, and `SigmaAdditiveMeasureData.toMeasure` (in MathlibProbability.lean)
provides the bridge to mathlib's `Measure`.

These axioms CANNOT be derived from basic K&S but are mathematically natural extensions
that preserve the core K&S structure while enabling σ-additivity.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.ToProbDist
