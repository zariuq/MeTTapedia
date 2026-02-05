import Mettapedia.Logic.PLNFirstOrder.Basic

/-!
# SatisfyingSet: Frame-Valued Predicates as Subobject Classifier

This file formalizes **SatisfyingSet** as the subobject classifier pattern for PLN.

## Key Insight

In topos theory, subobjects are classified by characteristic morphisms χ : X → Ω.
For PLN:
- Ω = Evidence (which IS a Frame = complete Heyting algebra)
- SatisfyingSet wraps a predicate P : U → Evidence
- The diagonal relation D_P = {(u,v) | P(u) ∧ P(v)} is the key to quantifier evaluation

## Diagonal Relation

For predicate P : U → Evidence, the diagonal D_P consists of pairs (u,v) where BOTH:
- u satisfies P (isTrue(P(u)))
- v satisfies P (isTrue(P(v)))

This diagonal relation is what Goertzel's weakness function operates on for quantifier evaluation.

## References

- Plan file (hashed-baking-bumblebee.md)
- Goertzel, "Weakness and Its Quantale"
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (subobject classifier)
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open scoped ENNReal
open Classical

/-! ## SatisfyingSet Structure -/

/-- A Frame-valued predicate on a finite type U.

This is the characteristic morphism χ : U → Ω where Ω = Evidence (Frame).
In topos-theoretic terms, this classifies a subobject of U. -/
structure SatisfyingSet (U : Type*) [Fintype U] where
  /-- The predicate P : U → Evidence (Frame-valued) -/
  pred : U → Evidence

namespace SatisfyingSet

variable {U : Type*} [Fintype U]

/-! ## Diagonal Relation -/

/-- The diagonal relation: pairs (u,v) where both u and v satisfy the predicate.

This is the key structure for quantifier evaluation via weakness.
For ∀x : P(x), we compute weakness of diagonal(P). -/
noncomputable def diagonal (S : SatisfyingSet U) : Finset (U × U) :=
  Finset.univ.filter (fun (u, v) => isTrue (S.pred u) ∧ isTrue (S.pred v))

/-- The complement diagonal: pairs where at least one does NOT satisfy the predicate.

Used for existential quantifier via De Morgan: ∃x : P(x) = ¬∀x : ¬P(x) -/
noncomputable def complement_diagonal (S : SatisfyingSet U) : Finset (U × U) :=
  Finset.univ.filter (fun (u, v) => ¬(isTrue (S.pred u) ∧ isTrue (S.pred v)))

/-! ## Basic Properties of Diagonal -/

theorem mem_diagonal (S : SatisfyingSet U) (uv : U × U) :
    uv ∈ diagonal S ↔ isTrue (S.pred uv.1) ∧ isTrue (S.pred uv.2) := by
  simp [diagonal]

theorem mem_complement_diagonal (S : SatisfyingSet U) (uv : U × U) :
    uv ∈ complement_diagonal S ↔ ¬(isTrue (S.pred uv.1) ∧ isTrue (S.pred uv.2)) := by
  simp [complement_diagonal]

/-- Diagonals are disjoint -/
theorem diagonal_disjoint_complement (S : SatisfyingSet U) :
    Disjoint (diagonal S) (complement_diagonal S) := by
  rw [Finset.disjoint_iff_ne]
  intros x hx y hy
  rw [mem_diagonal] at hx
  rw [mem_complement_diagonal] at hy
  intro heq
  rw [← heq] at hy
  exact hy hx

/-! ## NOTE: Why Diagonal Monotonicity Fails

The theorem `diagonal S₁ ⊆ diagonal S₂` from `∀ u, S₁.pred u ≤ S₂.pred u` is **FALSE**.

**Counter-example**:
- Let S₁.pred u = ⟨1, 0⟩ (isTrue holds: pos > 0, neg = 0)
- Let S₂.pred u = ⟨1, 1⟩ (isTrue fails: neg ≠ 0)
- We have S₁.pred u ≤ S₂.pred u (coordinatewise: 1≤1, 0≤1)
- But isTrue (S₁.pred u) and ¬isTrue (S₂.pred u)

**Reason**: `isTrue` requires BOTH pos > 0 AND neg = 0. The Evidence lattice order
allows neg to increase (gaining negative evidence), which breaks the isTrue property.

This is a feature, not a bug! Evidence is a **Heyting algebra** (paraconsistent logic),
not a Boolean algebra. The "true" corner and "both" corner are different points.

For monotonicity in PLN quantifiers, we instead use monotonicity of the **weakness function**
itself with respect to weight functions (proven in WeaknessConnection.lean).
-/

/-! ## Helper Functions -/

/-- The satisfying set for a constantly true predicate -/
def constantTrue : SatisfyingSet U :=
  ⟨fun _ => pTrue⟩

/-- The satisfying set for a constantly false predicate -/
def constantFalse : SatisfyingSet U :=
  ⟨fun _ => pFalse⟩

/-- Diagonal of constantTrue is the full square -/
theorem diagonal_constantTrue :
    diagonal (constantTrue : SatisfyingSet U) = Finset.univ := by
  ext uv
  constructor
  · intro _; exact Finset.mem_univ uv
  · intro _
    rw [mem_diagonal]
    constructor
    · unfold constantTrue pTrue PLNQuantaleSemantics.PBit.isTrue
      exact ⟨zero_lt_one, rfl⟩
    · unfold constantTrue pTrue PLNQuantaleSemantics.PBit.isTrue
      exact ⟨zero_lt_one, rfl⟩

/-- Diagonal of constantFalse is empty -/
theorem diagonal_constantFalse :
    diagonal (constantFalse : SatisfyingSet U) = ∅ := by
  ext uv
  simp only [mem_diagonal, constantFalse, pFalse]
  constructor
  · intro h
    unfold PLNQuantaleSemantics.PBit.isTrue at h
    exact absurd h.1.1 (not_lt.mpr (le_refl 0))
  · intro h; simp at h

end SatisfyingSet

end Mettapedia.Logic.PLNFirstOrder
