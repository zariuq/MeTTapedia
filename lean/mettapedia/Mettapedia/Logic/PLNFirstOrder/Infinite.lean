import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.Logic.PLNFirstOrder.SatisfyingSet

/-!
# Infinitary PLN First-Order Logic

This file extends PLN quantifiers to **arbitrary (potentially infinite) domains**.

## Motivation

The finitary version (`QuantifierSemantics.lean`) uses `[Fintype U]` constraint:
- Diagonal relation: `Finset (U × U)`
- Quantifiers collapse to finite conjunctions/disjunctions

For **true first-order logic**, we need infinite domains where:
- ∀x. P(x) is NOT equivalent to a finite conjunction
- Compactness, Löwenheim-Skolem, etc. become meaningful

## Key Changes from Finitary Version

| Aspect | Finitary | Infinitary |
|--------|----------|------------|
| Domain | `[Fintype U]` | Any `U : Type*` |
| Diagonal | `Finset (U × U)` | `Set (U × U)` |
| Weakness | Uses finite `sSup` | Uses arbitrary `sSup` |
| Weight | `WeightFunction U Q` with Fintype | `WeightFunctionInf U Q` |

## Mathematical Content

The infinitary version uses the same mathematical definitions, just with different types:
- `sSup` in a complete lattice already handles arbitrary suprema
- Evidence (ℝ≥0∞ × ℝ≥0∞) is a complete lattice coordinatewise
- No measure theory needed for basic quantifier semantics

## References

- Goertzel, "Weakness and Its Quantale"
- Foundation project (first-order model theory)
-/

namespace Mettapedia.Logic.PLNFirstOrder.Infinite

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open scoped ENNReal

/-! ## Weight Function for Arbitrary Domains -/

/-- Weight function on arbitrary domain U (no Fintype constraint).

For probability-theoretic applications, this would be a density function
with respect to some measure on U. For pure logic, we just need it to
assign Evidence values to domain elements. -/
structure WeightFunctionInf (U : Type*) (Q : Type*) [Monoid Q] where
  /-- The weight assignment μ : U → Q -/
  μ : U → Q

namespace WeightFunctionInf

variable {U : Type*} {Q Q' : Type*} [Monoid Q] [Monoid Q']

/-- Map a weight function through a monoid homomorphism -/
def map [CompleteLattice Q] [CompleteLattice Q']
    (f : Mettapedia.Algebra.QuantaleWeakness.QuantaleHom Q Q')
    (wf : WeightFunctionInf U Q) : WeightFunctionInf U Q' :=
  ⟨fun u => f (wf.μ u)⟩

@[simp]
theorem map_μ [CompleteLattice Q] [CompleteLattice Q']
    (f : Mettapedia.Algebra.QuantaleWeakness.QuantaleHom Q Q')
    (wf : WeightFunctionInf U Q) (u : U) :
    (map f wf).μ u = f (wf.μ u) := rfl

end WeightFunctionInf

/-! ## Infinitary Weakness -/

/-- Weakness of a set H ⊆ U × U under weight function μ.

This is the **arbitrary supremum** version: sSup { μ(u) * μ(v) | (u,v) ∈ H }.
For complete lattices, sSup is well-defined for any set. -/
noncomputable def weaknessInf {U : Type*} {Q : Type*}
    [Monoid Q] [CompleteLattice Q]
    (wf : WeightFunctionInf U Q) (H : Set (U × U)) : Q :=
  sSup { wf.μ p.1 * wf.μ p.2 | p ∈ H }

/-! ## Infinitary SatisfyingSet -/

/-- A Frame-valued predicate on arbitrary domain U.

This is the infinitary version: no Fintype constraint.
The predicate assigns Evidence values to each element of U. -/
structure SatisfyingSetInf (U : Type*) where
  /-- The predicate P : U → Evidence -/
  pred : U → Evidence

namespace SatisfyingSetInf

variable {U : Type*}

/-! ## Diagonal Relation (Set-based) -/

/-- The diagonal relation: pairs (u,v) where both u and v satisfy the predicate.

This is a **Set**, not a Finset - can be infinite. -/
def diagonal (S : SatisfyingSetInf U) : Set (U × U) :=
  { p | isTrue (S.pred p.1) ∧ isTrue (S.pred p.2) }

/-- The complement diagonal: pairs where at least one does NOT satisfy. -/
def complementDiagonal (S : SatisfyingSetInf U) : Set (U × U) :=
  { p | ¬(isTrue (S.pred p.1) ∧ isTrue (S.pred p.2)) }

/-! ## Basic Properties -/

theorem mem_diagonal (S : SatisfyingSetInf U) (p : U × U) :
    p ∈ diagonal S ↔ isTrue (S.pred p.1) ∧ isTrue (S.pred p.2) :=
  Iff.rfl

theorem mem_complementDiagonal (S : SatisfyingSetInf U) (p : U × U) :
    p ∈ complementDiagonal S ↔ ¬(isTrue (S.pred p.1) ∧ isTrue (S.pred p.2)) :=
  Iff.rfl

theorem diagonal_disjoint_complement (S : SatisfyingSetInf U) :
    Disjoint (diagonal S) (complementDiagonal S) := by
  rw [Set.disjoint_iff]
  intro p ⟨hd, hc⟩
  exact hc hd

theorem diagonal_union_complement (S : SatisfyingSetInf U) :
    diagonal S ∪ complementDiagonal S = Set.univ := by
  ext p
  simp only [Set.mem_union, mem_diagonal, mem_complementDiagonal, Set.mem_univ, iff_true]
  exact Classical.em _

/-! ## Negation -/

/-- Negation on SatisfyingSetInf: pointwise Heyting complement -/
noncomputable def neg (S : SatisfyingSetInf U) : SatisfyingSetInf U :=
  ⟨fun u => Evidence.compl (S.pred u)⟩

/-! ## Constants -/

/-- The constantly true predicate -/
def constantTrue : SatisfyingSetInf U :=
  ⟨fun _ => pTrue⟩

/-- The constantly false predicate -/
def constantFalse : SatisfyingSetInf U :=
  ⟨fun _ => pFalse⟩

theorem diagonal_constantTrue :
    diagonal (constantTrue : SatisfyingSetInf U) = Set.univ := by
  ext p
  simp only [mem_diagonal, constantTrue, Set.mem_univ, iff_true]
  unfold pTrue PLNQuantaleSemantics.PBit.isTrue
  exact ⟨⟨zero_lt_one, rfl⟩, ⟨zero_lt_one, rfl⟩⟩

theorem diagonal_constantFalse :
    diagonal (constantFalse : SatisfyingSetInf U) = ∅ := by
  ext p
  simp only [mem_diagonal, constantFalse, pFalse, Set.mem_empty_iff_false, iff_false]
  intro ⟨h1, _⟩
  unfold PLNQuantaleSemantics.PBit.isTrue at h1
  exact absurd h1.1 (not_lt.mpr (le_refl 0))

end SatisfyingSetInf

/-! ## Infinitary Quantifier Evaluation -/

/-- Evaluate ∀x : P(x) via weakness of the diagonal relation (infinitary version).

This computes the supremum over all pairs (u,v) where both satisfy P,
weighted by the weight function μ. -/
noncomputable def forAllEvalInf {U : Type*}
    (S : SatisfyingSetInf U)
    (μ : WeightFunctionInf U Evidence) : Evidence :=
  weaknessInf μ (SatisfyingSetInf.diagonal S)

/-- Evaluate ∃x : P(x) via De Morgan: ∃x : P(x) = ¬(∀x : ¬P(x)) -/
noncomputable def thereExistsEvalInf {U : Type*}
    (S : SatisfyingSetInf U)
    (μ : WeightFunctionInf U Evidence) : Evidence :=
  Evidence.compl (forAllEvalInf (SatisfyingSetInf.neg S) μ)

/-! ## Basic Theorems -/

variable {U : Type*}

/-- ForAll evaluation for constantTrue gives supremum of all pairs -/
theorem forAllEvalInf_constantTrue (μ : WeightFunctionInf U Evidence) :
    forAllEvalInf SatisfyingSetInf.constantTrue μ =
    sSup { e | ∃ (u : U) (v : U), e = μ.μ u * μ.μ v } := by
  unfold forAllEvalInf weaknessInf
  rw [SatisfyingSetInf.diagonal_constantTrue]
  -- Both sides are sSup over the same set (up to reformulation)
  -- { μ.μ p.1 * μ.μ p.2 | p ∈ univ } = { e | ∃ u v, e = μ.μ u * μ.μ v }
  congr 1
  ext e
  constructor
  · intro ⟨p, _, he⟩
    exact ⟨p.1, ⟨p.2, he.symm⟩⟩
  · intro ⟨u, v, he⟩
    exact ⟨(u, v), Set.mem_univ _, he.symm⟩

/-- ForAll evaluation for constantFalse gives bottom -/
theorem forAllEvalInf_constantFalse (μ : WeightFunctionInf U Evidence) :
    forAllEvalInf SatisfyingSetInf.constantFalse μ = ⊥ := by
  unfold forAllEvalInf weaknessInf
  rw [SatisfyingSetInf.diagonal_constantFalse]
  have h : { μ.μ p.1 * μ.μ p.2 | p ∈ (∅ : Set (U × U)) } = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
    constructor
    · intro ⟨_, h, _⟩; exact h
    · intro h; exact h.elim
  rw [h, sSup_empty]

/-- De Morgan law holds by definition -/
theorem deMorgan_inf (S : SatisfyingSetInf U) (μ : WeightFunctionInf U Evidence) :
    thereExistsEvalInf S μ =
    Evidence.compl (forAllEvalInf (SatisfyingSetInf.neg S) μ) := rfl

/-! ## Weakness Properties -/

/-- Weakness of empty set is bottom -/
theorem weaknessInf_empty {Q : Type*} [Monoid Q] [CompleteLattice Q]
    (wf : WeightFunctionInf U Q) :
    weaknessInf wf ∅ = ⊥ := by
  unfold weaknessInf
  have h : { wf.μ p.1 * wf.μ p.2 | p ∈ (∅ : Set (U × U)) } = ∅ := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
    constructor
    · intro ⟨_, hp, _⟩; exact hp
    · intro hp; exact hp.elim
  rw [h, sSup_empty]

/-- Weakness is monotone in the set argument -/
theorem weaknessInf_mono {Q : Type*} [Monoid Q] [CompleteLattice Q]
    (wf : WeightFunctionInf U Q) (H₁ H₂ : Set (U × U)) (h : H₁ ⊆ H₂) :
    weaknessInf wf H₁ ≤ weaknessInf wf H₂ := by
  unfold weaknessInf
  apply sSup_le_sSup
  intro q ⟨p, hp, hq⟩
  exact ⟨p, h hp, hq⟩

/-! ## Connection to Finitary Version

When U is Fintype, the infinitary definitions agree with the finitary ones
(via the natural embedding Finset → Set).
-/

/-- Convert a finitary SatisfyingSet to infinitary -/
def SatisfyingSetInf.ofFinitary {U : Type*} [Fintype U]
    (S : Mettapedia.Logic.PLNFirstOrder.SatisfyingSet U) : SatisfyingSetInf U :=
  ⟨S.pred⟩

/-- Convert a finitary WeightFunction to infinitary -/
def WeightFunctionInf.ofFinitary {U : Type*} [Fintype U] {Q : Type*} [Monoid Q]
    (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U Q) : WeightFunctionInf U Q :=
  ⟨wf.μ⟩

/-! ## Summary

### What This File Provides

1. **Infinitary weakness**: `weaknessInf` over arbitrary `Set (U × U)`
2. **Infinitary SatisfyingSet**: No `[Fintype U]` constraint
3. **Infinitary quantifiers**: `forAllEvalInf`, `thereExistsEvalInf`
4. **Basic theorems**: Empty/constant cases, De Morgan, monotonicity

### Significance

This allows PLN to reason about:
- Infinite domains (ℕ, ℝ, function spaces, etc.)
- True first-order semantics (not just propositional collapse)
- Properties that require infinite structures (compactness, categoricity, etc.)

### What's NOT Here (Future Work)

1. **Measure-theoretic integration**: For probability measures on infinite domains
2. **Connection to Foundation's FO model theory**: Would need to relate to `model_theory.basic`
3. **Completeness theorems**: For infinitary PLN proof calculus
4. **L_{ω1,ω} syntax**: Infinitary connectives (countable conjunctions/disjunctions)
-/

end Mettapedia.Logic.PLNFirstOrder.Infinite
