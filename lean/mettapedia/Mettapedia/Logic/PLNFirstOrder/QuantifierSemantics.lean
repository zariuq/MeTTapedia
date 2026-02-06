import Mettapedia.Logic.PLNFirstOrder.SatisfyingSet

/-!
# Quantifier Semantics via Weakness

This file defines the **semantic evaluation** of PLN quantifiers via Goertzel's weakness theory.

## Key Insight

**Quantifiers = Weakness of Diagonal Relation**

For predicate P : U → Evidence:
- ForAll($X : P($X)) = weakness({(u,v) | P(u) ∧ P(v)})
- ThereExists($X : P($X)) = dual of weakness (via De Morgan)

**Interpretation**:
- High weakness = many satisfying pairs = general/weak statement
- Low weakness = few satisfying pairs = specific/strong statement

This gives PLN's **third-order probability** interpretation:
P(∀x : P(x)) = probability that a random pair (u,v) both satisfies P

## References

- Goertzel, "Weakness and Its Quantale"
- Plan file (hashed-baking-bumblebee.md)
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open scoped ENNReal

variable {U : Type*} [Fintype U]

/-! ## Universal Quantifier Evaluation -/

/-- Evaluate ∀x : P(x) via weakness of the diagonal relation.

The diagonal consists of all pairs (u,v) where both u and v satisfy P.
The weakness of this diagonal gives the "generality" of the universal statement.

**Third-order probability interpretation**:
This computes the probability that a random pair (u,v), weighted by μ,
both satisfies the predicate P. -/
noncomputable def forAllEval
    (S : SatisfyingSet U)
    (μ : WeightFunction U Evidence) : Evidence :=
  weakness μ (SatisfyingSet.diagonal S)

/-! ## Typicality Quantifier Aliases -/

/-- Alias emphasizing the **PLN/typicality** reading of the universal quantifier. -/
noncomputable def forAllEvalTypical
    (S : SatisfyingSet U)
    (μ : WeightFunction U Evidence) : Evidence :=
  forAllEval S μ

/-! ## Existential Quantifier Evaluation -/

/-- Negation on SatisfyingSet: pointwise Heyting complement -/
noncomputable def SatisfyingSet.neg (S : SatisfyingSet U) : SatisfyingSet U :=
  ⟨fun u => Evidence.compl (S.pred u)⟩

/-- Evaluate ∃x : P(x) via De Morgan: ∃x : P(x) = ¬(∀x : ¬P(x))

This uses the Heyting algebra structure of Evidence:
1. Negate the predicate pointwise: ¬P = λu. compl(P(u))
2. Evaluate ∀x : ¬P(x) via weakness
3. Take Heyting complement of the result

Note: Evidence is a Heyting algebra, not Boolean. So ¬¬e ≠ e in general.
This is correct for PLN's paraconsistent logic (p-bits). -/
noncomputable def thereExistsEval
    (S : SatisfyingSet U)
    (μ : WeightFunction U Evidence) : Evidence :=
  Evidence.compl (forAllEval (SatisfyingSet.neg S) μ)

/-! ## Typicality Quantifier Aliases -/

/-- Alias emphasizing the **PLN/typicality** reading of the existential quantifier. -/
noncomputable def thereExistsEvalTypical
    (S : SatisfyingSet U)
    (μ : WeightFunction U Evidence) : Evidence :=
  thereExistsEval S μ

/-! ## Extensional (Meet/Join) Quantifier Views -/

/-- **Extensional ∀**: meet (inf) of all pointwise evidences.

This treats `S.pred u` as the truth value at each individual and aggregates
by lattice meet, aligning with a classical “all individuals satisfy” reading
inside the Evidence lattice. -/
noncomputable def forAllEvalExt
    (S : SatisfyingSet U) : Evidence :=
  sInf { e | ∃ u : U, e = S.pred u }

/-- **Extensional ∃**: join (sup) of all pointwise evidences.

This treats `S.pred u` as the truth value at each individual and aggregates
by lattice join, aligning with a classical “some individual satisfies” reading
inside the Evidence lattice. -/
noncomputable def thereExistsEvalExt
    (S : SatisfyingSet U) : Evidence :=
  sSup { e | ∃ u : U, e = S.pred u }

/-! ## Basic Properties -/

/-- ForAll evaluation for constantTrue predicate gives supremum of all pairs -/
theorem forAllEval_constantTrue (μ : WeightFunction U Evidence) :
    forAllEval SatisfyingSet.constantTrue μ =
    sSup { e | ∃ (u : U) (v : U), e = μ.μ u * μ.μ v } := by
  unfold forAllEval weakness
  rw [SatisfyingSet.diagonal_constantTrue]
  simp [Set.setOf_exists]

/-- ForAll evaluation for constantFalse predicate gives bottom -/
theorem forAllEval_constantFalse (μ : WeightFunction U Evidence) :
    forAllEval SatisfyingSet.constantFalse μ = ⊥ := by
  unfold forAllEval weakness
  rw [SatisfyingSet.diagonal_constantFalse]
  -- weakness μ ∅ = sSup { μ u * μ v | (u,v) ∈ ∅ } = sSup ∅ = ⊥
  simp [Set.setOf_false, sSup_empty]

/-! ## Well-Definedness -/

/-- ForAll evaluation is well-defined: the result is always in Evidence -/
theorem forAllEval_wellDefined (S : SatisfyingSet U) (μ : WeightFunction U Evidence) :
    ∃ e : Evidence, forAllEval S μ = e :=
  ⟨forAllEval S μ, rfl⟩

end Mettapedia.Logic.PLNFirstOrder
