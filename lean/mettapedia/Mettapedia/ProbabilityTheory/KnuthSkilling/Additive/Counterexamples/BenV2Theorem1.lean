import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.SemidirectNoSeparation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples

open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
# A sanity check against an *over-weak* reading of Goertzel v2 “Theorem 1”

Ben Goertzel’s `Foundations-of-inference-new-proofs_v2.pdf` (Theorem 1, algebraic form) is a
high-level statement about when an ordered associative combination operation should admit a
regrading into an additive commutative cancellative structure.

This file does **not** aim to refute Goertzel’s actual intended theorem. Instead, it records a
minimal counterexample to the *too-weak* hypothesis bundle:

> “associative + strictly monotone in each argument (on a linear order)”

alone does **not** force commutativity: there are noncommutative associative operations with
strict monotonicity in both arguments.

Therefore, any theorem in this direction needs additional hypotheses (e.g. cancellation laws,
solvability, separation/Archimedean conditions, or a construction of a commutative quotient).

We reuse the semidirect model built in `SemidirectNoSeparation.lean`.
-/

theorem exists_assoc_strictMono_noncomm :
    ∃ (S : Type) (_instOrd : LinearOrder S) (op : S → S → S),
      (∀ z, StrictMono fun x => op x z) ∧
      (∀ z, StrictMono fun y => op z y) ∧
      (∀ x y z, op (op x y) z = op x (op y z)) ∧
      (∃ x y, op x y ≠ op y x) := by
  classical
  refine ⟨SD, inferInstance, SD.op, SD.op_strictMono_left, SD.op_strictMono_right, SD.op_assoc, ?_⟩
  refine ⟨SD.exX, SD.exY, ?_⟩
  -- `SD.op_not_comm` is stated for the `KnuthSkillingAlgebra.op` instance, but this
  -- instance is definitionally `SD.op`.
  simpa [KnuthSkillingAlgebraBase.op, SD.op] using SD.op_not_comm

/-- A tiny meta-lemma: an order-reflecting additive regrading forces commutativity. -/
theorem commutative_of_representation
    {S : Type*} [LinearOrder S] (op : S → S → S)
    (Θ : S → ℝ)
    (horder : ∀ x y, x ≤ y ↔ Θ x ≤ Θ y)
    (hadd : ∀ x y, Θ (op x y) = Θ x + Θ y) :
    ∀ x y, op x y = op y x := by
  intro x y
  -- Compare via Θ and use `horder` to reflect back to `≤`.
  have hle : op x y ≤ op y x := (horder _ _).2 <| by
    -- Θ(op x y) = Θ x + Θ y = Θ y + Θ x = Θ(op y x)
    simp [hadd, add_comm]
  have hge : op y x ≤ op x y := (horder _ _).2 <| by
    simp [hadd, add_comm]
  exact le_antisymm hle hge

/-- Ben/Goertzel v2 (Theorem 1) cannot hold under *only* the monotone associativity axioms.

This is a concrete way to express the mismatch: if the conclusion provided a global additive
regrading `Θ : SD → ℝ`, then the operation would be commutative, contradicting `SD.op_not_comm`.
-/
theorem no_additive_regrading_for_SD :
    ¬ (∃ (Θ : SD → ℝ),
        (∀ x y : SD, x ≤ y ↔ Θ x ≤ Θ y) ∧
        (∀ x y : SD, Θ (op x y) = Θ x + Θ y)) := by
  rintro ⟨Θ, horder, hadd⟩
  have hcomm : ∀ x y : SD, op x y = op y x := commutative_of_representation op Θ horder hadd
  exact SD.op_not_comm (hcomm SD.exX SD.exY)

/-- Any claim that `KnuthSkillingAlgebra` alone forces commutativity is false. -/
theorem not_forall_knuthskilling_comm :
    ¬ (∀ (α : Type) (_ : KnuthSkillingAlgebra α), ∀ x y : α, op x y = op y x) := by
  intro h
  -- Apply the claim to the concrete noncommutative `KnuthSkillingAlgebra` instance `SD`.
  have hSD : ∀ x y : SD, op x y = op y x := h SD (inferInstance : KnuthSkillingAlgebra SD)
  exact SD.op_not_comm (hSD SD.exX SD.exY)

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples
