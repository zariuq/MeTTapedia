import Mettapedia.GSLT.Topos.PresheafFunctionPredicateConsumer

/-!
# Which judgments execute, which need proofs, and which are interpretation

This file reads the worked function-predicate consumer twice: once as a
programmer would, and once as a curriculum example for a proof assistant.
Both readings turn on the same pair of theorems.

## Executable

Membership in either property is decidable at every stage
(`decidableSource`, `decidableTarget`), and the examples below discharge
concrete instances by computation.  So "is this value in the property here?"
is a decision, and needs no proof from the user.

## Requiring a supplied proof

The entailment "this function carries the source property into the target" is
not that decision.  It quantifies over stages and over restrictions, and the
two theorems below show the gap is real rather than notional:

* `identity_carries_at_refined_stage` — the identity **does** carry the
  property at the refined stage, where the source already demands evenness;
* `identity_does_not_carry` (in the consumer) — and yet it is **not** an
  entailment, because the coarse stage demands nothing and offers an odd
  value.

`local_check_insufficient` states the two together.  For a programmer that
reads: *the check passed at the stage you tested, and the property is still
false.*  For a proof-assistant curriculum it reads: *this is why the judgment
quantifies over restrictions rather than over a single stage*, which is the
content a decision procedure at one stage cannot supply.

## Semantic interpretation

The exponential predicate itself is neither of the above.  It is a subobject
of the function object, and its stagewise reading (`mem_expPredicate`) is what
connects it to the two judgments: it says exactly which quantification the
supplied proof must establish.  It is interpretation, not a judgment to be
run or discharged.

## Scope

One artifact, two readings, deliberately not duplicated.  The example is
arithmetic because the rejection has to be recognisable; nothing here depends
on the choice of arithmetic.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.FunctionPredicateConsumer

/-! Executable: membership in either property is decidable at every stage. -/

instance decidableSource (U : Stageᵒᵖ) (n : ℕ) :
    Decidable (n ∈ sourcePred.obj U) := by
  unfold sourcePred
  by_cases h : U.unop = true
  · simp only [h, if_true]
    exact inferInstanceAs (Decidable (n % 2 = 0))
  · simp only [h]
    exact inferInstanceAs (Decidable True)

instance decidableTarget (U : Stageᵒᵖ) (n : ℕ) :
    Decidable (n ∈ targetPred.obj U) :=
  inferInstanceAs (Decidable (n % 2 = 0))

example : decide ((4 : ℕ) ∈ targetPred.obj (op true)) = true := by decide
example : decide ((3 : ℕ) ∈ targetPred.obj (op true)) = false := by decide

/-! Supplied proof: the entailment is not a decision at one stage. -/

/-- The identity DOES carry the property at the refined stage. -/
theorem identity_carries_at_refined_stage :
    ∀ n ∈ sourcePred.obj (op true),
      n ∈ (targetPred.preimage identityMap).obj (op true) := by
  intro n held
  have parity : n % 2 = 0 := held
  exact parity

/-- Yet it fails as an entailment, because the judgment ranges over the other
stage as well.  So passing the check at the stage one happens to test is not
sufficient: this judgment needs a proof, not a decision. -/
theorem local_check_insufficient :
    (∀ n ∈ sourcePred.obj (op true),
        n ∈ (targetPred.preimage identityMap).obj (op true)) ∧
      ¬ sourcePred ≤ targetPred.preimage identityMap :=
  ⟨identity_carries_at_refined_stage, identity_does_not_carry⟩
end Mettapedia.GSLT.Topos.FunctionPredicateConsumer

#print axioms Mettapedia.GSLT.Topos.FunctionPredicateConsumer.identity_carries_at_refined_stage
#print axioms Mettapedia.GSLT.Topos.FunctionPredicateConsumer.local_check_insufficient
