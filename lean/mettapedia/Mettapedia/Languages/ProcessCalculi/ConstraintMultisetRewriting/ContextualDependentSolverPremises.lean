import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalChecking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConversionBudget
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualCategory

/-! # Premises for the contextual dependent solver -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace SolverPremises

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction
open ContextualDependentConversionBudget

/-- A normal form exists at the original abstraction and type. -/
abbrev HasNormalForms {Head L : Type} [UniverseLevel.LevelOrder L]
    (S : Setting Head L) : Prop :=
  ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code

/-- The executable returns evidence for each normality check it accepts. -/
abbrev NormalityCertifier {Head L : Type} [UniverseLevel.LevelOrder L]
    (S : Setting Head L) : Type :=
  ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term))

/-- The declaration relation is single-valued at each head. -/
abbrev UniqueHeadTyping {Head : Type} (rules : Rules Head) : Prop :=
  ∀ {head first second : Head},
    rules.headTyping head first → rules.headTyping head second → first = second

/-- A root evaluator that reports absence rules out every root step. -/
abbrev CompleteRootEvaluation {Head : Type} {rules : Rules Head}
    (root : RootEvaluator rules) : Prop :=
  ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ rules.computation.step term target

/-- An additional unit of fuel keeps each previously returned reduction. -/
abbrev StableReducer {Head : Type} {rules : Rules Head} (reducer : Reducer rules) : Prop :=
  ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
    Keeps (reducer fuel term) (reducer (fuel + 1) term)

/-- Each one-step retention proof composes along a larger fuel allowance. -/
theorem keeps_of_le {α : Type*} {run : Nat → Option α}
    (step : ∀ fuel, Keeps (run fuel) (run (fuel + 1)))
    {first last : Nat} (enough : first ≤ last) : Keeps (run first) (run last) := by
  intro result finished
  induction enough with
  | refl => exact finished
  | @step last _ ih => exact step last result ih

end SolverPremises
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
