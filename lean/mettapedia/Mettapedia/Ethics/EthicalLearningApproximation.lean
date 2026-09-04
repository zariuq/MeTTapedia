import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Approximate Ethical Learning and Decision Margins

Universal approximation results can help a virtue learner imitate an ethical
score or policy, but approximation of scores does not by itself preserve the
chosen action.  The missing condition is a decision margin.

This module proves the reusable margin theorem.  If the ethically preferred
action beats every alternative by more than twice the uniform approximation
error, then the learned score has the same unique maximizer.  A two-action
counterexample shows that no such conclusion is available at a tie.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.EthicalLearningApproximation

universe uAction

/-- Uniform score approximation restricted to the currently available
actions. -/
def UniformlyApproximatesOn
    {Action : Type uAction} (options : Set Action)
    (trueScore learnedScore : Action → ℝ) (error : ℝ) : Prop :=
  ∀ action, action ∈ options →
    |learnedScore action - trueScore action| ≤ error

/-- `chosen` belongs to the choice set and beats every distinct alternative
by at least `margin` under the true score. -/
def HasDecisionMargin
    {Action : Type uAction} (options : Set Action)
    (trueScore : Action → ℝ) (chosen : Action) (margin : ℝ) : Prop :=
  chosen ∈ options ∧
    ∀ alternative, alternative ∈ options → alternative ≠ chosen →
      trueScore alternative + margin ≤ trueScore chosen

/-- A uniform approximation preserves a unique maximizing action whenever the
true decision margin exceeds twice the approximation error. -/
theorem unique_maximizer_preserved_of_error_lt_half_margin
    {Action : Type uAction} {options : Set Action}
    {trueScore learnedScore : Action → ℝ}
    {chosen : Action} {margin error : ℝ}
    (margin_bound : 2 * error < margin)
    (approximates : UniformlyApproximatesOn options trueScore learnedScore error)
    (separated : HasDecisionMargin options trueScore chosen margin) :
    ∀ alternative, alternative ∈ options → alternative ≠ chosen →
      learnedScore alternative < learnedScore chosen := by
  intro alternative available different
  have chosenAvailable : chosen ∈ options := separated.1
  have alternativeError := abs_le.mp (approximates alternative available)
  have chosenError := abs_le.mp (approximates chosen chosenAvailable)
  have trueGap := separated.2 alternative available different
  have alternativeUpper :
      learnedScore alternative ≤ trueScore alternative + error := by
    linarith [alternativeError.2]
  have chosenLower :
      trueScore chosen - error ≤ learnedScore chosen := by
    linarith [chosenError.1]
  linarith

/-- The preserved strict maximizer is in particular a weak maximizer on the
whole option set. -/
theorem maximizer_preserved_of_error_lt_half_margin
    {Action : Type uAction} {options : Set Action}
    {trueScore learnedScore : Action → ℝ}
    {chosen : Action} {margin error : ℝ}
    (margin_bound : 2 * error < margin)
    (approximates : UniformlyApproximatesOn options trueScore learnedScore error)
    (separated : HasDecisionMargin options trueScore chosen margin) :
    ∀ alternative, alternative ∈ options →
      learnedScore alternative ≤ learnedScore chosen := by
  intro alternative available
  by_cases same : alternative = chosen
  · subst alternative
    exact le_rfl
  · exact le_of_lt
      (unique_maximizer_preserved_of_error_lt_half_margin
        margin_bound approximates separated
        alternative available same)

/-! ## Tie counterexample -/

inductive TwoAction : Type
  | left
  | right
  deriving DecidableEq, Repr

def tiedTrueScore : TwoAction → ℝ :=
  fun _ => 0

def tiedLearnedScore : TwoAction → ℝ
  | .left => 1
  | .right => -1

theorem tiedLearnedScore_uniform_error_one :
    UniformlyApproximatesOn Set.univ tiedTrueScore tiedLearnedScore 1 := by
  intro action available
  cases action <;> norm_num [tiedTrueScore, tiedLearnedScore]

/-- At a true tie, an arbitrarily admissible choice of `right` need not remain
maximal after a uniformly bounded approximation. -/
theorem no_choice_preservation_without_margin :
    ¬ (∀ alternative, alternative ∈ (Set.univ : Set TwoAction) →
      tiedLearnedScore alternative ≤ tiedLearnedScore .right) := by
  intro maximal
  have := maximal TwoAction.left (Set.mem_univ TwoAction.left)
  norm_num [tiedLearnedScore] at this

/-! ## Axiom audit -/

#print axioms unique_maximizer_preserved_of_error_lt_half_margin
#print axioms maximizer_preserved_of_error_lt_half_margin
#print axioms tiedLearnedScore_uniform_error_one
#print axioms no_choice_preservation_without_margin

end Mettapedia.Ethics.EthicalLearningApproximation
