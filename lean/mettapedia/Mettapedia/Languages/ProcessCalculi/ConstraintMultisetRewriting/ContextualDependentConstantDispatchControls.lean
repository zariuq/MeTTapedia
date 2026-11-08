import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantDispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantPruningControls

/-!
# Actual queue recognition, orientation, and residual preservation

The dispatcher receives the declaration and typed equations, not a supplied
pruning shape or matching certificate. It recognizes the closed constraint,
handles reversed endpoints and a beta-redex endpoint, and carries skipped
equations into the smaller-metavariable context. Zero budget and unmatched
solvable equations remain residual.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantDispatch.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

abbrev setting := ContextualDependentConstantPruning.Controls.setting
abbrev base := ContextualDependentConstantPruning.Controls.base
abbrev whole := ContextualDependentConstantPruning.Controls.whole
abbrev source := extend base whole
abbrev previous := ContextualDependentConstantPruning.Controls.result

def candidate : Equation (TotalTerm source) := previous.closed.equations.get ⟨0, by decide +kernel⟩

def run (fuel : Nat) (problem : EquationStore (TotalTerm source)) := step (fun _ => (0 : Nat)) fuel whole problem
def direct := run 64 [candidate]
def reversed := run 64 [(candidate.2, candidate.1)]

def lambdaIndex {n : Nat} : Tower.Tm n → Option Nat
  | .lam (.var index) => some index.val
  | _ => none

theorem actual_recognition_finishes : direct.remaining = [] := by rfl'
theorem computed_fresh_metavariable_assignment : lambdaIndex (direct.answer.substitution 0) = some 1 := by rfl'
theorem actual_target_keeps_result_obligation : direct.target = ContextualDependentInversion.Controls.small := by rfl'
theorem reversed_input_finishes : reversed.remaining = [] := by rfl'

theorem principal_for_input_queue : (frames setting.levels).Principal [candidate] direct.answer :=
  direct.completed actual_recognition_finishes

def withSkipped := run 64 [ContextualDependentConstantPruning.Controls.side, candidate,
  ContextualDependentConstantPruning.Controls.side]

theorem skipped_and_following_equations_survive :
    withSkipped.remaining.map (fun equation => (lambdaIndex equation.1.2.code, lambdaIndex equation.2.2.code)) =
      [(some 1, some 0), (some 1, some 0)] := by rfl'

theorem zero_budget_keeps_original :
    run 0 [candidate] = Update.pending setting.levels [candidate] :=
  step_zero (fun _ => (0 : Nat)) whole [candidate]

def reflexive : Equation (TotalTerm source) := (Elimination.last base whole, Elimination.last base whole)
def unmatched := run 64 [reflexive]

theorem unmatched_equation_remains : unmatched = Update.pending setting.levels [reflexive] := by rfl'

theorem unmatched_equation_is_solvable : (frames setting.levels).Models (𝟙 source) [reflexive] := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  exact ((frames setting.levels).equivalence source).refl _

def identityJoin := (ExecutableTowerChoices.choices.join candidate.1.1.level candidate.1.1.level).get (by decide +kernel)

def identityType : TypeOver source :=
  ⟨.pi candidate.1.1.code (Presentation.rename wk candidate.1.1.code), identityJoin.val,
    (setting.levels.join_level identityJoin.property).1,
    .piForm candidate.1.1.formed candidate.1.1.universeWitness candidate.1.1.formed.weaken
      candidate.1.1.universeWitness identityJoin.property⟩

def delayed : Term source candidate.1.1 := by
  refine ⟨.app (.lam (.var 0)) candidate.1.2.code, ?_⟩
  have typed := Derivable.appElim (R := Tower.rules) (A := candidate.1.1.code)
    (B := Presentation.rename wk candidate.1.1.code)
    (.lamIntro identityType.formed identityType.universeWitness (.var 0)) candidate.1.2.typed
  rw [inst0_rename_wk] at typed
  exact typed

def delayedCandidate : Equation (TotalTerm source) := (⟨candidate.1.1, delayed⟩, candidate.2)
def delayedResult := run 64 [delayedCandidate]

theorem beta_variant_is_recognized : delayedResult.remaining = [] := by rfl'
theorem beta_variant_has_principal_answer : (frames setting.levels).Principal [delayedCandidate] delayedResult.answer :=
  delayedResult.completed beta_variant_is_recognized

theorem closed_solutions_preserved_separately :
    (∃ solution : empty Tower.rules ⟶ source, (frames setting.levels).Models solution [delayedCandidate]) ↔
      ∃ residual : empty Tower.rules ⟶ delayedResult.target, (frames setting.levels).Models residual delayedResult.remaining :=
  delayedResult.fixed_point_solutions_iff (empty Tower.rules)

def dependentWhole : TypeOver base :=
  ⟨.pi (.var 0) (.id (.var 1) (.var 0) (.var 0)), .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm (.var 0) (.sort _) (.idForm (.var 1) (.sort _) (.var 0) (.var 0)) (.sort _) (.sorts _ _)⟩

def dependentReflexive : Equation (TotalTerm (extend base dependentWhole)) :=
  (Elimination.last base dependentWhole, Elimination.last base dependentWhole)

theorem dependent_result_is_not_misclassified :
    step (fun _ => (0 : Nat)) 64 dependentWhole [dependentReflexive] =
      Update.pending setting.levels [dependentReflexive] := by rfl'

theorem dependent_result_still_has_a_solution :
    (frames setting.levels).Models (𝟙 (extend base dependentWhole)) [dependentReflexive] := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  exact ((frames setting.levels).equivalence _).refl _

end ContextualDependentConstantDispatch.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
