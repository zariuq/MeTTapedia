import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventEvaluation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Reindex
import Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

/-! # Executable controls for admission, budgets and handler observations

The evaluator consumes the same constraint-store effect as the authored
presentation. Its selected candidate is initially admitted, then refused
after the first successful tell. An unresolved strategy is kept distinct
from that refutation and from a zero budget. The existing contextual handler
controls supply the independent shared-state versus isolated-state examples.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step.Evaluation.Controls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Controls

def program : Step frame Nat Store (fun _ => Unit) := Step.ofEffect effect permission

def tryTell (state : Store) : Attempt program state :=
  if duplicate : (true, false) ∈ state then
    .refused () (fun ⟨_, allowed⟩ => allowed duplicate)
  else .admitted () ⟨Presentation.Controls.prepares state (), duplicate⟩

def waitForWork (state : Store) : Attempt program state := .unresolved (some ())

theorem initially_permitted : program.Admits (s := []) () :=
  ⟨Presentation.Controls.prepares [] (), by simp [permission]⟩

theorem zero_budget_is_not_a_refutation :
    program.Admits (s := []) () ∧
      (evaluate program tryTell 0 []).run.word = [] ∧
      (evaluate program tryTell 0 []).halt = .budgetExhausted :=
  ⟨initially_permitted, rfl, rfl⟩

theorem one_attempt_commits_before_budget :
    (evaluate program tryTell 1 []).run.last = [(true, false)] ∧
      (evaluate program tryTell 1 []).run.word.length = 1 ∧
      (evaluate program tryTell 1 []).halt = .budgetExhausted := by
  simp [evaluate, tryTell, Step.Run.last, Step.Run.word, program, Step.ofEffect,
    effect, EffectCore.tell, EffectCore.storeAction, Step.result]

theorem second_attempt_is_refused :
    (evaluate program tryTell 2 []).run.last = [(true, false)] ∧
      ∃ firing refutation,
        (evaluate program tryTell 2 []).halt = .refused firing refutation := by
  simp [evaluate, tryTell, Step.Run.last, program, Step.ofEffect,
    effect, EffectCore.tell, EffectCore.storeAction, Step.result]
  exact ⟨(), by simp [permission]⟩

theorem unresolved_does_not_refute_valid_work :
    program.Admits (s := []) () ∧
      (evaluate program waitForWork 3 []).run.word = [] ∧
      (evaluate program waitForWork 3 []).halt = .unresolved (some ()) :=
  ⟨initially_permitted, rfl, rfl⟩

theorem completed_effect_is_retained :
    (evaluate program tryTell 2 []).run.word.length = 1 := by
  simp [evaluate, tryTell, Step.Run.word, program, Step.ofEffect,
    effect, EffectCore.tell, EffectCore.storeAction, Step.result]

/-- The two alternatives carry different observable labels and the same store effect. -/
def alternatives : Step frame Nat Store (fun _ => Bool) := program.reindex (fun _ => ())

def choose (label : Bool) (state : Store) : Attempt alternatives state :=
  match tryTell state with
  | .admitted _ allowed => .admitted label allowed
  | .refused _ refused => .refused label refused
  | .unresolved _ => .unresolved (some label)

def branch (label : Bool) : Result alternatives [] := evaluate alternatives (choose label) 1 []

def answers (result : Result alternatives []) : List Bool := result.run.word.map (·.2)

/-- Enumeration and commitment differ even though these programs contain no
operation inspecting an answer order. The label is simply the chosen candidate. -/
theorem enumeration_and_commitment_differ :
    ([branch true, branch false].flatMap answers = [true, false]) ∧
      answers (branch true) = [true] ∧
      [branch true, branch false].flatMap answers ≠ answers (branch true) := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step.Evaluation.Controls

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step.Evaluation.HandlerControls

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

/-- Existing handler implementations disagree on the actual answer lists. -/
theorem shared_and_isolated_change_answers :
    (runWorlds Canary.twoIncrements 0).map WorldResult.answer ≠
      (runShared Canary.twoIncrements 0).answers := by
  rw [Canary.isolated_increments, Canary.shared_increments]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step.Evaluation.HandlerControls
