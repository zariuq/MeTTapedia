import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ParallelRunExchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.InterchangeTraceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectangleControls

/-!
# Complete native-run composition in the store-changing profile

Every pair of finite runs of the permissive tell profile has a local exchange
plan. The two resulting executions perform all input events. The same pair of
initial steps has no plan under duplicate refusal.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ParallelRunControls

open Presentation.Controls (Store)
open PublicationTransportControls
open InterchangeTraceControls (admitted)

abbrev P := program permissive
abbrev T := transport permissive

def crossing : ∀ {s : Store} (run : P.Run s) (g : Bool) (allowed : P.Admits g), T.Crossing run g allowed
  | _, .nil _, g, allowed => Transport.Crossing.nil (T := T) g allowed
  | _, .cons _ _ rest, g, _ => .cons (admitted _ _) (admitted _ g) (crossing rest g (admitted _ g))

def closings : ∀ {s : Store} {run : P.Run s} {g : Bool} {allowed : P.Admits g}
    (plan : T.Crossing run g allowed), plan.Closings
  | _, _, _, _, .nil _ _ => PUnit.unit
  | _, .cons _ _ _, _, _, .cons _ _ tail => ⟨⟨rfl⟩, closings tail⟩

theorem endpoint_eq {s : Store} {run : P.Run s} {g : Bool} {allowed : P.Admits g}
    (plan : T.Crossing run g allowed) (closed : plan.Closings) :
    (plan.exchangeWith closed).residualRun.last =
      P.result (plan.exchangeWith closed).residualFiring (plan.exchangeWith closed).residualAdmitted := by
  obtain ⟨⟨same⟩⟩ := (plan.exchangeWith closed).same_endpoint
  exact same

def plan : ∀ {s : Store} (left right : P.Run s), T.RunInterchangePlan left right
  | _, _, .nil _ => PUnit.unit
  | _, left, .cons g allowed right =>
      let head := crossing left g allowed
      let closed := closings head
      ⟨head, closed, ⟨endpoint_eq head closed⟩, plan (head.exchangeWith closed).residualRun right⟩

def exchange {s : Store} (left right : P.Run s) : T.ParallelExchange left right := (plan left right).exchange

theorem all_complete_runs_interchange {s : Store} (left right : P.Run s) :
    T.TraceEquiv s (right.append (exchange left right).afterRight)
      (left.append (exchange left right).afterLeft) := (exchange left right).interchange

theorem each_input_count_is_retained {s : Store} (left right : P.Run s) :
    (exchange left right).afterLeft.word.length = right.word.length ∧
      (exchange left right).afterRight.word.length = left.word.length :=
  ⟨(exchange left right).afterLeft_length, (exchange left right).afterRight_length⟩

theorem store_length : ∀ {s : Store} (run : P.Run s), run.last.length = s.length + run.word.length
  | _, .nil _ => by simp [Step.Run.last, Step.Run.word]
  | s, .cons f allowed rest => by
      have ih := store_length rest
      change rest.last.length = s.length + (rest.word.length + 1)
      change rest.last.length = (s ++ [(true, false)]).length + rest.word.length at ih
      simp only [List.length_append, List.length_singleton] at ih
      omega

theorem combined_store_changes {s : Store} (left right : P.Run s) :
    (left.append (exchange left right).afterLeft).last.length =
      s.length + (left.word.length + right.word.length) := by
  rw [store_length, (exchange left right).total_length]

abbrev Q := program strict
abbrev U := transport strict

theorem initial (label : Bool) : Q.Admits (s := ([] : Store)) label :=
  ExecutionRectangleControls.strict_initial_steps_admitted label

def once (label : Bool) : Q.Run ([] : Store) := .cons label (initial label) (.nil _)

theorem refused_pair_has_no_plan : ¬Nonempty (U.RunInterchangePlan (once false) (once true)) := by
  rintro ⟨both⟩
  change U.RunInterchangePlan (once false) (.cons true (initial true) (.nil _)) at both
  rw [Transport.RunInterchangePlan] at both
  obtain ⟨firstCrossing, _⟩ := both
  cases firstCrossing with
  | cons afterSecond _ _ => exact ExecutionRectangleControls.strict_rejects_second false afterSecond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ParallelRunControls
