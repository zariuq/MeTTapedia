import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions

/-!
# Executed controls for the explicit call-time-choice instructions

Expected observations are specified independently as ordered value/trace
lists. They distinguish one shared suspension, independent suspensions,
repeated evaluation, inert code and residual activation. The original natural
semantics is unchanged and is connected by `source_iff_executable`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Controls

open CallTimeChoice

def observations : Control → Option (List (Outcome × List Nat))
  | .returned results [] => some (results.map fun result => (result.1,result.2.trace))
  | _ => none

def execute (P : Program) (fuel : Nat) (code : Comp) :=
  observations (runFuel P fuel (.task (.eval Store.empty [] code) []))

def pair (left right : Val Nat) : Val Nat := .app (.app (.sym 3) left) right
def pairExpression (left right : VExp) : VExp := .app (.app (.sym 3) left) right
def pick : Comp := .choose (.ret (.sym 1)) (.ret (.sym 2))
def twice : Comp := .seq (.force (.var 0)) (.seq (.force (.var 1)) (.ret (pairExpression (.var 1) (.var 0))))
def shared : Comp := .need pick twice
def repeated : Comp := .delay pick twice
def independent : Comp := .need pick (.need pick
  (.seq (.force (.var 0)) (.seq (.force (.var 2)) (.ret (pairExpression (.var 1) (.var 0))))))

theorem shared_choices_stay_correlated : execute [] 200 shared =
    some [(.ok (pair (.sym 1) (.sym 1)),[]),(.ok (pair (.sym 2) (.sym 2)),[])] := by
  decide +kernel

theorem independent_choices_stay_independent : execute [] 300 independent =
    some [(.ok (pair (.sym 1) (.sym 1)),[]),(.ok (pair (.sym 1) (.sym 2)),[]),
      (.ok (pair (.sym 2) (.sym 1)),[]),(.ok (pair (.sym 2) (.sym 2)),[])] := by
  decide +kernel

theorem ordinary_delay_repeats_the_choice : execute [] 300 repeated =
    some [(.ok (pair (.sym 1) (.sym 1)),[]),(.ok (pair (.sym 1) (.sym 2)),[]),
      (.ok (pair (.sym 2) (.sym 1)),[]),(.ok (pair (.sym 2) (.sym 2)),[])] := by
  decide +kernel

def effectful : Comp := .emit 9 (.ret (.sym 1))
theorem shared_effect_occurs_once : execute [] 200 (.need effectful twice) =
    some [(.ok (pair (.sym 1) (.sym 1)),[9])] := by decide +kernel
theorem repeated_effect_occurs_twice : execute [] 200 (.delay effectful twice) =
    some [(.ok (pair (.sym 1) (.sym 1)),[9,9])] := by decide +kernel

def loopProgram : Program := [⟨7,0,.call 7 []⟩]
theorem unused_recursive_work_is_not_forced :
    execute loopProgram 10 (.need (.call 7 []) (.ret (.sym 8))) = some [(.ok (.sym 8),[])] := by
  decide +kernel

theorem equal_alternatives_keep_two_occurrences :
    execute [] 20 (.choose (.ret (.sym 1)) (.ret (.sym 1))) =
      some [(.ok (.sym 1),[]),(.ok (.sym 1),[])] := by decide +kernel

theorem duplicate_equations_keep_program_order_and_multiplicity :
    execute [⟨4,0,.emit 1 (.ret (.sym 8))⟩,⟨4,0,.emit 2 (.ret (.sym 8))⟩,
      ⟨4,0,.emit 1 (.ret (.sym 8))⟩] 50 (.call 4 []) =
      some [(.ok (.sym 8),[1]),(.ok (.sym 8),[2]),(.ok (.sym 8),[1])] := by decide +kernel

theorem quotation_is_inert : execute [] 10 (.quote effectful) = some [(.ok (.code 0),[])] := by decide +kernel

theorem activation_runs_code_afresh_each_time :
    execute [] 100 (.seq (.quote effectful) (.seq (.run (.var 0)) (.run (.var 1)))) =
      some [(.ok (.sym 1),[9,9])] := by decide +kernel

theorem activating_noncode_returns_the_declared_residual :
    execute [] 10 (.run (.sym 8)) = some [(.ok (.app (.sym unquoteHead) (.sym 8)),[])] := by decide +kernel

theorem unfinished_work_is_not_an_empty_answer_list : execute [] 0 shared = none := rfl

theorem every_executed_observation_has_a_source_derivation (P : Program) (fuel : Nat) (code : Comp)
    (result : List (Outcome × List Nat)) (observed : execute P fuel code = some result) :
    ∃ results, Derives P (.eval Store.empty [] code) results ∧
      results.map (fun answer => (answer.1,answer.2.trace)) = result := by
  generalize reached : runFuel P fuel (.task (.eval Store.empty [] code) []) = state at observed
  cases state with
  | task goal stack => simp [execute, reached, observations] at observed
  | returned results stack =>
      cases stack with
      | cons frame rest => simp [execute, reached, observations] at observed
      | nil =>
          have exactResults : results.map (fun answer => (answer.1,answer.2.trace)) = result := by
            simpa only [execute, reached, observations, Option.some.injEq] using observed
          exact ⟨results, (source_iff_executable P _ results).mpr ⟨fuel,reached⟩, exactResults⟩

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Controls
