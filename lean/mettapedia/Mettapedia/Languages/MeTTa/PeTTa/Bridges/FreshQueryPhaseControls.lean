import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryPhaseSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PreparedEffectfulQuery

/-! Authored phases, dynamic inner reads, and false-quiescence controls. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryPhaseSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval NamedSpaces SpaceSemantics

def app (name : String) (fields : List Atom) : Atom := .expression (.symbol name :: fields)
def fact (name : String) (value : Atom) : Atom := app name [value]
def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def seed : Atom := .symbol "seed"
def caller : Subst := [("out", .symbol "&self")]
def program : Program := {equations := [], declarations := []}
def first : Schema := ⟨[(.self, fact "p" (.var "x"))], fact "q" (.var "x")⟩
def second : Schema := ⟨[(.self, fact "q" (.var "x"))], fact "r" (.var "x")⟩
def before : Effects.State := Store.new [fact "p" a, fact "p" a] []
def after : Effects.State := Store.new [fact "p" a, fact "p" a, fact "q" a, fact "r" a] []

theorem complete_phase_adds_two_rows : run .self caller [first, second] before = some (after, 2) := by
  cbv

theorem repeated_phase_is_quiet : run .self caller [first, second] after = some (after, 0) := by
  cbv

theorem source_phase_returns_two :
    PureReturns program caller before (source "out" "payload" [first, second]) after (.grounded (.int 2)) :=
  source_returns program "out" "payload" .self caller [first, second] before after 2
    (by decide) (by decide +kernel) ⟨rfl, rfl⟩ complete_phase_adds_two_rows

theorem source_repeated_phase_returns_zero :
    PureReturns program caller after (source "out" "payload" [first, second]) after (.grounded (.int 0)) :=
  source_returns program "out" "payload" .self caller [first, second] after after 0
    (by decide) (by decide +kernel) ⟨rfl, rfl⟩ repeated_phase_is_quiet

theorem all_visited_schemas_saturated :
    ∀ schema ∈ [first, second], FreshNestedQuerySource.SaturatedAt after .self schema.template schema.legs caller :=
  ((zero_iff_saturated .self caller [first, second] after after).mp repeated_phase_is_quiet).2

theorem duplicate_inputs_remain_occurrences :
    before.core.count (fact "p" a) = 2 ∧ after.core.count (fact "p" a) = 2 ∧
      after.core.length = before.core.length + 2 := by decide +kernel

theorem unvisited_rule_can_still_add_rows :
    run .self caller [second] before = some (before, 0) ∧
      run .self caller [first, second] before = some (after, 2) := by
  exact ⟨by cbv, complete_phase_adds_two_rows⟩

def nested : Schema := ⟨[(.self, fact "step" (.var "x")), (.self, fact "cell" (.var "y"))],
  fact "cell" (app "pair" [.var "x", .var "y"])⟩
def startRows : List Atom := [fact "step" a, fact "step" b, fact "cell" seed]
def nestedBefore : Effects.State := Store.new startRows []
def newA : Atom := fact "cell" (app "pair" [a, seed])
def newB : Atom := fact "cell" (app "pair" [b, seed])
def newBA : Atom := fact "cell" (app "pair" [b, app "pair" [a, seed]])
def nestedAfter : Effects.State := Store.new (startRows ++ [newA, newB, newBA]) []

theorem dynamic_inner_read_sees_prior_insertion :
    run .self caller [nested] nestedBefore = some (nestedAfter, 3) := by cbv

theorem dynamic_nested_source_returns_three :
    PureReturns program caller nestedBefore (source "out" "payload" [nested]) nestedAfter (.grounded (.int 3)) :=
  source_returns program "out" "payload" .self caller [nested] nestedBefore nestedAfter 3
    (by decide) (by decide +kernel) ⟨rfl, rfl⟩ dynamic_inner_read_sees_prior_insertion

def frozenLegs : List PreparedEffectfulQuery.Leg :=
  [⟨.self, fact "step" (.var "x"), startRows⟩, ⟨.self, fact "cell" (.var "y"), startRows⟩]
def frozenAfter : Effects.State := Store.new (startRows ++ [newA, newB]) []

theorem frozen_worker_loses_one_fresh_result :
    PreparedEffectfulQuery.run (FreshQueryMaterialization.emit .self nested.template) frozenLegs caller nestedBefore =
      some (frozenAfter, [Effects.boolean true, Effects.boolean true]) := by cbv

theorem frozen_world_differs : frozenAfter ≠ nestedAfter := by
  intro same
  have sizes := congrArg (fun state : Effects.State => state.core.length) same
  contradiction

theorem initial_frozen_reads_are_valid : PreparedEffectfulQuery.Valid frozenLegs nestedBefore :=
  (PreparedEffectfulQuery.prepare_exact nestedBefore nested.legs frozenLegs (by rfl)).2

theorem later_frozen_reads_are_invalid : ¬ PreparedEffectfulQuery.Valid frozenLegs nestedAfter := by
  intro valid
  have view := valid ⟨.self, fact "cell" (.var "y"), startRows⟩ (by simp [frozenLegs]) caller
  have mismatch : QueryReadStability.view nestedAfter .self caller (fact "cell" (.var "y")) ≠
      some (EffectfulQuerySource.choices caller (fact "cell" (.var "y")) startRows) := by decide +kernel
  exact mismatch view

def inaccessible : Schema := ⟨[(.privateSpace 0, fact "p" (.var "x"))], fact "q" (.var "x")⟩
def skippedInner : Schema := ⟨[(.self, fact "absent" (.var "x")),
  (.privateSpace 0, fact "p" (.var "y"))], fact "q" (.var "x")⟩

theorem unavailable_read_is_not_quiescence : run .self caller [inaccessible] before = none := rfl

theorem unreached_read_needs_no_access : run .self caller [skippedInner] before = some (before, 0) := by
  cbv

theorem late_failure_does_not_certify_rollback :
    run .self caller [first, inaccessible] before = none ∧
      run .self caller [first] before = some (Store.new [fact "p" a, fact "p" a, fact "q" a] [], 1) := by
  exact ⟨by cbv, by cbv⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryPhaseSource.Controls
