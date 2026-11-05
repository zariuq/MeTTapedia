import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementEntry
import Mettapedia.Tools.KernelReflexivity

/-! Exact improvement, source dispatch, duplicate refusal and publication controls. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics NamedSpaces

def names : Names := ⟨"space", "vertex", "candidate", "current", "previous", "discard", by decide⟩
def distance (key value : Nat) : Atom := row "sd" (number key) (number value)
def before : Effects.State := Store.new [distance 0 10, distance 1 5] []
def after : Effects.State := Store.new [distance 1 5, distance 0 7] []
def equation : Equation := ⟨"improve", [.var names.space, .var names.vertex, .var names.candidate], source names "sd"⟩
def program : Program := {equations := [equation], declarations := []}

theorem strictly_better_replaces_and_returns_key : run names "sd" .self 0 7 before = some (after, [number 0]) := by
  kernel_reflexivity

theorem nonimprovement_returns_no_answer : run names "sd" .self 0 12 before = some (before, []) := by
  kernel_reflexivity

theorem equal_candidate_returns_no_answer : run names "sd" .self 0 10 before = some (before, []) := by
  kernel_reflexivity

theorem absent_key_inserts : run names "sd" .self 3 2 before =
    some (Store.new [distance 0 10, distance 1 5, distance 3 2] [], [number 3]) := by kernel_reflexivity

theorem actual_body_returns : Eval.Returns program (bindings names .self 0 7) before (source names "sd") after [number 0] :=
  returns names "sd" program .self 0 7 before after [number 0] strictly_better_replaces_and_returns_key

def caller : Subst := bindings names .self 0 7
theorem arguments : [names.space, names.vertex, names.candidate].map (fun name => applySubst caller (.var name)) =
    [Effects.handleValue .self, number 0, number 7] := rfl

def certificate : KeyedImprovementEntry.Certificate program "improve" names "sd" .self 0 7 :=
  (KeyedImprovementEntry.prepare program "improve" names "sd" .self 0 7).get (by decide +kernel)

theorem actual_authored_call_returns :
    Eval.Returns program caller before (KeyedImprovementEntry.call "improve" names) after [number 0] :=
  certificate.call_returns caller arguments before after [number 0] strictly_better_replaces_and_returns_key

def plan := KeyedImprovementEntry.region "improvement" certificate caller arguments

theorem accepted_call_commits_exact_observation :
    plan.attempt before = .committed (KeyedImprovementEntry.complete after [number 0]) := by kernel_reflexivity

def duplicate : Effects.State := Store.new [distance 0 10, distance 0 10] []

theorem duplicate_occurrences_are_not_a_single_slot : run names "sd" .self 0 7 duplicate = none := by kernel_reflexivity

theorem distinct_current_distances_refuse : run names "sd" .self 0 7 (Store.new [distance 0 10, distance 0 11] []) = none := by
  kernel_reflexivity

theorem duplicate_decline_restores_entrance : plan.attempt duplicate = .declined duplicate := by kernel_reflexivity

theorem duplicate_decline_uses_reference : plan.execute duplicate =
    PureCallPortfolio.sourceMeaning program caller (KeyedImprovementEntry.call "improve" names) duplicate :=
  KeyedImprovementEntry.execute_exact "improvement" certificate caller arguments duplicate

theorem duplicate_reference_is_not_an_improvement :
    Eval.run program 200 {state := duplicate, control := .evaluate caller (KeyedImprovementEntry.call "improve" names)} =
      .complete duplicate [] [] [] := by kernel_reflexivity

theorem negative_distance_refuses :
    run names "sd" .self 0 7 (Store.new [row "sd" (number 0) (.grounded (.int (-1)))] []) = none := by kernel_reflexivity

theorem boolean_distance_refuses :
    run names "sd" .self 0 7 (Store.new [row "sd" (number 0) (Effects.boolean true)] []) = none := by kernel_reflexivity

theorem relevant_open_row_refuses :
    run names "sd" .self 0 7 (Store.new [row "sd" (.var "v") (number 10)] []) = none := by kernel_reflexivity

theorem missing_space_is_not_absence : run names "sd" (.privateSpace 0) 0 7 before = none := by kernel_reflexivity

theorem declaration_head_refuses : run names "=" .self 0 7 before = none := by kernel_reflexivity

def withEquation : Effects.State := Store.new [distance 0 10, equation.toAtom] []

theorem unrelated_open_equation_is_preserved : run names "sd" .self 0 7 withEquation =
    some (Store.new [equation.toAtom, distance 0 7] [], [number 0]) := by kernel_reflexivity

def extra : Equation := ⟨"improve", equation.arguments, Effects.boolean false⟩

theorem productive_extra_clause_refuses :
    (KeyedImprovementEntry.prepare {program with equations := [equation, extra]} "improve" names "sd" .self 0 7).isNone = true := by
  decide +kernel

def unmatched : Equation := ⟨"improve", [number 7, number 0, number 7], .symbol "unreachable"⟩

theorem unmatchable_extra_clause_is_admitted :
    (KeyedImprovementEntry.prepare {program with equations := [unmatched, equation]} "improve" names "sd" .self 0 7).isSome = true := by
  decide +kernel

def renamed : Names := ⟨"destination", "node", "proposed", "found", "old", "written", by decide⟩
def renamedEquation : Equation := ⟨"lower-renamed", [.var renamed.space, .var renamed.vertex, .var renamed.candidate], source renamed "distance"⟩
def renamedProgram : Program := {equations := [renamedEquation], declarations := []}

theorem renamed_source_is_admitted :
    (KeyedImprovementEntry.prepare renamedProgram "lower-renamed" renamed "distance" .self 6 3).isSome = true := by decide +kernel

theorem renamed_data_head_is_not_special :
    run renamed "distance" .self 6 3 (Store.new [row "distance" (number 6) (number 8)] []) =
      some (Store.new [row "distance" (number 6) (number 3)] [], [number 6]) := by kernel_reflexivity

theorem exact_pages_decline :
    (KeyedImprovementEntry.classify .exactPage "improvement" program "improve" names "sd" .self 0 7 caller arguments).isNone = true := rfl

theorem intermediate_removal_is_visible :
    Effects.erase before .self (distance 0 10) = some (Store.new [distance 1 5] []) ∧
    (Store.new [distance 1 5] [] : Effects.State).read .self ≠ after.read .self := by
  constructor
  · kernel_reflexivity
  · decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementSource.Controls
