import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.OriginCards
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.Readouts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Closure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Exec

/-!
# Two actual firings, four held-origin runs, and live-rule boundaries

The ground program takes a `1` and makes a `2`. Two rows are fired in a
specified order, with both openings and all occurrence identities fixed.
Two persistent copies of the rule give four actual runs over that base run.
Captured knowledge and linear rule consumption are separate candidate
behaviours; they are not covered by the persistent projection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Controls

open RuleSyntax RuleSyntax.RuleOccurrences Origins
open OneFrame (Terms frames ext)
open Derived (link)
open MeTTaCalculus.OccurrenceCommits (fire)

private abbrev X := frames (Closed.action Nat)
private abbrev E := ext (Closed.action Nat)
private abbrev Q : Program (Terms Nat) := {link 1 2}
private abbrev P : Program (Terms Nat) := ∅
private def labels (_ : Fin 2) : Rule (Terms Nat) := link 1 2
private def zone (_ : Fin 2) : Unit := ()

def start : State (Terms Nat) Nat := ⟨PUnit.unit, [], {0, 1}, fun _ => 1⟩

def first : Firing Nat E (P ∪ Q) start.frame :=
  ⟨link 1 2, Or.inr rfl, PUnit.unit, PUnit.unit, ⟨[0], [], [2]⟩, []⟩

theorem first_admitted : first.Admits X start := by
  refine ⟨⟨?_, List.nodup_singleton 0, List.nodup_singleton 2, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro _ _ _
    exact ⟨PUnit.unit, fun _ _ => rfl, fun _ _ => rfl⟩
  · apply enabled_of <;> simp [first, start]
  · refine ⟨PUnit.unit, PUnit.unit, fun equation inside => ?_⟩
    have same : equation ∈ [((1 : Nat), 1)] := inside
    obtain rfl := List.mem_singleton.mp same
    rfl
  · intro _ _ _
    exact ⟨fun _ inside => absurd inside List.not_mem_nil,
      fun _ inside => absurd inside List.not_mem_nil⟩

def second : Firing Nat E (P ∪ Q) (first.result X start).frame :=
  ⟨link 1 2, Or.inr rfl, PUnit.unit, PUnit.unit, ⟨[1], [], [3]⟩, []⟩

theorem second_admitted : second.Admits X (first.result X start) := by
  refine ⟨⟨?_, List.nodup_singleton 1, List.nodup_singleton 3, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro _ _ _
    exact ⟨PUnit.unit, fun _ _ => rfl, fun _ _ => rfl⟩
  · apply enabled_of <;> simp [second, first, start, Firing.result, fire, Selection.commit]
  · refine ⟨PUnit.unit, PUnit.unit, fun equation inside => ?_⟩
    have same : equation ∈ [((1 : Nat), 1), (1, 1)] := inside
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at same
    subst equation
    rfl
  · intro _ _ _
    exact ⟨fun _ inside => absurd inside List.not_mem_nil,
      fun _ inside => absurd inside List.not_mem_nil⟩

def baseExecution : (baseEvents X E (P := P) (Q := Q)).Execution 2 start :=
  ⟨⟨first, first_admitted⟩, ⟨⟨second, second_admitted⟩, PUnit.unit⟩⟩

def baseRun : BaseRuns X E (P := P) (Q := Q) start 2 :=
  (step X Nat E (P ∪ Q)).toStep.countedExecutionRunEquiv
    (fun {_} firing => (firing.rule, firing.selection)) start 2 baseExecution

theorem offered_twice : Offers Q (Finset.univ : Finset (Fin 2)) labels := by
  intro rule
  constructor
  · intro member
    exact ⟨0, Finset.mem_univ _, (Set.mem_singleton_iff.mp member).symm⟩
  · rintro ⟨_, _, same⟩
    exact Set.mem_singleton_iff.mpr same.symm

def twoUses (state : State (Terms Nat) Nat)
    (firing : (baseEvents X E (P := P) (Q := Q)).Choice state) :
    Uses X E (ids := Finset.univ) (code := labels) zone state firing ≃ Fin 2 := by
  have same : firing.val.rule = link 1 2 := by
    rcases firing.val.member with impossible | member
    · exact (Set.notMem_empty _ impossible).elim
    · exact Set.mem_singleton_iff.mp member
  refine (heldUsesEquiv X E zone state firing).trans ?_
  refine ⟨Subtype.val, fun identity => ⟨identity, Finset.mem_univ _, same.symm⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem two_uses (state : State (Terms Nat) Nat)
    (firing : (baseEvents X E (P := P) (Q := Q)).Choice state) :
    Nat.card (Uses X E (ids := Finset.univ) (code := labels) zone state firing) = 2 := by
  rw [Nat.card_congr (twoUses state firing)]
  exact Nat.card_fin 2

theorem four_actual_runs :
    Nat.card {run : HeldRuns X E (P := P) (ids := Finset.univ) (code := labels) zone start 2 //
      projectRun X E zone offered_twice start 2 run = baseRun} = 4 := by
  rw [run_fibre_card]
  rw [ways_constant X E zone 2 two_uses]
  decide

theorem same_row_result : baseRun.val.last.label 2 = 2 ∧ baseRun.val.last.label 3 = 2 := by
  constructor <;> rfl

def decorations (firstOrigin secondOrigin : Fin 2) :
    Decorations X E (ids := Finset.univ) (code := labels) zone baseExecution :=
  ⟨⟨.held firstOrigin, Finset.mem_univ _, rfl⟩,
    ⟨⟨.held secondOrigin, Finset.mem_univ _, rfl⟩, PUnit.unit⟩⟩

noncomputable def selectedRun (firstOrigin secondOrigin : Fin 2) :
    HeldRuns X E (P := P) (ids := Finset.univ) (code := labels) zone start 2 :=
  liftOrigins X E zone offered_twice baseExecution (decorations firstOrigin secondOrigin)

theorem selected_run_projects (firstOrigin secondOrigin : Fin 2) :
    projectRun X E zone offered_twice start 2 (selectedRun firstOrigin secondOrigin) = baseRun :=
  project_liftOrigins X E zone offered_twice baseExecution _

theorem selected_run_origin_word (firstOrigin secondOrigin : Fin 2) :
    (selectedRun firstOrigin secondOrigin).val.word.map (fun entry => entry.2.use) =
      [.held firstOrigin, .held secondOrigin] :=
  liftOrigins_word X E zone offered_twice baseExecution _

theorem four_origin_words : Function.Injective (fun pair : Fin 2 × Fin 2 => selectedRun pair.1 pair.2) := by
  intro firstPair secondPair same
  have words := congrArg (fun run : HeldRuns X E (P := P) (ids := Finset.univ) (code := labels) zone start 2 =>
    run.val.word.map (fun entry => entry.2.use)) same
  rw [selected_run_origin_word, selected_run_origin_word] at words
  have heads := List.cons.inj words
  exact Prod.ext (Use.held.inj heads.1) (Use.held.inj (List.cons.inj heads.2).1)

theorem captured_binding_is_observable :
    (Closure.watchFiring [(Examples.x, Examples.c 5)]).Admits Examples.X (∅ : Set Unit) ∧
      ¬ (Closure.watchFiring []).Admits Examples.X (∅ : Set Unit) :=
  ⟨Closure.bound_admitted, Closure.unbound_refused⟩

def consumedRun :
    (rstep Examples.X Nat Nat Examples.E Exec.codes (∅ : Set Exec.Code)).toStep.Run Exec.factState :=
  .cons Exec.onceFiring Exec.once_admitted (.nil _)

theorem consumed_run_changes_table : consumedRun.word.length = 1 ∧ consumedRun.last.rules = ∅ :=
  ⟨rfl, Exec.once_taken⟩

theorem consumed_run_stuck :
    ¬ ∃ firing, (rstep Examples.X Nat Nat Examples.E Exec.codes (∅ : Set Exec.Code)).toStep.Admits
      (s := consumedRun.last) firing := by
  rintro ⟨firing, admitted⟩
  exact Exec.once_then_stuck firing admitted

def regeneratedRun :
    (rstep Examples.X Nat Nat Examples.E Exec.codes (∅ : Set Exec.Code)).toStep.Run Exec.loopState :=
  .cons Exec.loopFiring Exec.loop_admitted
    (.cons Exec.loopAgain Exec.loop_again_admitted (.nil _))

theorem made_occurrence_runs_next :
    regeneratedRun.word.map (fun entry => entry.2.use) = [.held 0, .held 5] ∧
      regeneratedRun.last.held 6 = ⟨Exec.Code.loop, [], .linear, ()⟩ := ⟨rfl, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Controls
