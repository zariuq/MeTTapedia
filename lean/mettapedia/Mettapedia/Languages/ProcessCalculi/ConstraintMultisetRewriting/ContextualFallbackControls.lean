import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFallback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingScheduler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingCodeControls

/-!
# Complete source fallback, guard rejection and late-arrival controls

The initial store has requests 1 and 2, but no request 3. A complete source
census permits a fallback that consumes request 1 and publishes request 3.
The publication keeps its entry census. An independently inserted request 3
invalidates emptiness and excludes fallback. A second control needs a real
guard countermodel even though its binding equations have a solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFallback.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualStandingEvents ContextualStandingScheduler
open ContextualSourceCensus
open ContextualRuleCode.Controls (DataOp dataSignature locals captures queries actor origin Tm symbol request declarationWorld entryModel)

local instance : DecidableEq dataSignature.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : dataSignature.Srt) : DecidableEq (dataSignature.Op result) := inferInstanceAs (DecidableEq DataOp)

def world : World dataSignature () Nat [] :=
  ⟨Nat, locals, inferInstance, declarationWorld, declarationWorld.present, []⟩

def primaryPlan : ContextualPublication.Plan (Tm actor) :=
  ⟨⟨[], [request (symbol 3)], [], [], [symbol 9]⟩, [true], rfl⟩
def primary : Request locals declarationWorld :=
  ⟨Nat, queries, inferInstance, primaryPlan, [91], by decide +kernel, rfl, by decide +kernel⟩

theorem complete_primary_rejection : primary.CertifiedEmpty := by
  have checked : ∀ chosen ∈ primary.candidates, primary.refutedB chosen 1 = true := by decide +kernel
  exact ⟨fun chosen present => .equations 1 ((primary.refutedB_iff chosen 1).mp (checked chosen present))⟩

theorem primary_patterned : ∀ chosen ∈ primary.candidates,
    ContextualPatternFragment.ProblemPattern (primary.information chosen) := by
  have checked : ∀ chosen ∈ primary.candidates,
      ContextualPatternFragment.checkProblem (primary.information chosen) = true := by decide +kernel
  exact fun chosen present => (ContextualPatternFragment.checkProblem_iff _).mp (checked chosen present)

def fallbackPlan : ContextualPublication.Plan (Tm actor) :=
  ⟨⟨[request (symbol 1)], [], [], [], [request (symbol 3)]⟩, [true], rfl⟩
def picked : Selection Nat := ⟨[0], [], [90]⟩

theorem fallback_source : Admitted queries [primary] fallbackPlan picked (before := world) := by
  refine ⟨?_, ?_⟩
  · intro alternative member
    have only := List.mem_singleton.mp member
    subst alternative
    exact complete_primary_rejection.no_source
  · refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      ⟨Nat, captures, entryModel, ?_⟩, ?_⟩
    · intro equation member
      change equation ∈ [_] at member
      have only := List.mem_singleton.mp member
      subst equation
      rfl
    · intro check member
      cases member

theorem the_actual_fallback_keeps_its_census_and_commits_once :
    ∃ compiled : Compiled queries [primary] fallbackPlan picked (before := world),
      compiled.fuel = 0 ∧ compiled.publication.negative = some compiled.census ∧
      Allowed (State.mk world ∅) (.commit world (.publish compiled.publication)) ∧
      compiled.publication.target.current.present = {1, 7, 90} := by
  have patterned : ∀ alternative ∈ ([primary] : List (Request locals declarationWorld)),
      ∀ chosen ∈ alternative.candidates,
        ContextualPatternFragment.ProblemPattern (alternative.information chosen) := by
    intro alternative member
    have only := List.mem_singleton.mp member
    subst alternative
    exact primary_patterned
  obtain ⟨compiled, budget⟩ := realize (before := world) queries [primary] fallbackPlan picked patterned fallback_source 0
  refine ⟨compiled, budget, rfl, ⟨rfl, ?_, trivial⟩, ?_⟩
  · change Disjoint picked.made.toFinset declarationWorld.present
    decide +kernel
  · rw [compiled.physical_result]
    decide +kernel

def lateRows (occurrence : Nat) : Row locals captures [] () :=
  if occurrence = 8 then ofStored locals captures (.shared (request (symbol 3)))
  else declarationWorld.rows occurrence
def lateState : ContextualConditionalExecution.State locals Nat [] () :=
  {declarationWorld with present := insert 8 declarationWorld.present, rows := lateRows}
def lateWorld : World dataSignature () Nat [] :=
  ⟨Nat, locals, inferInstance, lateState, lateState.present, []⟩
def latePrimary : Request locals lateState :=
  ⟨Nat, queries, inferInstance, primaryPlan, [91], by decide +kernel, rfl, by decide +kernel⟩

theorem an_arriving_primary_can_actually_fire : latePrimary.Enabled := by
  refine ⟨⟨[], [8], [91]⟩, ?_⟩
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, entryModel, ?_⟩, ?_⟩
  · intro equation member
    change equation ∈ [_] at member
    have only := List.mem_singleton.mp member
    subst equation
    rfl
  · intro check member
    cases member

theorem the_late_row_invalidates_emptiness : ¬ latePrimary.CertifiedEmpty :=
  fun complete => complete.no_source an_arriving_primary_can_actually_fire

theorem the_late_row_excludes_fallback :
    ¬ Nonempty (Compiled queries [latePrimary] fallbackPlan picked (before := lateWorld)) :=
  an_enabled_primary_excludes_fallback (before := lateWorld) queries [latePrimary] fallbackPlan picked latePrimary
    (List.mem_singleton_self _) an_arriving_primary_can_actually_fire

def firstCandidate : primary.Candidate := ⟨Fin.elim0, fun _ => 0⟩

theorem zero_budget_is_not_an_equation_census :
    ¬ (∀ chosen ∈ primary.candidates, primary.RefutedAt chosen 0) := by
  intro complete
  exact primary.zero_fuel_is_not_a_refutation firstCandidate
    (complete firstCandidate (by decide +kernel))

def guardPlan : ContextualPublication.Plan (Tm actor) :=
  ⟨⟨[], [request (symbol 1)], [], [.equal (symbol 1) (symbol 2)], [symbol 9]⟩, [true], rfl⟩
def guarded : Request locals declarationWorld :=
  ⟨Nat, queries, inferInstance, guardPlan, [91], by decide +kernel, rfl, by decide +kernel⟩
def guardCandidate : guarded.Candidate := ⟨Fin.elim0, fun _ => 0⟩

theorem guard_binding_model : ContextualResidual.Models entryModel (guarded.information guardCandidate) := by
  intro equation member
  change equation ∈ [_] at member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem guard_countermodel : guarded.Rejected guardCandidate := by
  refine .guard (.equal (symbol 1) (symbol 2)) (List.mem_singleton_self _) Nat captures entryModel guard_binding_model ?_
  intro equal
  have impossible : (1 : Nat) = 2 := ContextualRuleCode.Controls.symbol_injective equal
  omega

def guardPort : Fin guarded.plan.rule.read.length := ⟨0, by decide +kernel⟩

theorem all_guarded_candidates_are_rejected : guarded.CertifiedEmpty := by
  have options : ∀ chosen ∈ guarded.candidates,
      chosen.2 guardPort = 0 ∨ guarded.refutedB chosen 1 = true := by decide +kernel
  refine ⟨?_⟩
  intro chosen present
  rcases options chosen present with first | refuted
  · have same : chosen = guardCandidate := by
      apply Prod.ext
      · funext port
        exact Fin.elim0 port
      · funext port
        have only : port = guardPort := by
          apply Fin.ext
          have bounded : port.val < 1 := port.isLt
          change port.val = 0
          omega
        subst port
        exact first
    exact same.symm ▸ guard_countermodel
  · exact .equations 1 ((guarded.refutedB_iff chosen 1).mp refuted)

def doubleTakePlan : ContextualPublication.Plan (Tm actor) :=
  ⟨⟨[request (symbol 1), request (symbol 1)], [], [], [], [symbol 9]⟩, [true], rfl⟩
def doubleTake : Request locals declarationWorld :=
  ⟨Nat, queries, inferInstance, doubleTakePlan, [91], by decide +kernel, rfl, by decide +kernel⟩

theorem one_occurrence_cannot_supply_two_takes : doubleTake.CertifiedEmpty := by
  have options : ∀ chosen ∈ doubleTake.candidates,
      ¬ (doubleTake.selection chosen).taken.Nodup ∨ doubleTake.refutedB chosen 1 = true := by decide +kernel
  refine ⟨fun chosen present => ?_⟩
  rcases options chosen present with conflict | refuted
  · exact .aliased_take conflict
  · exact .equations 1 ((doubleTake.refutedB_iff chosen 1).mp refuted)

def takeReadPlan : ContextualPublication.Plan (Tm actor) :=
  ⟨⟨[request (symbol 1)], [request (symbol 1)], [], [], [symbol 9]⟩, [true], rfl⟩
def takeRead : Request locals declarationWorld :=
  ⟨Nat, queries, inferInstance, takeReadPlan, [91], by decide +kernel, rfl, by decide +kernel⟩

theorem one_occurrence_cannot_be_both_taken_and_kept : takeRead.CertifiedEmpty := by
  have options : ∀ chosen ∈ takeRead.candidates,
      ¬ Disjoint (takeRead.selection chosen).taken.toFinset (takeRead.selection chosen).read.toFinset ∨
        takeRead.refutedB chosen 1 = true := by decide +kernel
  refine ⟨fun chosen present => ?_⟩
  rcases options chosen present with conflict | refuted
  · exact .take_read conflict
  · exact .equations 1 ((takeRead.refutedB_iff chosen 1).mp refuted)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFallback.Controls
