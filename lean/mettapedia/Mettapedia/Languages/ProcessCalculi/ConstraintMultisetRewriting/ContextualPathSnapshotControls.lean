import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathInclusions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedExecutionControls

/-!
# Actual paths distinguish retained prefix snapshots from later effects

A guarded event produces a shared row and the following actual event consumes
it. The intermediate prefix snapshot still contains that row. Separately,
an actual tell binds a previously unconstrained caller; its original prefix
ask remains unentailed under pure path transport.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathSnapshotControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualWorldScopeLedger ContextualScopeSupport ContextualExecution
open ContextualSelectionViews.Controls (base locals captures active atom p)
open ContextualGuardedExecutionControls (initial)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

abbrev middle := ContextualGuardedExecutionControls.after
abbrev secondActive := ContextualActivatedStep.target locals middle.declarations
local instance : DecidableEq middle.Names := middle.equality

def consume : Selection Nat := ⟨[99], [], []⟩
def consumeRule : RuleInstance (Term (signature base (ContextualActivatedStep.source locals middle.declarations)) [] ()) :=
  ⟨[atom _], [], [], [], []⟩
def consumeOutputs (_ : Nat) : Term (signature base secondActive) [] () := atom _
def consumeProblem := ContextualActivatedStep.problem locals middle.declarations middle.occupied consume consumeRule
  middle.inventory.rows middle.inventory.configuration

theorem the_consumption_problem_is_the_actual_reflexive_row_equation :
    consumeProblem = [(atom secondActive, atom secondActive)] := by with_unfolding_all rfl

theorem consumeRule_covered : RuleCovered (privateScopes middle.scopes) middle.occupied consumeRule := by
  apply (ruleRoots_covered_iff (privateScopes middle.scopes) middle.occupied consumeRule).mp
  change (∅ : Finset Nat) ⊆ middle.occupied
  exact Finset.empty_subset _

theorem consume_admitted : ContextualGuardedStep.Requirements locals middle.declarations middle.occupied
    consume consumeRule middle.inventory.rows middle.inventory.configuration consumeOutputs := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, ?_, ?_⟩
  · change Enabled consumeOutputs ({7, 99} : Finset Nat) (consume.commit (T := Term (signature base secondActive) [] ()))
    decide +kernel
  · intro check member
    cases member

theorem consume_normalizes :
    ContextualRigidSolver.normalize (ContextualResidual.observeProblem consumeProblem) = some [] := by
  rw [the_consumption_problem_is_the_actual_reflexive_row_equation]
  with_unfolding_all rfl

def consumeUpdate := ContextualFrameWorklist.normalizationUpdate consume_normalizes

theorem consume_computed :
    ContextualFrameWorklist.run 1 secondActive (ContextualResidual.observeProblem consumeProblem) = .residual consumeUpdate := by
  have model : ContextualResidual.Models (generator secondActive) (ContextualResidual.observeProblem consumeProblem) := by
    apply (ContextualResidual.models_observeProblem _ _).mpr
    rw [the_consumption_problem_is_the_actual_reflexive_row_equation]
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl
  rw [ContextualFrameWorklist.run_eq_local_on_model 1 _ secondActive (generator secondActive) model]
  rw [ContextualFrameWorklist.runWithRefuter_normalized _ 0 _ [] consume_normalizes (by rfl)]
  rfl

def final : Endpoint locals Nat [] () :=
  computedTarget locals middle consumeRule consume consumeOutputs consumeRule_covered consume_admitted consumeUpdate

def consumeFiring : Firing locals middle final :=
  ⟨consumeRule, consumeRule_covered, consume, consumeOutputs, 1, consumeUpdate,
    consume_admitted, consume_computed, rfl, rfl⟩

def producePath : Quiver.Path initial middle := Quiver.Hom.toPath ContextualGuardedExecutionControls.firing
def consumePath : Quiver.Path middle final := Quiver.Hom.toPath consumeFiring
def combinedPath : Quiver.Path initial final := producePath.comp consumePath

theorem the_actual_two_event_path_retains_both_selections :
    selections combinedPath = [ContextualGuardedStep.Controls.selection, consume] ∧
      fuels combinedPath = [0, 1] ∧
      pathAssignment combinedPath = Assignment.compose (pathAssignment consumePath) (pathAssignment producePath) :=
  ⟨rfl, rfl, pathAssignment_comp producePath consumePath⟩

theorem the_removed_row_remains_in_the_intermediate_prefix_snapshot :
    99 ∈ (prefixSnapshot consumePath).configuration.present ∧
      99 ∉ final.inventory.configuration.present ∧
      (prefixSnapshot consumePath).configuration.present ≠ final.inventory.configuration.present := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro same
  have retained : 99 ∈ (prefixSnapshot consumePath).configuration.present := by decide +kernel
  rw [same] at retained
  exact (by decide +kernel : 99 ∉ final.inventory.configuration.present) retained

def tell : Selection Nat := ⟨[], [], []⟩
def tellRule : RuleInstance (Term (signature base (ContextualActivatedStep.source locals captures)) [] ()) :=
  ⟨[], [], [(generator (ContextualActivatedStep.source locals captures) (Sum.inr (0 : Nat)),
    atom (ContextualActivatedStep.source locals captures))], [], []⟩
def tellOutputs (_ : Nat) : Term (signature base active) [] () := atom _
def tellProblem := ContextualActivatedStep.problem locals captures initial.occupied tell tellRule
  initial.inventory.rows initial.inventory.configuration

theorem tellRule_covered : RuleCovered (privateScopes initial.scopes) initial.occupied tellRule := by
  apply (ruleRoots_covered_iff (privateScopes initial.scopes) initial.occupied tellRule).mp
  change (∅ : Finset Nat) ⊆ initial.occupied
  exact Finset.empty_subset _

theorem tell_admitted : ContextualGuardedStep.Requirements locals captures initial.occupied tell tellRule
    initial.inventory.rows initial.inventory.configuration tellOutputs := by
  exact ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, by decide +kernel, fun _ member => by cases member⟩

theorem tell_patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem tellProblem) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  decide +kernel

theorem original_caller_question_unentailed :
    ¬ ContextualGuardSemantics.Ask locals initial.inventory.configuration.equations initial.inventory.rows
      initial.inventory.configuration.present (.equal (generator captures 0) (atom captures)) := by
  intro ask
  have same := ask Nat captures (generator captures) (fun _ member => by cases member)
  change generator captures 0 = atom captures at same
  have heads := (Term.op.inj same).1
  cases heads

theorem actual_later_tell_does_not_discharge_the_retained_prefix_question :
    ∃ target : Endpoint locals Nat [] (), ∃ firing : Firing locals initial target,
      firing.rule = tellRule ∧ firing.selection = tell ∧
      ∃ path : Quiver.Path initial target,
      path = Quiver.Hom.toPath firing ∧ selections path = [tell] ∧
      ¬ ContextualGuardSemantics.Ask locals (prefixSnapshot path).configuration.equations
        (prefixSnapshot path).rows (prefixSnapshot path).configuration.present
        ((Check.equal (generator captures 0) (atom captures)).map (instantiate (pathAssignment path))) ∧
      ContextualGuardSemantics.Ask locals target.inventory.configuration.equations target.inventory.rows
        target.inventory.configuration.present
        ((Check.equal (generator captures 0) (atom captures)).map (instantiate (pathAssignment path))) := by
  obtain ⟨fuel, solved | refused⟩ := ContextualTransportedActivation.solve_or_refute locals captures tell_admitted tell_patterned
  · obtain ⟨update, returned⟩ := solved
    let target := computedTarget locals initial tellRule tell tellOutputs tellRule_covered tell_admitted update
    let firing : Firing locals initial target :=
      ⟨tellRule, tellRule_covered, tell, tellOutputs, fuel, update, tell_admitted,
        returned.computed, returned.empty, rfl⟩
    let path : Quiver.Path initial target := Quiver.Hom.toPath firing
    refine ⟨target, firing, rfl, rfl, path, rfl, rfl, ?_, ?_⟩
    · intro asked
      exact original_caller_question_unentailed ((ask_prefixSnapshot_iff path _).mp asked)
    · apply ContextualGuardSemantics.Ask.equal_of_mem locals
      change (instantiate (pathAssignment path) (generator captures 0),
        instantiate (pathAssignment path) (atom captures)) ∈ target.inventory.configuration.equations
      with_unfolding_all exact List.mem_singleton_self _
  · obtain ⟨impossible, _computed⟩ := refused
    apply False.elim
    let constantModel : Assignment active active := fun name => match name with
      | .inl _ => atom active
      | .inr _ => atom active
    apply impossible active constantModel
    apply (ContextualResidual.models_observeProblem _ _).mpr
    intro equation member
    change equation ∈ [(generator active (.inr 0), atom active)] at member
    obtain rfl := List.mem_singleton.mp member
    rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathSnapshotControls
