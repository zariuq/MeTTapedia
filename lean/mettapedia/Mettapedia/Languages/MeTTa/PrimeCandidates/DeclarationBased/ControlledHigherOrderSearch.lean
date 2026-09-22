import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.ControlledBoundedHOLSearch
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HigherOrderSearchedProof

/-!
# Controlled searches of a predicate/function theorem

Two supplied scoped candidate inventories run the actual bounded algorithm
on the same closed higher-order query. Reversing the occurrence-preserving
controller changes which search runs first and its actual event cost. Both
retained proofs cross the same native compiler and typing interface.

The completed portfolio preserves its proof bag, while the first-answer
receipt keeps its selected request and cost. A shallower actual search fails
without refuting the theorem; exhausted portfolios have no billable steps.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace ControlledHigherOrderSearch

open Mettapedia.Logic HOL HOL.BoundedLogicalSearch
open Mettapedia.GSLT.Core Mettapedia.GSLT.Core.BranchingTemporal
open ProofSearch HOLNativeGenericProofCompiler
open Presentation FormationSensitiveHOLInterface
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open FormationSensitiveHOLGenericProofInstances.CallGuard

private instance (type : Ty Unit) : DecidableEq (Constant type) := fun first second => by
  cases first <;> cases second
  all_goals first | exact .isTrue rfl | exact .isFalse (by intro same; cases same)

abbrev Request := ControlledHOL.BoundedProvider.Request Unit Constant
abbrev Proof := HOLAdapter.Solution HigherOrderSearchedProof.goal
abbrev State := ControlledSearch.State Request Proof Unit

def direct : Request := ⟨contextCandidates, 8⟩
def detour : Request := ⟨HigherOrderSearchedProof.applicationFirstCandidates, 8⟩
def shallow : Request := ⟨contextCandidates, 5⟩
def roots : List Request := [direct, detour]

def system : BranchingSystem Request Proof :=
  ControlledHOL.BoundedProvider.system HigherOrderSearchedProof.goal

def controller (preferDetour : Bool) : InferenceControl.Controller Request Proof Unit :=
  InferenceControl.Controller.fixed
    (if preferDetour then Scheduler.reverseBreadthFirst else Scheduler.breadthFirst)

def plan (preferDetour : Bool) :
    System HOLAdapter.Solution HOLAdapter.noCounter
      BoundedHOLProofPlanning.Constraints HigherOrderSearchedProof.goal :=
  ControlledSearch.plan HOLAdapter.noCounter BoundedHOLProofPlanning.Constraints
    HigherOrderSearchedProof.goal system (controller preferDetour) roots

def state (preferDetour : Bool) (fuel : Nat) : State :=
  ControlledSearch.runState system (controller preferDetour) fuel (plan preferDetour).initial

theorem first_live (preferDetour : Bool) :
    InferenceControl.Snapshot.LiveThrough system (controller preferDetour) 1
      (plan preferDetour).initial.snapshot := by
  intro elapsed smaller
  have zero : elapsed = 0 := by omega
  subst elapsed
  simp [InferenceControl.Snapshot.run, plan, ControlledSearch.plan,
    InferenceControl.Snapshot.initial, BranchingTemporal.initial, roots]

theorem full_live (preferDetour : Bool) :
    InferenceControl.Snapshot.LiveThrough system (controller preferDetour) 2
      (plan preferDetour).initial.snapshot := by
  intro elapsed smaller
  interval_cases elapsed <;> cases preferDetour <;>
    simp [InferenceControl.Snapshot.run, plan, ControlledSearch.plan,
      InferenceControl.Snapshot.initial, BranchingTemporal.initial, roots,
      InferenceControl.Snapshot.tick, BranchingTemporal.tick, controller,
      InferenceControl.Controller.fixed, Scheduler.breadthFirst,
      Scheduler.reverseBreadthFirst, system, ControlledHOL.BoundedProvider.system]

def firstTrace (preferDetour : Bool) :
    (plan preferDetour).Trace (plan preferDetour).initial (state preferDetour 1) :=
  ControlledSearch.runTrace 1 (plan preferDetour).initial (first_live preferDetour)

def fullTrace (preferDetour : Bool) :
    (plan preferDetour).Trace (plan preferDetour).initial (state preferDetour 2) :=
  ControlledSearch.runTrace 2 (plan preferDetour).initial (full_live preferDetour)

def workCost (preferDetour : Bool) : System.CostModel (plan preferDetour) (Nat × Nat) :=
  ControlledHOL.BoundedProvider.workCost HigherOrderSearchedProof.goal
    (controller preferDetour) roots

theorem first_cost (preferDetour : Bool) :
    (workCost preferDetour).total (firstTrace preferDetour) =
      (1, (if preferDetour then HigherOrderSearchedProof.detoured
        else HigherOrderSearchedProof.searched).events.length) := by
  cases preferDetour <;> rfl

theorem detoured_first_costs_more :
    ((workCost false).total (firstTrace false)).2 <
      ((workCost true).total (firstTrace true)).2 := by
  rw [first_cost, first_cost]
  exact HigherOrderSearchedProof.detoured_search_costs_more

theorem full_cost (preferDetour : Bool) :
    (workCost preferDetour).total (fullTrace preferDetour) =
      (2, HigherOrderSearchedProof.searched.events.length +
        HigherOrderSearchedProof.detoured.events.length) := by
  cases preferDetour
  · rfl
  · change (1 + (1 + 0),
        HigherOrderSearchedProof.detoured.events.length +
          (HigherOrderSearchedProof.searched.events.length + 0)) = _
    simp [Nat.add_comm]

theorem full_complete (preferDetour : Bool) :
    (state preferDetour 2).snapshot.search.frontier = [] := by
  cases preferDetour <;> rfl

theorem complete_bags_agree :
    eventBag (state false 2).snapshot.search.events =
      eventBag (state true 2).snapshot.search.events :=
  InferenceControl.Snapshot.completed_controllers_bag_agree system
    (controller false) (controller true)
    (ControlledHOL.BoundedProvider.denotation HigherOrderSearchedProof.goal)
    roots 2 2 (full_complete false) (full_complete true)

theorem no_terminal_charge (preferDetour : Bool) :
    ¬ ∃ target, Nonempty (ControlledSearch.Step system (controller preferDetour)
      (state preferDetour 2) target) :=
  ControlledSearch.no_step_of_complete _ (full_complete preferDetour)

/-- Requesting another unit after completion preserves the whole state,
including the actual expansion counter. -/
theorem extra_fuel_preserves_state (preferDetour : Bool) :
    state preferDetour 3 = state preferDetour 2 := by
  calc
    state preferDetour 3 = ControlledSearch.runState system (controller preferDetour)
        1 (state preferDetour 2) :=
      ControlledSearch.runState_add 2 1 (plan preferDetour).initial
    _ = state preferDetour 2 :=
      ControlledSearch.runState_of_complete 1 _ (full_complete preferDetour)

theorem extra_fuel_cost (preferDetour : Bool) :
    (ControlledSearch.expansionCost (counter := HOLAdapter.noCounter)
      (Constraint := BoundedHOLProofPlanning.Constraints)).total
        (ControlledSearch.boundedRunTrace (counter := HOLAdapter.noCounter)
          (Constraint := BoundedHOLProofPlanning.Constraints) (system := system)
          (controller := controller preferDetour) (roots := roots) 3
          (plan preferDetour).initial) = 2 := by
  calc
    _ = ControlledSearch.expansions system (controller preferDetour)
        (plan preferDetour).initial.snapshot 3 :=
      ControlledSearch.bounded_run_cost 3 (plan preferDetour).initial
    _ = 2 := by cases preferDetour <;> rfl

def compilation (preferDetour : Bool) : Option (Tower.Tm 0) :=
  ControlledHOL.compileState? (counter := HOLAdapter.noCounter)
    (Constraint := BoundedHOLProofPlanning.Constraints)
    FormationSensitiveHOLInvariant.signature proofName
    (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
    (state preferDetour 1) Fin.elim0 Fin.elim0

set_option maxRecDepth 10000 in
theorem compilation_succeeds (preferDetour : Bool) :
    (compilation preferDetour).isSome = true := by
  cases preferDetour <;> decide +kernel

def native (preferDetour : Bool) : Tower.Tm 0 :=
  (compilation preferDetour).get (compilation_succeeds preferDetour)

theorem native_emitted (preferDetour : Bool) :
    compilation preferDetour = some (native preferDetour) :=
  (Option.some_get (compilation_succeeds preferDetour)).symm

/-- Both controllers compile their actual searched answer at the same family.
The source proof is not replaced by a separately supplied theorem. -/
theorem native_typed (preferDetour : Bool) :
    ∃ code, represent FormationSensitiveHOLInvariant.signature HigherOrderSearchedProof.query =
      some code ∧
      Presentation.FormationSensitive.Typing rules .nil (native preferDetour)
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) := by
  have objectTyped : GenericTyping.Objects FormationSensitiveHOLInvariant.signature
      (gamma := []) .nil Fin.elim0 := by intro index; nomatch index
  have hypothesisTyped : GenericTyping.Hypotheses FormationSensitiveHOLInvariant.signature
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
      (gamma := []) (delta := []) .nil Fin.elim0 Fin.elim0 := by intro index; nomatch index
  simpa only [HigherOrderSearchedProof.goal, TelescopeAbstraction.subst_empty,
    TelescopeAbstraction.liftClosed_zero, Operations.logicalOnly, rules] using
    ControlledHOL.compiled_typed FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
      (firstTrace preferDetour) objectTyped hypothesisTyped (native_emitted preferDetour)

/-- The two actual compiled answers also use the same model algebra. -/
theorem native_denotes (preferDetour : Bool) (property : CompileLanguageControl → Prop) :
    HenkinFamilySemantics.Proves (CallGuardSemantics.emptyState property)
      (native preferDetour) HigherOrderSearchedProof.query := by
  apply ControlledHOL.compiled_denotes FormationSensitiveHOLInvariant.signature proofName
    (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
    (CallGuardSemantics.semantics property) (firstTrace preferDetour)
    (native_emitted preferDetour) (CallGuardSemantics.emptyState property)
  intro index
  nomatch index

set_option maxRecDepth 10000 in
theorem shallow_search_fails :
    (ControlledHOL.BoundedProvider.result HigherOrderSearchedProof.goal shallow).answer = none := by
  decide +kernel

theorem shallow_emits_nothing : system.emit shallow = none :=
  ControlledHOL.BoundedProvider.failed_emits_nothing HigherOrderSearchedProof.goal
    shallow shallow_search_fails

def shallowPlan :
    System HOLAdapter.Solution HOLAdapter.noCounter
      BoundedHOLProofPlanning.Constraints HigherOrderSearchedProof.goal :=
  ControlledSearch.plan HOLAdapter.noCounter BoundedHOLProofPlanning.Constraints
    HigherOrderSearchedProof.goal system (controller false) [shallow]

def shallowState : State :=
  ControlledSearch.runState system (controller false) 1 shallowPlan.initial

theorem shallow_live :
    InferenceControl.Snapshot.LiveThrough system (controller false) 1
      shallowPlan.initial.snapshot := by
  intro elapsed smaller
  have zero : elapsed = 0 := by omega
  subst elapsed
  simp [InferenceControl.Snapshot.run, shallowPlan, ControlledSearch.plan,
    InferenceControl.Snapshot.initial, BranchingTemporal.initial]

def shallowTrace : shallowPlan.Trace shallowPlan.initial shallowState :=
  ControlledSearch.runTrace 1 shallowPlan.initial shallow_live

theorem shallow_exhausted :
    shallowPlan.observe shallowState = some (.exhausted (.searchSpace 1)) := by
  simp [shallowPlan, ControlledSearch.plan, ControlledSearch.observe,
    shallowState, ControlledSearch.runState, InferenceControl.Snapshot.run,
    InferenceControl.Snapshot.tick, InferenceControl.Snapshot.initial,
    controller, InferenceControl.Controller.fixed, Scheduler.breadthFirst,
    BranchingTemporal.initial, BranchingTemporal.tick, shallow_emits_nothing]
  rfl

theorem failed_search_is_charged :
    (ControlledSearch.expansionCost (counter := HOLAdapter.noCounter)
      (Constraint := BoundedHOLProofPlanning.Constraints)).total shallowTrace = 1 :=
  ControlledSearch.run_expansion_cost 1 shallowPlan.initial shallow_live

theorem failed_search_not_compiled :
    ControlledHOL.compileState? (counter := HOLAdapter.noCounter)
      (Constraint := BoundedHOLProofPlanning.Constraints)
      FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
      shallowState (Fin.elim0 : Sub Tower.Head 0 0) Fin.elim0 = none :=
  ControlledHOL.exhausted_not_compiled FormationSensitiveHOLInvariant.signature proofName
    (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
    shallowState (.searchSpace 1) shallow_exhausted (Fin.elim0 : Sub Tower.Head 0 0) Fin.elim0

#print axioms first_cost
#print axioms detoured_first_costs_more
#print axioms full_cost
#print axioms complete_bags_agree
#print axioms no_terminal_charge
#print axioms extra_fuel_preserves_state
#print axioms extra_fuel_cost
#print axioms native_typed
#print axioms native_denotes
#print axioms shallow_search_fails
#print axioms failed_search_is_charged
#print axioms failed_search_not_compiled

end ControlledHigherOrderSearch
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
