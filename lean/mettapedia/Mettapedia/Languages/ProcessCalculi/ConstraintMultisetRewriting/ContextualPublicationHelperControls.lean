import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivationControls

/-!
# A genuinely new helper family can supply a reusable output

The source has no rigid constructors and no closed term in its original
frame. Its swapped binary-spine equation needs a fresh nullary helper.
An actual publication firing stores that result, preserving the two object
parameters' symmetry and refusing an output that leaks one of them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication.HelperControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualWorldScopeLedger ContextualScopeSupport

abbrev base := ContextualTransportedActivationControls.base
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Empty)

def rule := { ContextualTransportedActivationControls.rule with produce := [ContextualTransportedActivationControls.rawFormal] }
def selected : Selection Nat := ⟨[],[],[99]⟩
def outputs (_ : Nat) : ContextualTransportedActivationControls.ActiveTerm := ContextualTransportedActivationControls.formal
def scopes (_ : Unit) : Finset Nat := ∅
def inventory : Inventory ContextualTransportedActivationControls.locals ContextualTransportedActivationControls.captures (O := Nat) [(),()] () :=
  ⟨ContextualTransportedActivationControls.before,ContextualTransportedActivationControls.rows,[],[]⟩
def start : ContextualExecution.Endpoint ContextualTransportedActivationControls.locals Nat [(),()] () where
  Names := Unit
  equality := inferInstance
  declarations := ContextualTransportedActivationControls.captures
  scopes := scopes
  occupied := ContextualTransportedActivationControls.occupied
  inventory := inventory
  covered := (coveredWorld_iff ContextualTransportedActivationControls.locals ContextualTransportedActivationControls.captures scopes ContextualTransportedActivationControls.occupied inventory).mpr (by decide +kernel)

theorem problem_unchanged : ContextualActivatedStep.problem ContextualTransportedActivationControls.locals ContextualTransportedActivationControls.captures ContextualTransportedActivationControls.occupied
    selected rule ContextualTransportedActivationControls.rows ContextualTransportedActivationControls.before = ContextualTransportedActivationControls.problem := by with_unfolding_all rfl

theorem covered_rule : RuleCovered (privateScopes scopes) ContextualTransportedActivationControls.occupied rule := by
  apply (ruleRoots_covered_iff (privateScopes scopes) ContextualTransportedActivationControls.occupied rule).mp
  decide +kernel

theorem admitted : ContextualGuardedStep.Valid ContextualTransportedActivationControls.locals ContextualTransportedActivationControls.captures ContextualTransportedActivationControls.occupied
    selected rule ContextualTransportedActivationControls.rows ContextualTransportedActivationControls.before outputs := by
  refine ⟨⟨by decide,by decide,rfl,rfl,rfl,by decide,?_⟩,?_⟩
  · intro check member
    have same : check = .equal ContextualTransportedActivationControls.formal ContextualTransportedActivationControls.swapped := List.mem_singleton.mp member
    subst check
    apply ContextualGuardSemantics.Ask.equal_of_mem ContextualTransportedActivationControls.locals
    rw [problem_unchanged,ContextualTransportedActivationControls.the_actual_prepared_problem_is_the_swapped_equation]
    exact List.mem_singleton_self _
  · rw [problem_unchanged]
    exact ContextualFrameUnifier.solvable_of_model
      ((ContextualResidual.models_observeProblem _ _).mp ContextualTransportedActivationControls.a_later_helper_supplies_an_independent_model)

theorem patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem ContextualTransportedActivationControls.locals ContextualTransportedActivationControls.captures ContextualTransportedActivationControls.occupied selected rule ContextualTransportedActivationControls.rows ContextualTransportedActivationControls.before)) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  decide +kernel

def future (_ : Bool) : MetaArity base := ([],())
def answer (which : Bool) : Term (signature base future) [(),()] () := .op (.inr (.mk which)) .nil
def model (which : Bool) : Assignment ContextualTransportedActivationControls.active future
  | .inl ⟨_,impossible⟩ => nomatch impossible
  | .inr () => answer which

theorem source_instance (which : Bool) :
    SourceInstances (ContextualResidual.observeProblem ContextualTransportedActivationControls.problem) ContextualTransportedActivationControls.formal future (answer which) := by
  refine ⟨ContextualGuardMatching.Extension.identity future,model which,?_,?_⟩
  · apply (ContextualResidual.models_observeProblem _ _).mpr
    rw [ContextualTransportedActivationControls.the_actual_prepared_problem_is_the_swapped_equation]
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    with_unfolding_all rfl
  · with_unfolding_all rfl

theorem actual_helper_output_is_published :
    ∃ firing : ContextualPublication.Firing (before := start),
      firing.rule = rule ∧ firing.selection = selected ∧ firing.outputs = outputs ∧
      firing.reusable = (fun _ => true) ∧
      firing.target.inventory.configuration.present = {99} ∧
      (∀ candidate : Assignment firing.target.declarations future,
        ContextualGuardMatching.Matches (privateFamily ContextualTransportedActivationControls.locals firing.update.declaration) candidate (answer false)
          (firing.target.inventory.rows 99) ∧
        ContextualGuardMatching.Matches (privateFamily ContextualTransportedActivationControls.locals firing.update.declaration) candidate (answer true)
          (firing.target.inventory.rows 99)) ∧
      (∀ _term : Term (signature base ContextualTransportedActivationControls.active) [] (), False) := by
  obtain ⟨firing,ruleEq,selectionEq,outputsEq,kindEq⟩ :=
    ContextualPublication.realize_publication ContextualTransportedActivationControls.locals start rule selected outputs (fun _ => true)
      covered_rule admitted patterned
  refine ⟨firing,ruleEq,selectionEq,outputsEq,kindEq,?_,?_,ContextualTransportedActivationControls.the_original_frame_has_no_closed_term⟩
  · rw [firing.physical_result,selectionEq]
    change MeTTaCalculus.OccurrenceCommits.fire ContextualTransportedActivationControls.before.present (selected.commit (T := Unit)) = {99}
    decide +kernel
  · intro candidate
    have sourceFor (which : Bool) : SourceInstances (ContextualResidual.observeProblem
        (ContextualActivatedStep.problem ContextualTransportedActivationControls.locals start.declarations start.occupied
          selected rule start.inventory.rows start.inventory.configuration)) (outputs 99) future (answer which) := by
      change SourceInstances (ContextualResidual.observeProblem
        (ContextualActivatedStep.problem ContextualTransportedActivationControls.locals ContextualTransportedActivationControls.captures
          ContextualTransportedActivationControls.occupied selected rule ContextualTransportedActivationControls.rows
          ContextualTransportedActivationControls.before)) ContextualTransportedActivationControls.formal future (answer which)
      rw [problem_unchanged]
      exact source_instance which
    constructor <;>
      apply (firing.ordinary_matches_source (by rw [selectionEq]; decide) (by rw [kindEq]) future candidate _).mpr <;>
      rw [ruleEq,selectionEq,outputsEq] <;>
      exact sourceFor _

theorem leaking_one_object_parameter_is_refused :
    ¬ SourceInstances (ContextualResidual.observeProblem ContextualTransportedActivationControls.problem) ContextualTransportedActivationControls.formal future
      (Term.var (S := signature base future) .zero) := by
  rintro ⟨extension,candidate,model,same⟩
  have solved := (ContextualResidual.models_observeProblem candidate ContextualTransportedActivationControls.problem).mp model
  rw [ContextualTransportedActivationControls.the_actual_prepared_problem_is_the_swapped_equation] at solved
  have equation := solved _ List.mem_cons_self
  change instantiate candidate ContextualTransportedActivationControls.formal =
    instantiate candidate (rename (S := signature base ContextualTransportedActivationControls.active) ContextualTransportedActivationControls.swap ContextualTransportedActivationControls.formal) at equation
  have moved := equation.trans (ContextualFamily.instantiate_rename candidate
    ContextualTransportedActivationControls.swap ContextualTransportedActivationControls.formal)
  change instantiate candidate ContextualTransportedActivationControls.formal = .var .zero at same
  erw [same] at moved
  cases moved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication.HelperControls
