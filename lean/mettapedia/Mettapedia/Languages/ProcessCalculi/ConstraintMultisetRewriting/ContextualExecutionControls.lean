import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivatedStepControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStepControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPreparationExtensions

/-!
# Actual contextual paths keep independent schema reads and original guards

The positive driver binds two fresh uses of one physical schema independently.
Its original shared caller equation and untouched shared row remain present.
The endpoint evidence comes from the actual returned update.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualScopeSupport ContextualWorldScopeLedger
open ContextualSelectionViews.Controls
  (base locals captures active a b p selection occupied split)
open ContextualActivatedStep.Controls
  (before rows rule outputs equations the_computed_two_read_problem_has_a_model
    the_shared_physical_schema_read_is_a_valid_firing)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

local instance : Quiver (ContextualExecution.Endpoint locals Nat [] ()) :=
  ContextualExecution.graph locals Nat

def scopes (_ : Nat) : Finset Nat := ∅
def inventory : Inventory locals captures (O := Nat) [] () := ⟨before, rows, [], []⟩

def initial : ContextualExecution.Endpoint locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  scopes := scopes
  occupied := occupied
  inventory := inventory
  covered := (coveredWorld_iff locals captures scopes occupied inventory).mpr (by decide +kernel)

theorem rule_covered : RuleCovered (privateScopes scopes) occupied rule := by
  apply (ruleRoots_covered_iff (privateScopes scopes) occupied rule).mp
  decide +kernel

theorem admitted : ContextualGuardedStep.Requirements locals captures occupied selection rule rows before outputs := by
  have valid := the_shared_physical_schema_read_is_a_valid_firing
  exact ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length,
    valid.outputs, valid.occurrences, fun check member => by cases member⟩

theorem independent_model : ContextualResidual.Models split (ContextualResidual.observeProblem equations) :=
  (ContextualResidual.models_observeProblem split equations).mpr the_computed_two_read_problem_has_a_model

def remainingCount {V : Type} {declaration : V → MetaArity base} {problem : ContextualResidual.Problem declaration} :
    ContextualFrameWorklist.Result problem → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

theorem actual_driver_completes :
    remainingCount (ContextualFrameWorklist.run 6 active (ContextualResidual.observeProblem equations)) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 6 (ContextualResidual.observeProblem equations)
    active split independent_model]
  decide +kernel

theorem actual_shared_schema_path :
    ∃ after : ContextualExecution.Endpoint locals Nat [] (),
      ∃ firing : ContextualExecution.Firing locals initial after,
        firing.selection.read = [7, 7] ∧ firing.fuel = 6 ∧
        after.inventory.configuration.present = {7, 8, 99} ∧
        after.occupied = ContextualFreshFrameScopeLedger.helperLedger
          (ContextualActivationScopes.after occupied selection) ∧
        ∃ path : Quiver.Path initial after, ContextualExecution.selections path = [selection] := by
  have closed := actual_driver_completes
  cases computed : ContextualFrameWorklist.run 6 active (ContextualResidual.observeProblem equations) with
  | refuted impossible => simp only [computed, remainingCount, reduceCtorEq] at closed
  | residual update =>
      have empty : update.remaining = [] := by
        simpa only [computed, remainingCount, Option.some.injEq, List.length_eq_zero_iff] using closed
      let after := ContextualExecution.computedTarget locals initial rule selection outputs rule_covered admitted update
      let firing : ContextualExecution.Firing locals initial after :=
        ⟨rule, rule_covered, selection, outputs, 6, update, admitted, computed, empty, rfl⟩
      let path : Quiver.Path initial after := Quiver.Hom.toPath firing
      have present : after.inventory.configuration.present = {7, 8, 99} := by
        rw [firing.physical_result]
        change fire before.present (selection.commit (T := Unit)) = _
        decide +kernel
      exact ⟨after, firing, rfl, rfl, present, rfl, path, rfl⟩

theorem duplicated_exclusive_take_is_not_admissible : ¬ ([7, 7] : List Nat).Nodup := by decide +kernel

namespace HelperConsumption

abbrev helperBase := ContextualTransportedActivationControls.base
abbrev localDefs := ContextualTransportedActivationControls.locals
abbrev captureDefs := ContextualTransportedActivationControls.captures
abbrev activationDefs := ContextualTransportedActivationControls.active

local instance : DecidableEq helperBase.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : helperBase.Srt) : DecidableEq (helperBase.Op sort) := inferInstanceAs (DecidableEq Empty)

def picked : Selection Nat := ⟨[7], [], [99]⟩
def takeRule : RuleInstance ContextualTransportedActivationControls.RawTerm :=
  ⟨[ContextualTransportedActivationControls.rawFormal], [], [],
    [.equal ContextualTransportedActivationControls.rawFormal ContextualTransportedActivationControls.rawSwapped],
    [ContextualTransportedActivationControls.rawFormal]⟩
def stored (_ : Nat) : ContextualStoredRows.Row localDefs captureDefs [(), ()] () :=
  .shared (rename (S := signature helperBase captureDefs) ContextualTransportedActivationControls.swap
    (generator captureDefs ()))
def beginning : Configuration (Term (signature helperBase captureDefs) [(), ()] ()) Nat := ⟨[], {7, 8}⟩
def made (_ : Nat) : ContextualTransportedActivationControls.ActiveTerm := ContextualTransportedActivationControls.formal
def ledger : Finset Nat := ContextualTransportedActivationControls.occupied
def oldScopes (_ : Unit) : Finset Nat := ∅
def state : Inventory localDefs captureDefs (O := Nat) [(), ()] () := ⟨beginning, stored, [], []⟩
def start : ContextualExecution.Endpoint localDefs Nat [(), ()] () where
  Names := Unit
  equality := inferInstance
  declarations := captureDefs
  scopes := oldScopes
  occupied := ledger
  inventory := state
  covered := (coveredWorld_iff localDefs captureDefs oldScopes ledger state).mpr (by decide +kernel)

theorem the_take_builds_the_nontrivial_swap_problem :
    ContextualActivatedStep.problem localDefs captureDefs ledger picked takeRule stored beginning =
      ContextualTransportedActivationControls.problem := by with_unfolding_all rfl

theorem covered_rule : RuleCovered (privateScopes oldScopes) ledger takeRule := by
  apply (ruleRoots_covered_iff (privateScopes oldScopes) ledger takeRule).mp
  decide +kernel

theorem semantically_admitted : ContextualGuardedStep.Valid
    localDefs captureDefs ledger picked takeRule stored beginning made := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_⟩, ?_⟩
  · intro check member
    have only : check = Check.equal ContextualTransportedActivationControls.formal
        ContextualTransportedActivationControls.swapped := by
      change check ∈ [Check.equal ContextualTransportedActivationControls.formal
        ContextualTransportedActivationControls.swapped] at member
      exact List.mem_singleton.mp member
    subst check
    apply ContextualGuardSemantics.Ask.equal_of_mem localDefs
    rw [the_take_builds_the_nontrivial_swap_problem,
      ContextualTransportedActivationControls.the_actual_prepared_problem_is_the_swapped_equation]
    exact List.mem_singleton_self _
  · rw [the_take_builds_the_nontrivial_swap_problem]
    exact ContextualFrameUnifier.solvable_of_model
      ((ContextualResidual.models_observeProblem _ _).mp
        ContextualTransportedActivationControls.a_later_helper_supplies_an_independent_model)

theorem supported_patterns : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem localDefs captureDefs ledger picked takeRule stored beginning)) :=
  (ContextualPatternFragment.checkProblem_iff _).mp (by decide +kernel)

theorem no_endomorphic_model :
    ¬ (ContextualFamilies.action (ContextualActivatedStep.target localDefs captureDefs) [(), ()] ()).Consistent
      (ContextualActivatedStep.problem localDefs captureDefs ledger picked takeRule stored beginning) := by
  rw [the_take_builds_the_nontrivial_swap_problem]
  exact ContextualTransportedActivationControls.the_original_small_frame_is_inconsistent

/-- The generic semantic realization constructs this actual consuming and
producing execution, despite the absence of an original endomorphic model. -/
theorem actual_consumption_and_production_require_the_fresh_family :
    ∃ after : ContextualExecution.Endpoint localDefs Nat [(), ()] (),
      ∃ firing : ContextualExecution.Firing localDefs start after,
        firing.selection = picked ∧ firing.rule = takeRule ∧
        after.inventory.configuration.present = {8, 99} ∧
        ¬ (ContextualFamilies.action (ContextualActivatedStep.target localDefs captureDefs) [(), ()] ()).Consistent
          (ContextualActivatedStep.problem localDefs captureDefs ledger picked takeRule stored beginning) := by
  obtain ⟨after, firing, ruleEq, selectionEq, _⟩ :=
    ContextualExecution.realize_semantic_admission localDefs start takeRule picked made
      covered_rule semantically_admitted supported_patterns
  refine ⟨after, firing, selectionEq, ruleEq, ?_, no_endomorphic_model⟩
  rw [firing.physical_result, selectionEq]
  change fire beginning.present (picked.commit (T := Unit)) = {8, 99}
  decide +kernel

def extraDeclarations := ContextualGuardMatching.Extension.withLocals
  ContextualTransportedActivationControls.helpers captureDefs

def extendedRule := takeRule.map
  (instantiate (ContextualStoredRows.liftCaptures localDefs extraDeclarations.assignment))
def extendedRows := fun occurrence => (stored occurrence).map localDefs extraDeclarations.assignment
def extendedBefore := ContextualTransportedActivation.configurationMap extraDeclarations.assignment beginning
def extendedOutputs := fun occurrence =>
  instantiate (ContextualViewNaturality.activeLift localDefs extraDeclarations.assignment) (made occurrence)

theorem unused_declarations_preserve_the_actual_semantic_admission :
    ContextualGuardedStep.Valid localDefs extraDeclarations.declarations ledger picked
      extendedRule extendedRows extendedBefore extendedOutputs :=
  (ContextualViewNaturality.semantic_admission_extension_iff localDefs extraDeclarations ledger picked
    takeRule stored beginning made).mpr semantically_admitted

abbrev extendedActive := ContextualActivatedStep.target localDefs extraDeclarations.declarations

def extendedModel : Assignment extendedActive extendedActive
  | .inl ⟨_, impossible⟩ => nomatch impossible
  | .inr (.inl ()) => generator extendedActive (.inr (.inl ()))
  | .inr (.inr ()) => .op (.inr (.mk (.inr (.inl ())))) .nil

set_option backward.isDefEq.respectTransparency.types false in
theorem the_extended_family_now_has_an_endomorphic_model :
    (ContextualFamilies.action extendedActive [(), ()] ()).Models extendedModel
      (ContextualActivatedStep.problem localDefs extraDeclarations.declarations ledger picked
        extendedRule extendedRows extendedBefore) := by
  change ContextualFrameUnifier.Models extendedModel _
  intro equation member
  have only : equation =
      (instantiate (ContextualViewNaturality.activeLift localDefs extraDeclarations.assignment)
        ContextualTransportedActivationControls.formal,
       instantiate (ContextualViewNaturality.activeLift localDefs extraDeclarations.assignment)
        ContextualTransportedActivationControls.swapped) := by
    change equation ∈
      [(instantiate (ContextualViewNaturality.activeLift localDefs extraDeclarations.assignment)
          ContextualTransportedActivationControls.formal,
        instantiate (ContextualViewNaturality.activeLift localDefs extraDeclarations.assignment)
          ContextualTransportedActivationControls.swapped)] at member
    exact List.mem_singleton.mp member
  subst equation
  with_unfolding_all rfl

/-- Same-frame consistency can change merely because an unused helper
arity is available; contextual admission is invariant under that extension. -/
theorem endomorphic_consistency_depends_on_unused_declarations :
    ¬ (ContextualFamilies.action (ContextualActivatedStep.target localDefs captureDefs) [(), ()] ()).Consistent
        (ContextualActivatedStep.problem localDefs captureDefs ledger picked takeRule stored beginning) ∧
      (ContextualFamilies.action extendedActive [(), ()] ()).Consistent
        (ContextualActivatedStep.problem localDefs extraDeclarations.declarations ledger picked
          extendedRule extendedRows extendedBefore) :=
  ⟨no_endomorphic_model, ⟨extendedModel, the_extended_family_now_has_an_endomorphic_model⟩⟩

end HelperConsumption

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionControls
