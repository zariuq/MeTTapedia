import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalGuards
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionEndpoints
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPreparationNaturality

/-!
# Solver-backed conditional binding and one occurrence update

Every selected row opens its value and latent equations at its actual port
scope. The joint information problem retains the incoming heterogeneous
equations, matched values, body equations and all selected latent equations.
An admitted event can retain an unfinished actual solver result: reusable
outputs store its value and pending equations together; shared outputs keep
the original references in the returned world.

This indexed information/resource execution does not infer client authority
or textual scope ownership. Those remain formation refinements. A solver
return alone does not replace the semantic guard and solvability evidence
required for a committed firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local Shared O : Type}
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {Γ : Ctx S} {sort : S.Srt}

def latent (occupied : Finset Nat) (selection : Selection O) (rows : O → Row locals captures Γ sort) :
    ContextualResidual.Problem (ContextualActivatedStep.target locals captures) :=
  (List.ofFn fun port : Fin selection.taken.length =>
    (rows (selection.taken.get port)).obligationsAt locals captures
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port))).flatten ++
  (List.ofFn fun port : Fin selection.read.length =>
    (rows (selection.read.get port)).obligationsAt locals captures
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port))).flatten

def information (occupied : Finset Nat) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures) :
    ContextualResidual.Problem (ContextualActivatedStep.target locals captures) :=
  ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget locals captures) before ++
    ContextualResidual.observeProblem (ContextualActivatedStep.addedEquations locals captures occupied selection rule
      (fun occurrence => (rows occurrence).value)) ++ latent locals captures occupied selection rows

/-- Captured declaration maps retain each selected row's latent equations
at the same take/read scope, including repeated reads of one physical row. -/
theorem latent_transport {Next : Type} {next : Next → MetaArity S}
    (change : Assignment captures next) (occupied : Finset Nat) (selection : Selection O)
    (rows : O → Row locals captures Γ sort) :
    ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change)
        (latent locals captures occupied selection rows) =
      latent locals next occupied selection (fun occurrence => (rows occurrence).map locals captures change) := by
  have append (first second : ContextualResidual.Problem (ContextualActivatedStep.target locals captures)) :
      ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change) (first ++ second) =
        ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change) first ++
          ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change) second :=
    List.map_append ..
  have flatten (parts : List (ContextualResidual.Problem (ContextualActivatedStep.target locals captures))) :
      ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change) parts.flatten =
        (parts.map (ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change))).flatten :=
    List.map_flatten ..
  simp only [latent, append, flatten, List.map_ofFn, Function.comp_def, obligations_transport]

/-- The complete heterogeneous information store commutes with capture
transport. This retains incoming, matched, authored and row-local equations. -/
theorem information_transport {Next : Type} {next : Next → MetaArity S}
    (change : Assignment captures next) (occupied : Finset Nat) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures) :
    ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change)
        (information locals captures occupied selection rule rows before) =
      information locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals captures change)
        (ContextualResidual.mapProblem change before) := by
  have append (first second : ContextualResidual.Problem (ContextualActivatedStep.target locals captures)) :
      ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change) (first ++ second) =
        ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change) first ++
          ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change) second :=
    List.map_append ..
  simp only [information, append, ContextualConditionalNaturality.map_problem_compose,
    ContextualViewNaturality.capture_square, ← ContextualResidual.observeProblem_mapProblem,
    ContextualPreparationNaturality.added_equations_transport, latent_transport]
  rfl

section ScopeRelocation

variable (sourceLedger targetLedger : Finset Nat) (selection : Selection O)
  (permutation : Equiv.Perm Nat)
  (aligned : ∀ port : ContextualActivationScopes.Port selection,
    permutation (ContextualActivationScopes.scopeAt sourceLedger port) =
      ContextualActivationScopes.scopeAt targetLedger port)

include aligned

theorem latent_relocated (rows : O → Row locals captures Γ sort) :
    ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation)
        (latent locals captures sourceLedger selection rows) =
      latent locals captures targetLedger selection rows := by
  have append (first second : ContextualResidual.Problem (ContextualActivatedStep.target locals captures)) :
      ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation) (first ++ second) =
        ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation) first ++
          ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation) second :=
    List.map_append ..
  have flatten (parts : List (ContextualResidual.Problem (ContextualActivatedStep.target locals captures))) :
      ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation) parts.flatten =
        (parts.map (ContextualResidual.mapProblem
          (ContextualEventViewRelocation.assignment locals captures permutation))).flatten := List.map_flatten ..
  simp only [latent, append, flatten, List.map_ofFn, Function.comp_def,
    ContextualConditionalNaturality.obligations_relocated, aligned]

/-- A fresh-scope permutation transports the complete conditional problem,
fixing captured information and retaining each selected use's equations. -/
theorem information_relocated
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures) :
    ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation)
        (information locals captures sourceLedger selection rule rows before) =
      information locals captures targetLedger selection rule rows before := by
  have append (first second : ContextualResidual.Problem (ContextualActivatedStep.target locals captures)) :
      ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation) (first ++ second) =
        ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation) first ++
          ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation) second :=
    List.map_append ..
  simp only [information, append, ContextualConditionalNaturality.map_problem_compose,
    ContextualEventViewRelocation.capture_assignment_fixed, ← ContextualResidual.observeProblem_mapProblem,
    ContextualEventViewRelocation.added_equations_between_allocations locals captures sourceLedger targetLedger
      selection permutation aligned, latent_relocated locals captures sourceLedger targetLedger selection permutation aligned]

end ScopeRelocation

theorem latent_ofStored (occupied : Finset Nat) (selection : Selection O)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    latent locals captures occupied selection (fun occurrence => ofStored locals captures (rows occurrence)) = [] := by
  simp [latent, Row.obligationsAt, ofStored, ContextualResidual.mapProblem]

/-- The old value-only binding problem embeds exactly, rather than merely
having a selected example with the same result. -/
theorem information_ofStored (occupied : Finset Nat) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    information locals captures occupied selection rule (fun occurrence => ofStored locals captures (rows occurrence))
      (ContextualResidual.observeProblem before.equations) =
    ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures occupied selection rule rows before) := by
  rw [information, latent_ofStored, List.append_nil, ContextualActivatedStep.problem_eq_frame_append]
  change ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget locals captures)
      (ContextualResidual.observeProblem before.equations) ++
      ContextualResidual.observeProblem (ContextualActivatedStep.addedEquations locals captures occupied selection rule rows) =
    ContextualResidual.observeProblem (ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals captures)
      before.equations ++ ContextualActivatedStep.addedEquations locals captures occupied selection rule rows)
  rw [← ContextualResidual.observeProblem_mapProblem]
  exact List.map_append .. |>.symm

structure State (O : Type) (context : Ctx S) (sort : S.Srt) : Type 1 where
  Names : Type
  equality : DecidableEq Names
  declarations : Names → MetaArity S
  occupied : Finset Nat
  equations : ContextualResidual.Problem declarations
  present : Finset O
  rows : O → Row locals declarations context sort

variable {locals} in
/-- Change the row representation while retaining this state's information,
physical occurrences and declaration frame. Row-meaning comparisons are
proved by each publication decoder. -/
def State.withRows {Other : Type} (state : State locals O Γ sort) (others : Other → MetaArity S)
    (rows : O → Row others state.declarations Γ sort) : State others O Γ sort where
  Names := state.Names
  equality := state.equality
  declarations := state.declarations
  occupied := state.occupied
  equations := state.equations
  present := state.present
  rows := rows

def ofEndpoint (before : ContextualExecution.Endpoint locals O Γ sort) : State locals O Γ sort :=
  ⟨before.Names, before.equality, before.declarations, before.occupied,
    ContextualResidual.observeProblem before.inventory.configuration.equations, before.inventory.configuration.present,
    fun occurrence => ofStored locals before.declarations (before.inventory.rows occurrence)⟩

def guardRows (rows : O → Row locals captures Γ sort) :=
  fun occurrence => (rows occurrence).map locals captures (ContextualSelectionViews.capturedTarget locals captures)

theorem guardRows_transport {Next : Type} {next : Next → MetaArity S}
    (change : Assignment captures next) (rows : O → Row locals captures Γ sort) :
    (fun occurrence => (guardRows locals captures rows occurrence).map locals _
      (ContextualViewNaturality.activeLift locals change)) =
      guardRows locals next (fun occurrence => (rows occurrence).map locals captures change) := by
  funext occurrence
  simp only [guardRows, ContextualConditionalNaturality.row_map_compose,
    ContextualViewNaturality.capture_square]

/-- Original-cut guards transport with the complete information and row
table. The physical world and the take/read scope allocation stay fixed. -/
theorem ask_transport {Next : Type} {next : Next → MetaArity S}
    (change : Assignment captures next) (occupied : Finset Nat) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures)
    (world : Finset O) (check : Check (Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort))
    (asked : ContextualConditionalGuards.Ask locals
      (information locals captures occupied selection rule rows before)
      (guardRows locals captures rows) world check) :
    ContextualConditionalGuards.Ask locals
      (information locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals captures change)
        (ContextualResidual.mapProblem change before))
      (guardRows locals next (fun occurrence => (rows occurrence).map locals captures change)) world
      (check.map (instantiate (ContextualViewNaturality.activeLift locals change))) := by
  have transported := ContextualConditionalGuards.ask_transport locals
    (ContextualViewNaturality.activeLift locals change) asked
  rw [information_transport, guardRows_transport] at transported
  exact transported

def Solvable {V : Type} {declaration : V → MetaArity S} (problem : ContextualResidual.Problem declaration) : Prop :=
  ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment declaration future),
    ContextualResidual.Models candidate problem

theorem Solvable.reindex_iff {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}
    (forward : V → W) (backward : W → V)
    (forwardPreserves : ∀ name, target (forward name) = source name)
    (backwardPreserves : ∀ name, source (backward name) = target name)
    (leftInverse : Function.LeftInverse backward forward) (problem : ContextualResidual.Problem source) :
    Solvable (ContextualResidual.mapProblem (reindex forward forwardPreserves) problem) ↔ Solvable problem := by
  constructor
  · rintro ⟨Future, future, candidate, model⟩
    exact ⟨Future, future, Assignment.compose candidate (reindex forward forwardPreserves),
      (ContextualResidual.models_mapProblem _ _ _).mp model⟩
  · rintro ⟨Future, future, candidate, model⟩
    refine ⟨Future, future, Assignment.compose candidate (reindex backward backwardPreserves), ?_⟩
    apply (ContextualResidual.models_mapProblem _ _ _).mpr
    rw [← Assignment.compose_associative,
      reindex_left_inverse forward backward forwardPreserves backwardPreserves leftInverse,
      Assignment.compose_identity_right]
    exact model

theorem guardRows_relocated (permutation : Equiv.Perm Nat) (rows : O → Row locals captures Γ sort) :
    (fun occurrence => (guardRows locals captures rows occurrence).map locals _
      (ContextualEventViewRelocation.assignment locals captures permutation)) = guardRows locals captures rows := by
  funext occurrence
  rw [guardRows, ContextualConditionalNaturality.row_map_compose,
    ContextualEventViewRelocation.capture_assignment_fixed]

theorem ask_relocated_iff (sourceLedger targetLedger : Finset Nat) (selection : Selection O)
    (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port selection,
      permutation (ContextualActivationScopes.scopeAt sourceLedger port) =
        ContextualActivationScopes.scopeAt targetLedger port)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures)
    (world : Finset O) (check : Check (Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort)) :
    ContextualConditionalGuards.Ask locals (information locals captures targetLedger selection rule rows before)
        (guardRows locals captures rows) world
        (check.map (instantiate (ContextualEventViewRelocation.assignment locals captures permutation))) ↔
      ContextualConditionalGuards.Ask locals (information locals captures sourceLedger selection rule rows before)
        (guardRows locals captures rows) world check := by
  have reflected := ContextualConditionalNaturality.ask_reindex_iff locals
    (ContextualEventViewRelocation.names permutation) (ContextualEventViewRelocation.names permutation.symm)
    (ContextualEventViewRelocation.preserves locals captures permutation)
    (ContextualEventViewRelocation.preserves locals captures permutation.symm)
    (ContextualEventViewRelocation.names_left_inverse permutation)
    (information locals captures sourceLedger selection rule rows before) (guardRows locals captures rows) world check
  change ContextualConditionalGuards.Ask locals
    (ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation)
      (information locals captures sourceLedger selection rule rows before))
    (fun occurrence => (guardRows locals captures rows occurrence).map locals _
      (ContextualEventViewRelocation.assignment locals captures permutation)) world _ ↔ _ at reflected
  rw [information_relocated locals captures sourceLedger targetLedger selection permutation aligned,
    guardRows_relocated] at reflected
  exact reflected

structure Admitted [DecidableEq O] (before : State locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort) : Prop where
  take_distinct : selection.taken.Nodup
  output_distinct : selection.made.Nodup
  take_length : rule.take.length = selection.taken.length
  read_length : rule.read.length = selection.read.length
  outputs : selection.made.map outputs =
    (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.produce
  taken_present : selection.taken.toFinset ⊆ before.present
  read_present : selection.read.toFinset ⊆ before.present
  apart : Disjoint selection.taken.toFinset selection.read.toFinset
  fresh : Disjoint selection.made.toFinset before.present
  solvable : Solvable (information locals before.declarations before.occupied selection rule before.rows before.equations)
  checks : ∀ check ∈ (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.checks,
    ContextualConditionalGuards.Ask locals
      (information locals before.declarations before.occupied selection rule before.rows before.equations)
      (guardRows locals before.declarations before.rows) before.present check

/-- Admission does not depend on the spelling of newly allocated scopes.
The source inventory, captured declarations and all original-cut checks
are retained. Scope coverage of the chosen occupied inventory is separate. -/
theorem Admitted.relocate [DecidableEq O] {before : State locals O Γ sort}
    {rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)}
    {selection : Selection O}
    {outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort}
    (admitted : Admitted locals before rule selection outputs)
    (occupied : Finset Nat) (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port selection,
      permutation (ContextualActivationScopes.scopeAt before.occupied port) =
        ContextualActivationScopes.scopeAt occupied port) :
    Admitted locals {before with occupied := occupied} rule selection
      (fun occurrence => instantiate (ContextualEventViewRelocation.assignment locals before.declarations permutation)
        (outputs occurrence)) := by
  have mappedRule := ContextualEventViewRelocation.prepared_rule_between_allocations locals before.declarations
    before.occupied occupied selection permutation aligned rule (fun occurrence => (before.rows occurrence).value)
  refine ⟨admitted.take_distinct, admitted.output_distinct, admitted.take_length, admitted.read_length,
    ?_, admitted.taken_present, admitted.read_present, admitted.apart, admitted.fresh, ?_, ?_⟩
  · have mapped := congrArg (List.map (instantiate
      (ContextualEventViewRelocation.assignment locals before.declarations permutation))) admitted.outputs
    exact (List.map_map ..).symm.trans (mapped.trans (congrArg RuleInstance.produce mappedRule))
  · have solved := (Solvable.reindex_iff
      (ContextualEventViewRelocation.names permutation) (ContextualEventViewRelocation.names permutation.symm)
      (ContextualEventViewRelocation.preserves locals before.declarations permutation)
      (ContextualEventViewRelocation.preserves locals before.declarations permutation.symm)
      (ContextualEventViewRelocation.names_left_inverse permutation)
      (information locals before.declarations before.occupied selection rule before.rows before.equations)).mpr admitted.solvable
    rw [show ContextualResidual.mapProblem
      (reindex (ContextualEventViewRelocation.names permutation)
        (ContextualEventViewRelocation.preserves locals before.declarations permutation))
      (information locals before.declarations before.occupied selection rule before.rows before.equations) = _ from
        information_relocated locals before.declarations before.occupied occupied selection permutation aligned
          rule before.rows before.equations] at solved
    exact solved
  · intro check member
    have checks := congrArg RuleInstance.checks mappedRule
    change List.map (Check.map (instantiate
      (ContextualEventViewRelocation.assignment locals before.declarations permutation)))
      (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
        (fun occurrence => (before.rows occurrence).value)).rule.checks = _ at checks
    rw [← checks] at member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (ask_relocated_iff locals before.declarations before.occupied occupied selection permutation aligned
      rule before.rows before.equations before.present original).mpr (admitted.checks original present)

theorem admitted_relocation_iff [DecidableEq O] (before : State locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (occupied : Finset Nat) (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port selection,
      permutation (ContextualActivationScopes.scopeAt before.occupied port) =
        ContextualActivationScopes.scopeAt occupied port) :
    Admitted locals {before with occupied := occupied} rule selection
        (fun occurrence => instantiate (ContextualEventViewRelocation.assignment locals before.declarations permutation)
          (outputs occurrence)) ↔ Admitted locals before rule selection outputs := by
  constructor
  · intro relocated
    have alignedBack (port : ContextualActivationScopes.Port selection) :
        permutation.symm (ContextualActivationScopes.scopeAt occupied port) =
          ContextualActivationScopes.scopeAt before.occupied port := by
      rw [← aligned port, permutation.symm_apply_apply]
    have restored := Admitted.relocate locals relocated before.occupied permutation.symm alignedBack
    have outputsRestored : (fun occurrence =>
        instantiate (ContextualEventViewRelocation.assignment locals before.declarations permutation.symm)
          (instantiate (ContextualEventViewRelocation.assignment locals before.declarations permutation) (outputs occurrence))) =
        outputs := by
      funext occurrence
      rw [← Assignment.instantiate_compose, ContextualEventViewRelocation.assignment_inverse, instantiate_identity]
    change Admitted locals before rule selection _ at restored
    rw [outputsRestored] at restored
    exact restored
  · intro admitted
    exact admitted.relocate locals occupied permutation aligned

/-- Empty latent conditions recover the previous semantic admission,
including its all-future guards and its physical occurrence discipline. -/
theorem admitted_ofEndpoint_iff [DecidableEq O] (before : ContextualExecution.Endpoint locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort) :
    Admitted locals (ofEndpoint locals before) rule selection outputs ↔
      ContextualGuardedStep.Valid locals before.declarations before.occupied selection rule
        before.inventory.rows before.inventory.configuration outputs := by
  have sameProblem := information_ofStored locals before.declarations before.occupied selection rule
    before.inventory.rows before.inventory.configuration
  have sameChecks (check : Check (Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)) :
      ContextualConditionalGuards.Ask locals
        (information locals before.declarations before.occupied selection rule
          (ofEndpoint locals before).rows (ofEndpoint locals before).equations)
        (guardRows locals before.declarations (ofEndpoint locals before).rows)
        before.inventory.configuration.present check ↔
      ContextualGuardSemantics.Ask locals
        (ContextualActivatedStep.problem locals before.declarations before.occupied selection rule
          before.inventory.rows before.inventory.configuration)
        (ContextualGuardedStep.guardRows locals before.declarations before.inventory.rows)
        before.inventory.configuration.present check := by
    rw [show information locals before.declarations before.occupied selection rule
      (ofEndpoint locals before).rows (ofEndpoint locals before).equations = _ from sameProblem]
    exact ContextualConditionalGuards.ask_ofStored locals _ _ _ _
  constructor
  · intro admitted
    refine ⟨⟨admitted.take_distinct, admitted.output_distinct, admitted.take_length, admitted.read_length,
      admitted.outputs, ⟨admitted.taken_present, admitted.read_present, admitted.apart, admitted.fresh, ?_⟩,
      (fun check member => (sameChecks check).mp (admitted.checks check member))⟩, ?_⟩
    · intro query member
      cases member
    · obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
      refine ⟨Future, future, candidate, ?_⟩
      exact (ContextualResidual.models_observeProblem candidate _).mp (sameProblem ▸ model)
  · intro admitted
    refine ⟨admitted.take_distinct, admitted.output_distinct, admitted.take_length, admitted.read_length,
      admitted.outputs, admitted.occurrences.taken_subset, admitted.occurrences.kept_subset,
      admitted.occurrences.apart, admitted.occurrences.fresh, ?_,
      (fun check member => (sameChecks check).mpr (admitted.checks check member))⟩
    obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
    refine ⟨Future, future, candidate, ?_⟩
    exact sameProblem.symm ▸ (ContextualResidual.models_observeProblem candidate _).mpr model

section Matching

variable [DecidableEq O] {before : State locals O Γ sort}
    {rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)}
    {selection : Selection O}
    {outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort}

omit [DecidableEq O] in
theorem take_conditions {Next : Type} {next : Next → MetaArity S}
    (candidate : Assignment (ContextualActivatedStep.target locals before.declarations) next)
    (model : ContextualResidual.Models candidate
      (information locals before.declarations before.occupied selection rule before.rows before.equations))
    (port : Fin selection.taken.length) :
    ContextualResidual.Models candidate ((before.rows (selection.taken.get port)).obligationsAt locals before.declarations
      (ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.takePort selection port))) := by
  have selected := (ContextualResidual.models_append candidate _ _).mp model |>.2
  have takes := (ContextualResidual.models_append candidate _ _).mp selected |>.1
  intro equation member
  exact takes equation (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨port, rfl⟩, member⟩)

theorem take_matches {Next : Type} {next : Next → MetaArity S}
    (admitted : Admitted locals before rule selection outputs)
    (candidate : Assignment (ContextualActivatedStep.target locals before.declarations) next)
    (model : ContextualResidual.Models candidate
      (information locals before.declarations before.occupied selection rule before.rows before.equations))
    (port : Fin selection.taken.length) :
    Matches locals before.declarations (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals before.declarations))
      (instantiate candidate ((ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
        (fun occurrence => (before.rows occurrence).value)).rule.take.get
          ⟨port.val, by simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
            ContextualFreshening.ruleAt, RuleInstance.map, List.length_map, admitted.take_length] using port.isLt⟩))
      (before.rows (selection.taken.get port)) := by
  have initial := (ContextualResidual.models_append candidate _ _).mp model |>.1
  have observed := (ContextualResidual.models_append candidate _ _).mp initial |>.2
  have equations := (ContextualResidual.models_observeProblem candidate _).mp observed
  have takes := (ContextualFrameUnifier.models_append candidate _ _).mp
    ((ContextualFrameUnifier.models_append candidate _ _).mp equations).1 |>.1
  have shape : (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.take.length =
      (List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
        (fun occurrence => (before.rows occurrence).value)).taken).length := by
    simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare, ContextualFreshening.ruleAt,
      RuleInstance.map, List.length_map, List.length_ofFn] using admitted.take_length
  have paired := (ContextualActivatedStep.models_useEquations_iff locals before.declarations candidate _ _ shape).mp takes
  have valueBound : port.val < (List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).taken).length := by simpa only [List.length_ofFn] using port.isLt
  have patternBound : port.val < (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.take.length := shape.symm ▸ valueBound
  have equal := paired.get patternBound valueBound
  apply matches_of_open locals before.declarations _ candidate _ _ (take_conditions locals candidate model port)
  have value := (List.get_ofFn _ ⟨port.val, by simpa only [List.length_ofFn] using port.isLt⟩).trans
    (ContextualActivatedStep.prepared_taken_view locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value) port)
  exact (congrArg (instantiate candidate) value).symm.trans equal.symm

omit [DecidableEq O] in
theorem read_conditions {Next : Type} {next : Next → MetaArity S}
    (candidate : Assignment (ContextualActivatedStep.target locals before.declarations) next)
    (model : ContextualResidual.Models candidate
      (information locals before.declarations before.occupied selection rule before.rows before.equations))
    (port : Fin selection.read.length) :
    ContextualResidual.Models candidate ((before.rows (selection.read.get port)).obligationsAt locals before.declarations
      (ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.readPort selection port))) := by
  have selected := (ContextualResidual.models_append candidate _ _).mp model |>.2
  have reads := (ContextualResidual.models_append candidate _ _).mp selected |>.2
  intro equation member
  exact reads equation (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨port, rfl⟩, member⟩)

theorem read_matches {Next : Type} {next : Next → MetaArity S}
    (admitted : Admitted locals before rule selection outputs)
    (candidate : Assignment (ContextualActivatedStep.target locals before.declarations) next)
    (model : ContextualResidual.Models candidate
      (information locals before.declarations before.occupied selection rule before.rows before.equations))
    (port : Fin selection.read.length) :
    Matches locals before.declarations (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals before.declarations))
      (instantiate candidate ((ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
        (fun occurrence => (before.rows occurrence).value)).rule.read.get
          ⟨port.val, by simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
            ContextualFreshening.ruleAt, RuleInstance.map, List.length_map, admitted.read_length] using port.isLt⟩))
      (before.rows (selection.read.get port)) := by
  have initial := (ContextualResidual.models_append candidate _ _).mp model |>.1
  have observed := (ContextualResidual.models_append candidate _ _).mp initial |>.2
  have equations := (ContextualResidual.models_observeProblem candidate _).mp observed
  have reads := (ContextualFrameUnifier.models_append candidate _ _).mp
    ((ContextualFrameUnifier.models_append candidate _ _).mp equations).1 |>.2
  have shape : (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.read.length =
      (List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
        (fun occurrence => (before.rows occurrence).value)).read).length := by
    simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare, ContextualFreshening.ruleAt,
      RuleInstance.map, List.length_map, List.length_ofFn] using admitted.read_length
  have paired := (ContextualActivatedStep.models_useEquations_iff locals before.declarations candidate _ _ shape).mp reads
  have valueBound : port.val < (List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).read).length := by simpa only [List.length_ofFn] using port.isLt
  have patternBound : port.val < (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.read.length := shape.symm ▸ valueBound
  have equal := paired.get patternBound valueBound
  apply matches_of_open locals before.declarations _ candidate _ _ (read_conditions locals candidate model port)
  have value := (List.get_ofFn _ ⟨port.val, by simpa only [List.length_ofFn] using port.isLt⟩).trans
    (ContextualActivatedStep.prepared_read_view locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value) port)
  exact (congrArg (instantiate candidate) value).symm.trans equal.symm

end Matching

section Execution

variable [DecidableEq Local] [DecidableEq O] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

structure Firing (before : State locals O Γ sort) : Type 1 where
  rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)
  selection : Selection O
  outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort
  reusable : O → Bool
  admitted : Admitted locals before rule selection outputs
  fuel : Nat
  update : ContextualFrameUpdate.Update
    (information locals before.declarations before.occupied selection rule before.rows before.equations)
  computed : letI := before.equality
    ContextualFrameWorklist.run fuel (ContextualActivatedStep.target locals before.declarations)
      (information locals before.declarations before.occupied selection rule before.rows before.equations) = .residual update

namespace Firing

variable {locals} {before : State locals O Γ sort}

abbrev target (firing : Firing locals before) :
    State (ContextualPublication.privateFamily locals firing.update.declaration) O Γ sort where
  Names := (Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names) ⊕ (firing.update.Variables ⊕ Empty)
  equality := by let _ := before.equality; let _ := firing.update.equality; infer_instance
  declarations := ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals before.declarations) firing.update.declaration
  occupied := ContextualFreshFrameScopeLedger.helperLedger (ContextualActivationScopes.after before.occupied firing.selection)
  equations := ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource firing.update)
    (information locals before.declarations before.occupied firing.selection firing.rule before.rows before.equations)
  present := fire before.present (firing.selection.commit (T := Unit))
  rows occurrence :=
    if occurrence ∈ firing.selection.made then
      if firing.reusable occurrence then
        ContextualConditionalPublication.ordinary locals firing.update.declaration _
          (ContextualConditionalAnswers.ofUpdate firing.update (firing.outputs occurrence))
      else ofStored _ _ (.shared (instantiate (ContextualComputedFreshFrame.includeSource firing.update) (firing.outputs occurrence)))
    else ContextualConditionalPublication.extendPrivate locals firing.update.declaration _
      ((before.rows occurrence).map locals before.declarations
        (Assignment.compose (ContextualComputedFreshFrame.includeSource firing.update)
          (ContextualSelectionViews.capturedTarget locals before.declarations)))

theorem physical_result (firing : Firing locals before) :
    firing.target.present = fire before.present (firing.selection.commit (T := Unit)) := rfl

theorem ordinary_matches_source (firing : Firing locals before) (occurrence : O)
    (made : occurrence ∈ firing.selection.made) (ordinary : firing.reusable occurrence = true)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals firing.update.declaration) firing.target.declarations candidate pattern
      (firing.target.rows occurrence) ↔
    ContextualPublication.SourceInstances
      (information locals before.declarations before.occupied firing.selection firing.rule before.rows before.equations)
      (firing.outputs occurrence) next pattern := by
  change Matches _ _ candidate pattern (if _ then (if _ then _ else _) else _) ↔ _
  rw [if_pos made, if_pos ordinary]
  exact ContextualConditionalPublication.update_matches_source locals firing.target.declarations firing.update candidate _ pattern

/-- Ordinary conditional outputs of separate solver runs have the same
instances after scope relocation, even when their returned families differ.
This readout keeps residual conditions but hides private helper identities;
it makes no claim about shared or selectively captured recipe outputs. -/
theorem relocated_ordinary_matches (firing : Firing locals before) (occupied : Finset Nat)
    (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port firing.selection,
      permutation (ContextualActivationScopes.scopeAt before.occupied port) =
        ContextualActivationScopes.scopeAt occupied port)
    (moved : Firing locals {before with occupied := occupied})
    (sameRule : moved.rule = firing.rule) (sameSelection : moved.selection = firing.selection)
    (occurrence : O) (made : occurrence ∈ firing.selection.made)
    (sameOutput : moved.outputs occurrence = instantiate
      (ContextualEventViewRelocation.assignment locals before.declarations permutation) (firing.outputs occurrence))
    (reusable : firing.reusable occurrence = true) (movedReusable : moved.reusable occurrence = true)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment firing.target.declarations next)
    (movedCandidate : Assignment moved.target.declarations next)
    (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals firing.update.declaration) firing.target.declarations
        candidate pattern (firing.target.rows occurrence) ↔
      Matches (ContextualPublication.privateFamily locals moved.update.declaration) moved.target.declarations
        movedCandidate pattern (moved.target.rows occurrence) := by
  have movedMade : occurrence ∈ moved.selection.made := by rwa [sameSelection]
  rw [firing.ordinary_matches_source occurrence made reusable next candidate pattern,
    moved.ordinary_matches_source occurrence movedMade movedReusable next movedCandidate pattern]
  rw [sameRule, sameSelection, sameOutput]
  rw [← information_relocated locals before.declarations before.occupied occupied firing.selection permutation aligned]
  exact (ContextualConditionalNaturality.sourceInstances_reindex_iff
    (ContextualEventViewRelocation.names permutation) (ContextualEventViewRelocation.names permutation.symm)
    (ContextualEventViewRelocation.preserves locals before.declarations permutation)
    (ContextualEventViewRelocation.preserves locals before.declarations permutation.symm)
    (ContextualEventViewRelocation.names_left_inverse permutation) _ _ next pattern).symm

theorem retained_matches (firing : Firing locals before) (occurrence : O)
    (notMade : occurrence ∉ firing.selection.made) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals firing.update.declaration) firing.target.declarations
      candidate pattern (firing.target.rows occurrence) ↔
    Matches locals before.declarations
      (Assignment.compose candidate (Assignment.compose (ContextualComputedFreshFrame.includeSource firing.update)
        (ContextualSelectionViews.capturedTarget locals before.declarations))) pattern (before.rows occurrence) := by
  change Matches _ _ candidate pattern (if _ then _ else _) ↔ _
  rw [if_neg notMade, ContextualConditionalPublication.extendPrivate_matches_iff, matches_map_iff]

theorem shared_row (firing : Firing locals before) (occurrence : O)
    (made : occurrence ∈ firing.selection.made) (isShared : firing.reusable occurrence = false) :
    firing.target.rows occurrence = ofStored _ _ (.shared
      (instantiate (ContextualComputedFreshFrame.includeSource firing.update) (firing.outputs occurrence))) := by
  change (if _ then (if _ then _ else _) else _) = _
  rw [if_pos made, isShared]
  rfl

/-- The returned solver declarations extend the firing's information frame. -/
def resultFrame (firing : Firing locals before) :
    ContextualGuardMatching.Extension (ContextualActivatedStep.target locals before.declarations) where
  Names := firing.target.Names
  declarations := firing.target.declarations
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

theorem resultFrame_assignment (firing : Firing locals before) :
    firing.resultFrame.assignment = ContextualComputedFreshFrame.includeSource firing.update := by
  funext name
  exact (ContextualFreshFrameScopeLedger.includeSource_image firing.update name).symm

/-- Every returned model projects to the firing's information problem. -/
theorem model_projects (firing : Firing locals before) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment firing.target.declarations next)
    (model : ContextualResidual.Models candidate firing.target.equations) :
    ContextualResidual.Models (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
      (information locals before.declarations before.occupied firing.selection firing.rule before.rows before.equations) :=
  (ContextualResidual.models_mapProblem _ _ _).mp model

/-- Every given information model extends through the returned helper frame,
with its original names fixed by the resulting square. -/
theorem model_extends (firing : Firing locals before) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment (ContextualActivatedStep.target locals before.declarations) next)
    (model : ContextualResidual.Models candidate
      (information locals before.declarations before.occupied firing.selection firing.rule before.rows before.equations)) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ realized : Assignment firing.target.declarations extension.declarations,
        ContextualResidual.Models realized firing.target.equations ∧
          Assignment.compose realized (ContextualComputedFreshFrame.includeSource firing.update) =
            Assignment.compose extension.assignment candidate := by
  let extension := ContextualGuardMatching.Extension.withLocals firing.resultFrame.complementDeclarations next
  refine ⟨extension, firing.resultFrame.liftModel candidate, ?_, ?_⟩
  · change ContextualResidual.Models _ (ContextualResidual.mapProblem
      (ContextualComputedFreshFrame.includeSource firing.update) _)
    rw [← firing.resultFrame_assignment]
    exact (ContextualConditionalNaturality.models_liftModel_iff firing.resultFrame candidate _).mpr model
  · rw [← firing.resultFrame_assignment]
    exact firing.resultFrame.liftModel_square candidate

theorem target_solvable (firing : Firing locals before) : Solvable firing.target.equations := by
  change Solvable (ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource firing.update) _)
  rw [← firing.resultFrame_assignment]
  exact (ContextualConditionalNaturality.solvable_extension_iff firing.resultFrame _).mpr firing.admitted.solvable

/-- Reuse flags are metadata of the same admitted execution and solver return. -/
def withReuse (firing : Firing locals before) (reuse : O → Bool) : Firing locals before :=
  { firing with reusable := reuse }

/-- A row observer cannot see reuse flags outside the made ports. -/
theorem withReuse_rows (firing : Firing locals before) (reuse : O → Bool)
    (same : ∀ occurrence ∈ firing.selection.made, reuse occurrence = firing.reusable occurrence) :
    (firing.withReuse reuse).target.rows = firing.target.rows := by
  funext occurrence
  change (if occurrence ∈ firing.selection.made then (if reuse occurrence then _ else _) else _) = _
  by_cases made : occurrence ∈ firing.selection.made
  · simp only [target, if_pos made, same occurrence made]
    rfl
  · simp only [target, if_neg made]
    rfl

end Firing

/-- Publication contracts either specify every reuse flag or only those
at made ports. Flags outside made ports are unobserved by a port contract. -/
inductive ReuseIntent (Occurrence : Type) where
  | all : (Occurrence → Bool) → ReuseIntent Occurrence
  | made : List Bool → ReuseIntent Occurrence

abbrev ReuseIntent.Holds (intent : ReuseIntent O) (made : List O) (flags : O → Bool) : Prop :=
  match intent with
  | .all expected => flags = expected
  | .made expected => made.map flags = expected

/-- One actual execution with its constructed rule, selection, output code
and reuse contract pinned. Source-specific publication decoders use this
record; they do not introduce another execution witness. -/
structure Published (before : State locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (reuse : ReuseIntent O) where
  firing : Firing locals before
  authored : firing.rule = rule
  selected : firing.selection = selection
  values : firing.outputs = outputs
  intents : reuse.Holds selection.made firing.reusable

/-- Every admitted source operation has an actual conditional solver return
at every finite budget. A nonempty residual queue is preserved in outputs;
it is not interpreted as a completion certificate. -/
theorem realize_at_fuel (before : State locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (reusable : O → Bool) (admitted : Admitted locals before rule selection outputs) (fuel : Nat) :
    ∃ firing : Firing locals before, firing.rule = rule ∧ firing.selection = selection ∧
      firing.outputs = outputs ∧ firing.reusable = reusable ∧ firing.fuel = fuel := by
  let _ := before.equality
  cases computed : ContextualFrameWorklist.run fuel (ContextualActivatedStep.target locals before.declarations)
      (information locals before.declarations before.occupied selection rule before.rows before.equations) with
  | refuted impossible =>
      obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
      exact False.elim (impossible future candidate model)
  | residual update => exact ⟨⟨rule, selection, outputs, reusable, admitted, fuel, update, computed⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- A relocated admission is realized by a new run of the actual solver at
the requested budget. No equality of the two returned helper families is
assumed; physical effects agree because occurrence identities are fixed. -/
theorem Firing.relocate_exists {before : State locals O Γ sort} (firing : Firing locals before)
    (occupied : Finset Nat) (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port firing.selection,
      permutation (ContextualActivationScopes.scopeAt before.occupied port) =
        ContextualActivationScopes.scopeAt occupied port) (fuel : Nat) :
    ∃ moved : Firing locals {before with occupied := occupied},
      moved.rule = firing.rule ∧ moved.selection = firing.selection ∧
        moved.outputs = (fun occurrence => instantiate
          (ContextualEventViewRelocation.assignment locals before.declarations permutation) (firing.outputs occurrence)) ∧
        moved.reusable = firing.reusable ∧ moved.fuel = fuel ∧ moved.target.present = firing.target.present := by
  obtain ⟨moved, rule, selection, outputs, reusable, budget⟩ := realize_at_fuel locals
    {before with occupied := occupied} firing.rule firing.selection _ firing.reusable
    (firing.admitted.relocate locals occupied permutation aligned) fuel
  refine ⟨moved, rule, selection, outputs, reusable, budget, ?_⟩
  rw [moved.physical_result, firing.physical_result, selection]

end Execution

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution
