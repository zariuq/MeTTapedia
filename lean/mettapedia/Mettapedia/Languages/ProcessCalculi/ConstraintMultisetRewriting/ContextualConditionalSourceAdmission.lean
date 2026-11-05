import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalSourceProblem

/-!
# Conditional-input source admission agrees with the actual firing

The source judgment retains physical occurrences, shared query bindings,
per-use row variables, latent equations and original-cut guard observations.
It does not assume a native execution or an answer supplied by an evaluator.
The value-only source semantics is recovered when row conditions are empty.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalSourceAdmission

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualClauseFrames ContextualConditionalRows ContextualConditionalNaturality
open ContextualConditionalSourceProblem

variable {S : Signature} {Query Local Shared Next O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

theorem extendPrivate_map (change : Assignment captures next) (row : Row locals captures Γ sort) :
    (ContextualConditionalPublication.extendPrivate locals queries captures row).map (bank queries locals) captures change =
      ContextualConditionalPublication.extendPrivate locals queries next (row.map locals captures change) := by
  have square : Assignment.compose (ContextualStoredRows.liftCaptures (bank queries locals) change)
      (ContextualPublication.includePrivate locals queries) =
      Assignment.compose (ContextualPublication.includePrivate locals queries) (ContextualStoredRows.liftCaptures locals change) := by
    funext name
    have old := ContextualClauseAdmission.extendPrivate_map queries locals captures change
      (.schema (generator (ContextualSelectionViews.source locals captures) name))
    have bodies := ContextualStoredRows.Row.schema.inj old
    change instantiate (ContextualStoredRows.liftCaptures (bank queries locals) change)
      (instantiate (ContextualPublication.includePrivate locals queries) (generator _ name)) =
      instantiate (ContextualPublication.includePrivate locals queries)
        (instantiate (ContextualStoredRows.liftCaptures locals change) (generator _ name)) at bodies
    simpa only [Assignment.compose, instantiate_generator] using bodies
  cases row with
  | mk value obligations =>
      change ContextualConditionalRows.Row.mk
        ((ContextualPublication.extendPrivate locals queries value).map (bank queries locals) change)
        (ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ obligations)) =
        ContextualConditionalRows.Row.mk (ContextualPublication.extendPrivate locals queries (value.map locals change))
          (ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ obligations))
      rw [ContextualClauseAdmission.extendPrivate_map, map_problem_compose, map_problem_compose, square]

def sourceRows (rows : O → Row locals captures Γ sort) :=
  fun occurrence => (rows occurrence).map locals captures (captureEmbedding queries locals captures)

theorem guard_rows (occupied : Finset Nat) (rows : O → Row locals captures Γ sort) :
    ContextualConditionalExecution.guardRows (bank queries locals) captures (nativeRows queries locals captures rows) =
      fun occurrence => ContextualConditionalPublication.extendPrivate locals queries _
        ((sourceRows queries locals captures rows occurrence).map locals _ (frame queries locals captures occupied).assignment) := by
  funext occurrence
  change (ContextualConditionalPublication.extendPrivate locals queries captures (rows occurrence)).map (bank queries locals)
      captures (ContextualSelectionViews.capturedTarget (bank queries locals) captures) =
    ContextualConditionalPublication.extendPrivate locals queries _
      (((rows occurrence).map locals captures (captureEmbedding queries locals captures)).map locals _
        (frame queries locals captures occupied).assignment)
  rw [row_map_compose, captures_square]
  exact extendPrivate_map queries locals captures _ _

theorem check_iff (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures) (world : Finset O)
    (check : Check (Term (signature S (queryFamily queries captures)) Γ sort)) :
    ContextualConditionalGuards.Ask (bank queries locals)
      (ContextualConditionalExecution.information (bank queries locals) captures occupied selection
        (ContextualClauseProblem.nativeRule queries locals captures code) (nativeRows queries locals captures rows) before)
      (ContextualConditionalExecution.guardRows (bank queries locals) captures (nativeRows queries locals captures rows)) world
      ((check.map (queryView queries locals captures)).map (instantiate (frame queries locals captures occupied).assignment)) ↔
    ContextualConditionalGuards.Ask locals (problem queries locals captures selection code rows before)
      (sourceRows queries locals captures rows) world (check.map (queryView queries locals captures)) := by
  rw [actual_information, guard_rows]
  exact (ask_extendPrivate locals queries _ _ _ _).trans
    (ask_extension_iff locals (frame queries locals captures occupied) _ _ _ _)

structure Admitted [DecidableEq O] (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures) (world : Finset O) : Prop where
  take_distinct : selection.taken.Nodup
  output_distinct : selection.made.Nodup
  take_shape : code.take.length = selection.taken.length
  read_shape : code.read.length = selection.read.length
  output_shape : selection.made.length = code.produce.length
  taken_present : selection.taken.toFinset ⊆ world
  read_present : selection.read.toFinset ⊆ world
  apart : Disjoint selection.taken.toFinset selection.read.toFinset
  fresh : Disjoint selection.made.toFinset world
  solvable : ContextualConditionalExecution.Solvable (problem queries locals captures selection code rows before)
  checks : ∀ check ∈ code.checks, ContextualConditionalGuards.Ask locals
    (problem queries locals captures selection code rows before) (sourceRows queries locals captures rows)
    world (check.map (queryView queries locals captures))

def outputs [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) :=
  ContextualClauseAdmission.outputs queries locals captures occupied selection code (fun occurrence => (rows occurrence).value)

theorem prepared_rule (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) :
    (ContextualActivatedStep.prepared (bank queries locals) captures occupied selection
      (ContextualClauseProblem.nativeRule queries locals captures code)
      (fun occurrence => (nativeRows queries locals captures rows occurrence).value)).rule =
    (code.map (queryView queries locals captures)).map (instantiate (frame queries locals captures occupied).assignment) :=
  ContextualClauseProblem.prepared_rule queries locals captures occupied selection code (fun occurrence => (rows occurrence).value)

theorem admitted_iff [DecidableEq O] (before : ContextualConditionalExecution.State locals O Γ sort)
    (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries before.declarations)) Γ sort)) :
    Admitted queries locals before.declarations selection code before.rows before.equations before.present ↔
    ContextualConditionalExecution.Admitted (bank queries locals) (prepareState queries locals before)
      (ContextualClauseProblem.nativeRule queries locals before.declarations code) selection
      (outputs queries locals before.declarations before.occupied selection code before.rows) := by
  have solution : ContextualConditionalExecution.Solvable
      (ContextualConditionalExecution.information (bank queries locals) before.declarations before.occupied selection
        (ContextualClauseProblem.nativeRule queries locals before.declarations code)
        (nativeRows queries locals before.declarations before.rows) before.equations) ↔
    ContextualConditionalExecution.Solvable
      (problem queries locals before.declarations selection code before.rows before.equations) := by
    rw [actual_information]
    exact solvable_extension_iff (frame queries locals before.declarations before.occupied) _
  constructor
  · intro source
    refine ⟨source.take_distinct, source.output_distinct, ?_, ?_, ?_, source.taken_present, source.read_present,
      source.apart, source.fresh, solution.mpr source.solvable, ?_⟩
    · change (code.take.map (instantiate (actor queries locals before.declarations))).length = selection.taken.length
      simpa only [List.length_map] using source.take_shape
    · change (code.read.map (instantiate (actor queries locals before.declarations))).length = selection.read.length
      simpa only [List.length_map] using source.read_shape
    · exact ContextualClauseAdmission.output_shape queries locals before.declarations before.occupied selection code
        (fun occurrence => (before.rows occurrence).value) source.output_distinct source.output_shape
    · intro check member
      change check ∈ (ContextualActivatedStep.prepared (bank queries locals) before.declarations before.occupied selection
        (ContextualClauseProblem.nativeRule queries locals before.declarations code)
        (fun occurrence => (nativeRows queries locals before.declarations before.rows occurrence).value)).rule.checks at member
      rw [prepared_rule] at member
      obtain ⟨mapped, mappedMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp mappedMember
      exact (check_iff queries locals before.declarations before.occupied selection code before.rows before.equations
        before.present original).mpr (source.checks original originalMember)
  · intro actual
    refine ⟨actual.take_distinct, actual.output_distinct, ?_, ?_, ?_, actual.taken_present, actual.read_present,
      actual.apart, actual.fresh, solution.mp actual.solvable, ?_⟩
    · have shape : (code.take.map (instantiate (actor queries locals before.declarations))).length = selection.taken.length :=
        actual.take_length
      simpa only [List.length_map] using shape
    · have shape : (code.read.map (instantiate (actor queries locals before.declarations))).length = selection.read.length :=
        actual.read_length
      simpa only [List.length_map] using shape
    · have shape := congrArg List.length actual.outputs
      change (selection.made.map (outputs queries locals before.declarations before.occupied selection code before.rows)).length =
        ((code.produce.map (instantiate (actor queries locals before.declarations))).map
          (ContextualFreshening.termAt (bank queries locals) before.declarations
            (ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.rulePort selection)))).length at shape
      simpa only [List.length_map] using shape
    · intro check member
      apply (check_iff queries locals before.declarations before.occupied selection code before.rows before.equations
        before.present check).mp
      apply actual.checks
      change (check.map (queryView queries locals before.declarations)).map
          (instantiate (frame queries locals before.declarations before.occupied).assignment) ∈
        (ContextualActivatedStep.prepared (bank queries locals) before.declarations before.occupied selection
          (ContextualClauseProblem.nativeRule queries locals before.declarations code)
          (fun occurrence => (nativeRows queries locals before.declarations before.rows occurrence).value)).rule.checks
      rw [prepared_rule]
      exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨check, member, rfl⟩, rfl⟩

theorem admitted_ofEndpoint_iff [DecidableEq O] (before : ContextualExecution.Endpoint locals O Γ sort)
    (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries before.declarations)) Γ sort)) :
    Admitted queries locals before.declarations selection code
      (ContextualConditionalExecution.ofEndpoint locals before).rows
      (ContextualConditionalExecution.ofEndpoint locals before).equations before.inventory.configuration.present ↔
    ContextualClauseAdmission.Admitted queries locals before.declarations selection code before.inventory.rows before.inventory.configuration := by
  have sameProblem := problem_ofStored queries locals before.declarations selection code before.inventory.rows before.inventory.configuration
  have sameChecks (check : Check (Term (signature S (queryFamily queries before.declarations)) Γ sort)) :
      ContextualConditionalGuards.Ask locals
        (problem queries locals before.declarations selection code (ContextualConditionalExecution.ofEndpoint locals before).rows
          (ContextualConditionalExecution.ofEndpoint locals before).equations)
        (sourceRows queries locals before.declarations (ContextualConditionalExecution.ofEndpoint locals before).rows)
        before.inventory.configuration.present (check.map (queryView queries locals before.declarations)) ↔
      ContextualGuardSemantics.Ask locals
        (ContextualClauseProblem.problem queries locals before.declarations selection code before.inventory.rows before.inventory.configuration)
        (ContextualClauseAdmission.sourceRows queries locals before.declarations before.inventory.rows)
        before.inventory.configuration.present (check.map (queryView queries locals before.declarations)) := by
    rw [show problem queries locals before.declarations selection code
      (ContextualConditionalExecution.ofEndpoint locals before).rows
      (ContextualConditionalExecution.ofEndpoint locals before).equations = _ from sameProblem]
    exact ContextualConditionalGuards.ask_ofStored locals _ _ _ _
  constructor
  · intro source
    refine ⟨source.take_distinct, source.output_distinct, source.take_shape, source.read_shape, source.output_shape,
      source.taken_present, source.read_present, source.apart, source.fresh, ?_,
      fun check member => (sameChecks check).mp (source.checks check member)⟩
    obtain ⟨Future, future, candidate, model⟩ := source.solvable
    exact ⟨Future, future, candidate, (ContextualResidual.models_observeProblem candidate _).mp (sameProblem ▸ model)⟩
  · intro source
    refine ⟨source.take_distinct, source.output_distinct, source.take_shape, source.read_shape, source.output_shape,
      source.taken_present, source.read_present, source.apart, source.fresh, ?_,
      fun check member => (sameChecks check).mpr (source.checks check member)⟩
    obtain ⟨Future, future, candidate, model⟩ := source.solvable
    exact ⟨Future, future, candidate, sameProblem.symm ▸ (ContextualResidual.models_observeProblem candidate _).mpr model⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalSourceAdmission
