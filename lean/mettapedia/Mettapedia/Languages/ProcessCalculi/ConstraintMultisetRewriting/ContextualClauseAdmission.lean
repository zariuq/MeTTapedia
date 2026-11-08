import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAsks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplateSource

/-!
# Independent source-clause admission and native admission agree

The source judgment states occurrence discipline, future-family solvability
of its joint query/body problem, and its original guard asks. Compilation
constructs the output labels from the authored production list. No solver
answer, output oracle or host evaluator is an admission premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseAdmission

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualClauseFrames ContextualClauseProblem

variable {S : Signature} {Query Local Shared Next O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

theorem extendPrivate_map (change : Assignment captures next)
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    (ContextualPublication.extendPrivate locals queries row).map (bank queries locals) change =
      ContextualPublication.extendPrivate locals queries (row.map locals change) := by
  cases row with
  | shared value => rfl
  | schema body =>
      change ContextualStoredRows.Row.schema
        (instantiate (ContextualStoredRows.liftCaptures (bank queries locals) change)
          (instantiate (ContextualPublication.includePrivate locals queries) body)) =
        ContextualStoredRows.Row.schema
          (instantiate (ContextualPublication.includePrivate locals queries)
            (instantiate (ContextualStoredRows.liftCaptures locals change) body))
      congr 1
      rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
      apply congrArg (fun assignment => instantiate assignment body)
      funext name
      cases name with
      | inl name =>
          change instantiate (ContextualStoredRows.liftCaptures (bank queries locals) change)
              (generator _ (.inl (.inl name))) =
            instantiate (ContextualPublication.includePrivate locals queries) (generator _ (.inl name))
          rw [instantiate_generator, instantiate_generator]
          rfl
      | inr name =>
          change instantiate (ContextualStoredRows.liftCaptures (bank queries locals) change)
              (generator _ (.inr name)) =
            instantiate (ContextualPublication.includePrivate locals queries)
              (instantiate (ContextualSelectionViews.capturedSource locals next) (change name))
          rw [instantiate_generator, ← Assignment.instantiate_compose]
          have same : Assignment.compose (ContextualPublication.includePrivate locals queries)
              (ContextualSelectionViews.capturedSource locals next) =
              ContextualSelectionViews.capturedSource (bank queries locals) next := by
            funext identity
            exact instantiate_generator _ _
          rw [same]
          rfl

def sourceRows (rows : O → ContextualStoredRows.Row locals captures Γ sort) :=
  fun occurrence => (rows occurrence).map locals (captureEmbedding queries locals captures)

theorem guard_rows (occupied : Finset Nat) (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    ContextualGuardedStep.guardRows (bank queries locals) captures (nativeRows queries locals captures rows) =
      fun occurrence => ContextualPublication.extendPrivate locals queries
        ((sourceRows queries locals captures rows occurrence).map locals (frame queries locals captures occupied).assignment) := by
  funext occurrence
  change (ContextualPublication.extendPrivate locals queries (rows occurrence)).map (bank queries locals)
      (ContextualSelectionViews.capturedTarget (bank queries locals) captures) =
    ContextualPublication.extendPrivate locals queries (((rows occurrence).map locals
      (captureEmbedding queries locals captures)).map locals (frame queries locals captures occupied).assignment)
  rw [ContextualStoredRows.Row.map_compose, captures_square]
  exact extendPrivate_map queries locals captures _ _

theorem check_iff (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (check : Check (Term (signature S (queryFamily queries captures)) Γ sort)) :
    ContextualGuardSemantics.Ask (bank queries locals)
      (ContextualActivatedStep.problem (bank queries locals) captures occupied selection
        (nativeRule queries locals captures code) (nativeRows queries locals captures rows) before)
      (ContextualGuardedStep.guardRows (bank queries locals) captures (nativeRows queries locals captures rows))
      before.present ((check.map (queryView queries locals captures)).map
        (instantiate (frame queries locals captures occupied).assignment)) ↔
    ContextualGuardSemantics.Ask locals (problem queries locals captures selection code rows before)
      (sourceRows queries locals captures rows) before.present (check.map (queryView queries locals captures)) := by
  rw [actual_problem, guard_rows queries locals captures occupied]
  exact (ContextualPublication.ask_extendPrivate locals queries _ _ _ _).trans
    (ContextualGuardSemantics.Ask.extension_iff locals (frame queries locals captures occupied) _ _ _ _)

structure Admitted [DecidableEq O] (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) : Prop where
  take_distinct : selection.taken.Nodup
  output_distinct : selection.made.Nodup
  take_shape : code.take.length = selection.taken.length
  read_shape : code.read.length = selection.read.length
  output_shape : selection.made.length = code.produce.length
  taken_present : selection.taken.toFinset ⊆ before.present
  read_present : selection.read.toFinset ⊆ before.present
  apart : Disjoint selection.taken.toFinset selection.read.toFinset
  fresh : Disjoint selection.made.toFinset before.present
  solvable : ContextualFrameUnifier.Solvable (problem queries locals captures selection code rows before)
  checks : ∀ check ∈ code.checks,
    ContextualGuardSemantics.Ask locals (problem queries locals captures selection code rows before)
      (sourceRows queries locals captures rows) before.present (check.map (queryView queries locals captures))

def outputs [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) : O → Term (signature S (nativeActive queries locals captures)) Γ sort :=
  let values := (ContextualActivatedStep.prepared (bank queries locals) captures occupied selection
    (nativeRule queries locals captures code) (nativeRows queries locals captures rows)).rule.produce
  fun occurrence => (ContextualTemplateSource.assign selection.made values occurrence).getD
    (ContextualStoredRows.viewAt (bank queries locals) captures (ContextualActivationScopes.start occupied)
      (nativeRows queries locals captures rows occurrence))

theorem output_shape [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (distinct : selection.made.Nodup) (shape : selection.made.length = code.produce.length) :
    selection.made.map (outputs queries locals captures occupied selection code rows) =
      (ContextualActivatedStep.prepared (bank queries locals) captures occupied selection
        (nativeRule queries locals captures code) (nativeRows queries locals captures rows)).rule.produce := by
  apply ContextualTemplateSource.assign_map selection.made _ _ distinct
  simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare, nativeRule,
    ContextualFreshening.ruleAt, RuleInstance.map, List.length_map] using shape

/-- Both directions retain the same physical selection and the entire
source binding problem. The compiler supplies output labels itself. -/
theorem admitted_iff [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    Admitted queries locals captures selection code rows before ↔
    ContextualGuardedStep.Valid (bank queries locals) captures occupied selection
      (nativeRule queries locals captures code) (nativeRows queries locals captures rows) before
      (outputs queries locals captures occupied selection code rows) := by
  constructor
  · intro source
    refine ⟨⟨source.take_distinct, source.output_distinct, ?_, ?_, output_shape queries locals captures occupied selection code rows
      source.output_distinct source.output_shape, ?_, ?_⟩,
      (solvable_iff queries locals captures occupied selection code rows before).mpr source.solvable⟩
    · simpa only [nativeRule, RuleInstance.map, List.length_map] using source.take_shape
    · simpa only [nativeRule, RuleInstance.map, List.length_map] using source.read_shape
    · exact ⟨source.taken_present, source.read_present, source.apart, source.fresh, fun _ member => by cases member⟩
    · intro check member
      rw [prepared_rule] at member
      change check ∈ (code.checks.map (Check.map (queryView queries locals captures))).map
        (Check.map (instantiate (frame queries locals captures occupied).assignment)) at member
      obtain ⟨mapped, mappedMember, rfl⟩ := List.mem_map.mp member
      have originalExists : ∃ original ∈ code.checks, original.map (queryView queries locals captures) = mapped :=
        List.mem_map.mp mappedMember
      obtain ⟨original, originalMember, rfl⟩ := originalExists
      exact (check_iff queries locals captures occupied selection code rows before original).mpr (source.checks original originalMember)
  · intro native
    refine ⟨native.take_distinct, native.output_distinct, ?_, ?_, ?_, native.occurrences.taken_subset,
      native.occurrences.kept_subset, native.occurrences.apart, native.occurrences.fresh,
      (solvable_iff queries locals captures occupied selection code rows before).mp native.solvable, ?_⟩
    · simpa only [nativeRule, RuleInstance.map, List.length_map] using native.take_length
    · simpa only [nativeRule, RuleInstance.map, List.length_map] using native.read_length
    · have lengths := congrArg List.length native.outputs
      simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare, nativeRule,
        ContextualFreshening.ruleAt, RuleInstance.map, List.length_map] using lengths
    · intro check member
      apply (check_iff queries locals captures occupied selection code rows before check).mp
      apply native.checks
      rw [prepared_rule]
      exact List.mem_map.mpr ⟨check.map (queryView queries locals captures),
        List.mem_map.mpr ⟨check, member, rfl⟩, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseAdmission
