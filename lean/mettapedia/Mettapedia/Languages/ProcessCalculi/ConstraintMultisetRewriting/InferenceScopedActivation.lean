import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferenceValues
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceRequestExecution

/-!
# The actual installed inference activation admits structural scoped payloads

The source rule ID and ordered inputs are passed to the original activation.
Its successful located rule is scope-checked position by position. This local
data conversion retains every source value; it does not check a proof object
or replace source admission with an independent soundness callback.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedActivation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker hiding RuleInstance
open InferenceSchemaActivation (Tm judgment)
open InferenceSchemaKernel (Space Value)
open ScopedInferenceValues (Ready Scoped)

def values? : List Value → Option (List Ready)
  | [] => some []
  | value :: rest => do return (← ScopedInferenceValues.checkScope? value) :: (← values? rest)

theorem values_origin {values : List Value} {ready : List Ready}
    (computed : values? values = some ready) : ready.map Subtype.val = values := by
  induction values generalizing ready with
  | nil => have same : ready = [] := (Option.some.inj computed).symm; subst ready; rfl
  | cons value rest earlier =>
      cases accepted : ScopedInferenceValues.checkScope? value with
      | none => simp [values?, accepted] at computed
      | some head =>
          cases tailResult : values? rest with
          | none => simp [values?, accepted, tailResult] at computed
          | some tail =>
              have same : head :: tail = ready := by simpa [values?, accepted, tailResult] using computed
              subst ready
              rw [List.map_cons, (ScopedInferenceValues.checked_scope accepted).1, earlier tailResult]

theorem values_complete (values : List Value) (supported : ∀ value ∈ values, Scoped value) :
    ∃ ready, values? values = some ready := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons value rest earlier =>
      obtain ⟨tail, accepted⟩ := earlier (fun item member => supported item (List.mem_cons_of_mem _ member))
      let head : Ready := ⟨value, supported value List.mem_cons_self⟩
      refine ⟨head :: tail, ?_⟩
      simp only [values?, ScopedInferenceValues.checkScope?, head, dif_pos (supported value List.mem_cons_self), accepted]
      rfl

def rule? (original : RuleInstance Value) : Option (RuleInstance Ready) :=
  if original.tell.isEmpty && original.checks.isEmpty then do
    let take ← values? original.take
    let read ← values? original.read
    let produce ← values? original.produce
    return ⟨take, read, [], [], produce⟩
  else none

theorem rule_origin {original : RuleInstance Value} {ready : RuleInstance Ready}
    (computed : rule? original = some ready) : ready.map Subtype.val = original ∧ ready.checks = [] := by
  unfold rule? at computed
  split at computed
  · rename_i free
    have emptyTell : original.tell = [] := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp free).1
    have emptyChecks : original.checks = [] := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp free).2
    cases takeResult : values? original.take with
    | none => simp [takeResult] at computed
    | some take =>
        cases readResult : values? original.read with
        | none => simp [takeResult, readResult] at computed
        | some read =>
            cases outputResult : values? original.produce with
            | none => simp [takeResult, readResult, outputResult] at computed
            | some produce =>
                have same : (⟨take, read, [], [], produce⟩ : RuleInstance Ready) = ready := by
                  simpa [takeResult, readResult, outputResult] using computed
                subst ready
                refine ⟨?_, rfl⟩
                have takeEq := values_origin takeResult
                have readEq := values_origin readResult
                have outputEq := values_origin outputResult
                cases original
                simp_all [RuleInstance.map]
  · cases computed

theorem rule_complete (original : RuleInstance Value) (noTell : original.tell = [])
    (noChecks : original.checks = []) (takes : ∀ value ∈ original.take, Scoped value)
    (reads : ∀ value ∈ original.read, Scoped value) (produces : ∀ value ∈ original.produce, Scoped value) :
    ∃ ready, rule? original = some ready := by
  obtain ⟨take, acceptedTake⟩ := values_complete original.take takes
  obtain ⟨read, acceptedRead⟩ := values_complete original.read reads
  obtain ⟨produce, acceptedProduce⟩ := values_complete original.produce produces
  refine ⟨⟨take, read, [], [], produce⟩, ?_⟩
  simp only [rule?, noTell, noChecks, List.isEmpty_nil, Bool.true_and, ite_true,
    acceptedTake, acceptedRead, acceptedProduce]
  rfl

def activate (definition : ValidatedCalculusLanguageDef) (id : RuleId) (arguments : List Pattern) :
    Option (RuleInstance Ready) := do
  let original ← InferenceSchemaActivation.activate definition id arguments
  rule? (InferenceSchemaKernel.locate original)

/-- Exact local source origin and exact data readback of the admitted rule. -/
theorem origin (definition : ValidatedCalculusLanguageDef) (id : RuleId) (arguments : List Pattern)
    {ready : RuleInstance Ready} (computed : activate definition id arguments = some ready) :
    ∃ original, InferenceSchemaActivation.activate definition id arguments = some original ∧
      ready.map Subtype.val = InferenceSchemaKernel.locate original ∧ ready.checks = [] := by
  unfold activate at computed
  cases localResult : InferenceSchemaActivation.activate definition id arguments with
  | none => simp [localResult] at computed
  | some original =>
      have admitted : rule? (InferenceSchemaKernel.locate original) = some ready := by
        simpa [localResult] using computed
      exact ⟨original, rfl, (rule_origin admitted).1, (rule_origin admitted).2⟩

private theorem application_arguments {definition : ValidatedCalculusLanguageDef}
    {instance_ : InferenceChecker.RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (applied : RuleApplication definition instance_ premises conclusion) (source : RuleSchema)
    (lookup : definition.1.lookupRule? instance_.ruleId = some source) :
    argumentsValidAt source.metavariables instance_.arguments = true := by
  cases applied with
  | intro selected selectedLookup arguments _ _ _ =>
      have same : selected = source := Option.some.inj (selectedLookup.symm.trans lookup)
      subst source
      exact arguments

/-- The scope conversion accepts every successful original inference
activation, including parameters admitted under nonempty binding prefixes. -/
theorem complete (definition : ValidatedCalculusLanguageDef) (id : RuleId) (arguments : List Pattern)
    {original : RuleInstance Tm}
    (computed : InferenceSchemaActivation.activate definition id arguments = some original) :
    ∃ ready, activate definition id arguments = some ready := by
  obtain ⟨source, premises, conclusion, lookup, instantiated, same⟩ :=
    InferenceSchemaActivation.origin definition id arguments computed
  have applied : RuleApplication definition ⟨id, arguments⟩ premises conclusion :=
    instantiateRule?_eq_some_iff_application.mp instantiated
  have scopes := InferenceSchemaActivation.application_scopes applied
  obtain ⟨ready, admitted⟩ := rule_complete (InferenceSchemaKernel.locate original)
    (by rw [same]; rfl) (by rw [same]; rfl)
    (by
      intro value member
      simp only [same, InferenceSchemaKernel.locate, LocatedRequest.lift,
        InferenceSchemaActivation.fromResult, List.map_cons, List.map_nil, List.mem_singleton] at member
      subst value
      exact InferenceSchemaActivation.requestFields_supported source.metavariables arguments
        (application_arguments applied source lookup))
    (by
      intro value member
      simp only [same, InferenceSchemaKernel.locate, LocatedRequest.lift,
        InferenceSchemaActivation.fromResult, List.map_map, Function.comp_def] at member
      obtain ⟨premise, present, rfl⟩ := List.mem_map.mp member
      exact InferenceSchemaActivation.judgment_supported premise (scopes.1 premise present))
    (by
      intro value member
      simp only [same, InferenceSchemaKernel.locate, LocatedRequest.lift,
        InferenceSchemaActivation.fromResult, List.map_cons, List.map_nil, List.mem_singleton] at member
      subst value
      exact InferenceSchemaActivation.judgment_supported conclusion scopes.2)
  refine ⟨ready, ?_⟩
  unfold activate
  rw [computed]
  exact admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedActivation
