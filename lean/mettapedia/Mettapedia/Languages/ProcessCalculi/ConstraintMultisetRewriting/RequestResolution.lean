import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestActivation

/-!
# Resolving an activated request firing back to its source recipe

Successful source template instances remain fixed in the declared ambient
interface. At any actual solution of the retained equation store, the same
physical selections give a matching receipt for the source recipe. Its data
condition is recovered from the activated equality check, rather than trusted
from a supplied true code.

The finite input-binding contract remains explicit. This is a resolved
observation theorem; it does not identify an unbound raw store with its
resolved observation or certify publication of a derived schema.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestResolution

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open RequestActivation

variable {V Head P : Type}

private theorem collect_iff {A B : Type} (function : A → Option B) (inputs : List A) (outputs : List B) :
    inputs.mapM function = some outputs ↔ List.Forall₂ (fun input output => function input = some output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases outputs <;> simp
  | cons input inputs earlier =>
      cases outputs with
      | nil =>
          cases head : function input <;> cases tail : inputs.mapM function <;>
            simp [List.mapM_cons, head, tail]
      | cons output outputs =>
          cases head : function input <;> cases tail : inputs.mapM function <;>
            simp [List.mapM_cons, head, tail, ← earlier]

theorem instTemplate_iff (layer : TermLayer V (Term Head) P) (assignment : Subst V (Term Head))
    (patterns : List P) (values : List (Term Head)) :
    instTemplate layer assignment patterns = some values ↔
      List.Forall₂ (fun pattern value => layer.inst assignment pattern = some value) patterns values :=
  collect_iff (layer.inst assignment) patterns values

theorem source_matches {O : Type*} (layer : TermLayer V (Term Head) P) (structural : layer.E = Eq)
    (width : Nat) (assignment : Subst V (Term Head)) (candidate : ABTProtectedParameters.Assignment Head width)
    (label : O → Term Head) {patterns : List P} {values : List (Term Head)}
    (instances : List.Forall₂ (fun pattern value => layer.inst assignment pattern = some value) patterns values) :
    ∀ {picked : List O},
      List.Forall₂ (fun value occurrence => (ABTProtectedParameters.action width).E
        ((ABTProtectedParameters.action width).apply candidate value)
        ((ABTProtectedParameters.action width).apply candidate (label occurrence))) values picked →
      (∀ value ∈ values, FixedMatching.Fixed (ABTProtectedParameters.action width) value) →
      List.Forall₂ (layer.Solves assignment) patterns
        (picked.map fun occurrence => (ABTProtectedParameters.action width).apply candidate (label occurrence)) := by
  induction instances with
  | nil =>
      intro picked matched _
      cases matched
      exact .nil
  | @cons pattern value patterns values instantiated rest earlier =>
      intro picked matched fixed
      cases matched with
      | cons equal tail =>
          refine .cons ⟨value, instantiated, ?_⟩ (earlier tail
            (fun body member => fixed body (List.mem_cons_of_mem _ member)))
          rw [structural]
          change (ABTProtectedParameters.action width).apply candidate value =
            _ at equal
          rw [fixed value List.mem_cons_self candidate] at equal
          exact equal

noncomputable def resolvedReceipt {O : Type*} (layer : TermLayer V (Term Head) P)
    (recipe : Recipe V Head P) (assignment : Subst V (Term Head)) (width : Nat)
    (candidate : ABTProtectedParameters.Assignment Head width) (label : O → Term Head)
    (world : Finset O) (picked : Selection O) : GuardedMultisetRewriting.FiringReceipt O V (Term Head) :=
  ⟨assignment, picked.taken, picked.read, picked.made,
    [regionOf (fun occurrence => (ABTProtectedParameters.action width).apply candidate (label occurrence))
      world (semRegion layer assignment recipe.request)]⟩

theorem receipt_of_valid {O : Type*} [DecidableEq O]
    (layer : TermLayer V (Term Head) P) (structural : layer.E = Eq)
    (falseHead trueHead : Head) (distinct : falseHead ≠ trueHead) (width : Nat)
    (recipe : Recipe V Head P) (assignment : Subst V (Term Head))
    {rule : RuleInstance (Term Head)} {label : O → Term Head} {before : Configuration (Term Head) O}
    {picked : Selection O}
    (computed : activate layer falseHead trueHead recipe assignment = some rule)
    (bindings : GuardedMultisetRewriting.BindsOnlyGathers layer recipe.matchingRule assignment)
    (templatesFixed : ∀ pattern ∈ recipe.request :: recipe.premises ++ [recipe.conclusion],
      ∀ value, layer.inst assignment pattern = some value → FixedMatching.Fixed (ABTProtectedParameters.action width) value)
    (valid : picked.Valid (ABTProtectedParameters.action width) label rule before)
    (candidate : ABTProtectedParameters.Assignment Head width)
    (models : (ABTProtectedParameters.action width).Models candidate (picked.problem label rule before)) :
    (resolvedReceipt layer recipe assignment width candidate label before.present picked).ValidAt
      layer recipe.matchingRule
      (fun occurrence => (ABTProtectedParameters.action width).apply candidate (label occurrence)) before.present := by
  have checked := condition_of_valid layer falseHead trueHead distinct width recipe assignment computed valid
  obtain ⟨request, premises, conclusion, requestInstance, premiseInstances, conclusionInstance, rfl⟩ :=
    (activate_iff layer falseHead trueHead recipe assignment rule).mp computed
  obtain ⟨_, takes, reads, _⟩ := Selection.models_problem (ABTProtectedParameters.action width) valid models
  have requestFixed := templatesFixed recipe.request (by simp) request requestInstance
  have conclusionFixed := templatesFixed recipe.conclusion (by simp) conclusion conclusionInstance
  have readFixed : ∀ value ∈ premises, FixedMatching.Fixed (ABTProtectedParameters.action width) value := by
    intro value member
    have instances := (instTemplate_iff layer assignment recipe.premises premises).mp premiseInstances
    obtain ⟨pattern, present, instantiated⟩ := GuardedMultisetRewriting.mem_of_forall₂ instances value member
    exact templatesFixed pattern (by simp [present]) value instantiated
  refine ⟨valid.take_distinct, valid.output_distinct,
    valid.occurrences.taken_subset, valid.occurrences.kept_subset,
    valid.occurrences.apart, valid.occurrences.fresh, bindings,
    ?_, ?_, ?_, ?_⟩
  · exact source_matches layer structural width assignment candidate label
      (.cons requestInstance .nil) takes (by
        intro value member
        have same := List.mem_singleton.mp member
        subst value
        exact requestFixed)
  · exact source_matches layer structural width assignment candidate label
      ((instTemplate_iff layer assignment recipe.premises premises).mp premiseInstances) reads readFixed
  · have rawOutputs : picked.made.map label = [conclusion] := valid.outputs
    have mapped := congrArg (List.map ((ABTProtectedParameters.action width).apply candidate)) rawOutputs
    have outputs : picked.made.map (fun occurrence => (ABTProtectedParameters.action width).apply candidate (label occurrence)) =
        [conclusion] := by
      simpa only [List.map_map, List.map_cons, List.map_nil, conclusionFixed candidate, Function.comp_def] using mapped
    change instTemplate layer assignment [recipe.conclusion] =
      some (picked.made.map fun occurrence => (ABTProtectedParameters.action width).apply candidate (label occurrence))
    rw [outputs]
    simp [instTemplate, conclusionInstance]
  · exact .cons ⟨rfl, checked⟩ .nil

theorem resolved_step_of_valid {O : Type*} [DecidableEq O] [DecidableEq Head]
    (layer : TermLayer V (Term Head) P) (structural : layer.E = Eq)
    (falseHead trueHead : Head) (distinct : falseHead ≠ trueHead) (width : Nat)
    (recipe : Recipe V Head P) (assignment : Subst V (Term Head))
    {rule : RuleInstance (Term Head)} {label : O → Term Head} {before : Configuration (Term Head) O}
    {picked : Selection O}
    (computed : activate layer falseHead trueHead recipe assignment = some rule)
    (bindings : GuardedMultisetRewriting.BindsOnlyGathers layer recipe.matchingRule assignment)
    (templatesFixed : ∀ pattern ∈ recipe.request :: recipe.premises ++ [recipe.conclusion],
      ∀ value, layer.inst assignment pattern = some value → FixedMatching.Fixed (ABTProtectedParameters.action width) value)
    (valid : picked.Valid (ABTProtectedParameters.action width) label rule before)
    (candidate : ABTProtectedParameters.Assignment Head width)
    (models : (ABTProtectedParameters.action width).Models candidate (picked.problem label rule before)) :
    GuardedMultisetRewriting.Step layer recipe.matchingRule
      (labels (fun occurrence => (ABTProtectedParameters.action width).apply candidate (label occurrence)) before.present)
      (labels (fun occurrence => (ABTProtectedParameters.action width).apply candidate (label occurrence))
        (picked.result label rule before).present) := by
  have observed := (receipt_of_valid layer structural falseHead trueHead distinct width recipe assignment computed
    bindings templatesFixed valid candidate models).step
  simpa only [resolvedReceipt, GuardedMultisetRewriting.FiringReceipt.commit,
    Selection.result, Selection.commit, fire] using observed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestResolution
