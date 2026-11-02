import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaKernel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestActivation

/-!
# Ordinary clients post data and the same kernel executes an inference request

The client can publish arbitrary request data, including malformed or
proof-shaped data, only in request space. A successful source application is
realized by an ordinary client-post step followed by the existing kernel's
ordinary consume/read/produce step. Earlier occurrences are retained and
multiple premise positions may read the same physical occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceRequestExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker hiding RuleInstance
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm action judgment)
open InferenceSchemaKernel (Space Value locatedAction)

abbrev Occurrence := IndexedOccurrences.Occurrence Value
abbrev label : Occurrence → Value := IndexedOccurrences.label
def location (occurrence : Occurrence) : Space := (label occurrence).1
def payload (occurrence : Occurrence) : Tm := (label occurrence).2

def postRule (value : Tm) : RuleInstance Value := ⟨[], [], [], [], [(.requests, value)]⟩

def system (definition : ValidatedCalculusLanguageDef) :
    InferenceSchemaKernel.System definition Unit Tm Bool Occurrence location where
  clientActivation := fun _ value => some (postRule value)
  authority :=
    { process := fun actor => if actor then
        ⟨fun _ _ => true, definition.1.rules.map (fun rule => .inl rule.id)⟩
      else ⟨fun space _ => space == .requests, [.inr ()]⟩
      kernel := true
      soleWriter := by
        intro actor notKernel occurrence protectedHere
        cases actor with
        | true => exact False.elim (notKernel rfl)
        | false =>
            change (location occurrence == Space.requests) = false
            rw [show location occurrence = Space.judgments from protectedHere]
            rfl }
  kernelSchemas := rfl

def posted (before : Configuration Value Occurrence) (request : Occurrence) : Configuration Value Occurrence :=
  ⟨before.equations, insert request before.present⟩

theorem client_posts (definition : ValidatedCalculusLanguageDef) (before : Configuration Value Occurrence)
    (background : locatedAction.Consistent before.equations) (value : Tm) (request : Occurrence)
    (fresh : request ∉ before.present) (readback : label request = (.requests, value)) :
    (system definition).Step payload false before (posted before request) := by
  let picked : Selection Occurrence := ⟨[], [], [request]⟩
  refine ⟨.inr (), by simp [system], .inr value, postRule value, rfl, picked, ?_, ?_, ?_⟩
  · refine ⟨by simp [picked], by simp [picked], rfl, rfl, ?_, ?_, ?_, ?_⟩
    · change [(location request, payload request)] = [(Space.requests, value)]
      exact congrArg List.singleton readback
    · refine ⟨by simp [picked, Selection.commit], by simp [picked, Selection.commit],
        by simp [picked, Selection.commit], ?_, by simp [picked, Selection.commit]⟩
      simpa [picked, Selection.commit, Finset.disjoint_left] using fresh
    · simpa [picked, postRule, Selection.problem, Selection.equations] using background
    · intro check member
      cases member
  · intro occurrence made
    have same : occurrence = request := by simpa [picked] using made
    subst occurrence
    change (location request == Space.requests) = true
    exact beq_iff_eq.mpr (congrArg Prod.fst readback)
  · apply congrArg₂ Configuration.mk
    · simp [picked, Selection.problem, Selection.equations, postRule]
    · ext occurrence
      simp [picked, Selection.commit, fire]

theorem application_runs (definition : ValidatedCalculusLanguageDef)
    {instance_ : InferenceChecker.RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (applied : RuleApplication definition instance_ premises conclusion)
    (before : Configuration Value Occurrence) (background : locatedAction.Consistent before.equations)
    (available : ∀ premise ∈ premises, ∃ occurrence ∈ before.present, label occurrence = (.judgments, judgment premise)) :
    ∃ (after : Configuration Value Occurrence),
      (system definition).Run payload before [false, true] after ∧
      before.present ⊆ after.present ∧
      ∃ occurrence ∈ after.present, label occurrence = (.judgments, judgment conclusion) := by
  obtain ⟨rule, lookup, activated⟩ := InferenceSchemaActivation.activate_of_application applied
  let requestValue := InferenceSchemaActivation.request instance_.ruleId rule instance_.arguments
  obtain ⟨request, freshRequest, requestLabel⟩ := IndexedOccurrences.supply before.present (Space.requests, requestValue)
  let middle := posted before request
  have postedStep := client_posts definition before background requestValue request freshRequest requestLabel
  obtain ⟨reads, readPresent, readLabels⟩ := GuardedMultisetRewriting.exists_list_of_mem label before.present
    (premises.map (fun premise => (Space.judgments, judgment premise))) (by
      intro value member
      obtain ⟨premise, present, rfl⟩ := List.mem_map.mp member
      exact available premise present)
  obtain ⟨output, freshOutput, outputLabel⟩ := IndexedOccurrences.supply middle.present (Space.judgments, judgment conclusion)
  let raw := InferenceSchemaActivation.fromResult instance_.ruleId rule instance_.arguments premises conclusion
  let located := InferenceSchemaKernel.locate raw
  let picked : Selection Occurrence := ⟨[request], reads, [output]⟩
  have valid : picked.Valid locatedAction label located middle := by
    refine ⟨by simp [picked], by simp [picked], rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [located, InferenceSchemaKernel.locate, LocatedRequest.lift, raw,
        InferenceSchemaActivation.fromResult, picked] using (congrArg List.length readLabels).symm
    · simpa [located, InferenceSchemaKernel.locate, LocatedRequest.lift, raw,
        InferenceSchemaActivation.fromResult, picked] using outputLabel
    · refine ⟨?_, ?_, ?_, ?_, by simp [picked, Selection.commit]⟩
      · simp [picked, Selection.commit, middle, posted]
      · intro occurrence member
        exact Finset.mem_insert_of_mem (readPresent occurrence (by simpa [picked, Selection.commit] using member))
      · apply Finset.disjoint_left.mpr
        intro occurrence taken read
        have same : occurrence = request := by simpa [picked, Selection.commit] using taken
        subst occurrence
        exact freshRequest (readPresent request (by simpa [picked, Selection.commit] using read))
      · simpa [picked, Selection.commit, Finset.disjoint_left] using freshOutput
    · obtain ⟨assignment, solved⟩ := background
      refine ⟨assignment, ?_⟩
      change locatedAction.Models assignment (before.equations ++
        Selection.equations label [(Space.requests, requestValue)] [request] ++
        Selection.equations label ((premises.map judgment).map (fun value => (Space.judgments, value))) reads ++ [])
      simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true]
      have takeSolved : locatedAction.Models assignment
          (Selection.equations label [(Space.requests, requestValue)] [request]) := by
        rw [← requestLabel]
        exact RequestActivation.self_equations locatedAction assignment label [request]
      simp only [List.map_map, Function.comp_def]
      rw [← readLabels]
      exact ⟨⟨solved, takeSolved⟩, RequestActivation.self_equations locatedAction assignment label reads⟩
    · intro check member
      cases member
  have serverStep : (system definition).Step payload true middle (picked.result label located middle) := by
    refine ⟨.inl instance_.ruleId, ?_, .inl instance_.arguments, located, ?_, picked, valid, ?_, rfl⟩
    · refine List.mem_map.mpr ⟨rule, List.mem_of_find?_eq_some lookup, ?_⟩
      have identity : rule.id = instance_.ruleId := by simpa using List.find?_some lookup
      exact congrArg Sum.inl identity
    · change (InferenceSchemaActivation.activate definition instance_.ruleId instance_.arguments).map
        InferenceSchemaKernel.locate = some located
      rw [activated]
      rfl
    · intro occurrence made
      rfl
  refine ⟨picked.result label located middle, .cons postedStep (.cons serverStep (.nil _)), ?_, output, ?_, outputLabel⟩
  · intro occurrence present
    apply mem_fire.mpr
    left
    refine ⟨Finset.mem_insert_of_mem present, ?_⟩
    intro taken
    have same : occurrence = request := by simpa [picked, Selection.commit] using taken
    exact freshRequest (same ▸ present)
  · apply mem_fire.mpr
    right
    simp [picked, Selection.commit]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceRequestExecution
