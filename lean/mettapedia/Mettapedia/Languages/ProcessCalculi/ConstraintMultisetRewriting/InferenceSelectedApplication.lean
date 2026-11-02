import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceClassifying

/-!
# Executing a source application with prescribed physical premise reads

This refines the existing request execution construction by retaining the
selected firing witnesses and the supplied ordered read list. No distinctness
condition is imposed on reads. The same physical protected occurrence may
therefore serve several equal-judgment premise ports.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedApplication

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker hiding RuleInstance
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm action judgment)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload system)
open InferenceSelectedFirings

/-- An admitted source application executes using exactly the prescribed
physical reads, with actual installed-schema and activation evidence. -/
theorem application_runs_with_reads (definition : ValidatedCalculusLanguageDef)
    {instance_ : InferenceChecker.RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (applied : RuleApplication definition instance_ premises conclusion)
    (before : Configuration Value Occurrence) (background : locatedAction.Consistent before.equations)
    (reads : List Occurrence) (readPresent : ∀ occurrence ∈ reads, occurrence ∈ before.present)
    (readLabels : reads.map label = premises.map (fun premise => (Space.judgments, judgment premise))) :
    ∃ (middle after : Configuration Value Occurrence)
      (_client : SelectedFiring definition false before middle)
      (server : SelectedFiring definition true middle after),
      server.source = .inl instance_.ruleId ∧ server.inputs = .inl instance_.arguments ∧
      server.picked.read = reads ∧ before.present ⊆ after.present ∧
      ∃ output ∈ after.present, label output = (.judgments, judgment conclusion) := by
  obtain ⟨rule, lookup, activated⟩ := InferenceSchemaActivation.activate_of_application applied
  let requestValue := InferenceSchemaActivation.request instance_.ruleId rule instance_.arguments
  obtain ⟨request, freshRequest, requestLabel⟩ :=
    IndexedOccurrences.supply before.present (Space.requests, requestValue)
  let middle := InferenceRequestExecution.posted before request
  obtain ⟨client⟩ := SelectedFiring.of_step
    (InferenceRequestExecution.client_posts definition before background requestValue request freshRequest requestLabel)
  obtain ⟨output, freshOutput, outputLabel⟩ :=
    IndexedOccurrences.supply middle.present (Space.judgments, judgment conclusion)
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
      · simp [picked, Selection.commit, middle, InferenceRequestExecution.posted]
      · intro occurrence member
        exact Finset.mem_insert_of_mem
          (readPresent occurrence (by simpa [picked, Selection.commit] using member))
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
  let server : SelectedFiring definition true middle (picked.result label located middle) :=
    { source := .inl instance_.ruleId
      installed := by
        refine List.mem_map.mpr ⟨rule, List.mem_of_find?_eq_some lookup, ?_⟩
        have identity : rule.id = instance_.ruleId := by simpa using List.find?_some lookup
        exact congrArg Sum.inl identity
      inputs := .inl instance_.arguments
      rule := located
      computed := by
        change (InferenceSchemaActivation.activate definition instance_.ruleId instance_.arguments).map
          InferenceSchemaKernel.locate = some located
        rw [activated]
        rfl
      picked := picked
      qualified := valid
      formed := by intro occurrence made; rfl
      destination := rfl }
  refine ⟨middle, picked.result label located middle, client, server, rfl, rfl, rfl,
    ?_, output, ?_, outputLabel⟩
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

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedApplication
