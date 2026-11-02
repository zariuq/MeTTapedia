import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactRequestExecution

/-!
# Physical execution of one exact consume/read/produce interaction

Several actual data occurrences can be consumed in the same ordinary CMR
selection. Fresh outputs preserve multiplicity. This is the existing atomic
Step with its original selection validity, not a new transaction relation.
Source activation and handle authority remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactInteractionExecution

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {T S : Type*} [DecidableEq T]
abbrev Occurrence := IndexedOccurrences.Occurrence T
abbrev label : Occurrence (T := T) → T := IndexedOccurrences.label

def rule (taken premises outputs : List T) : RuleInstance T := ⟨taken, premises, [], [], outputs⟩

theorem selection (action : SubstitutionAction T S) (takenValues premises outputs : List T)
    (before : Configuration T (Occurrence (T := T))) (background : action.Consistent before.equations)
    (taken : List (Occurrence (T := T))) (distinctTaken : taken.Nodup)
    (takePresent : ∀ occurrence ∈ taken, occurrence ∈ before.present)
    (takeLabels : taken.map label = takenValues)
    (available : ∀ value ∈ premises, ∃ occurrence ∈ before.present, label occurrence = value)
    (separate : ∀ occurrence ∈ before.present, label occurrence ∈ premises → occurrence ∉ taken) :
    ∃ picked : Selection (Occurrence (T := T)), picked.taken = taken ∧
      picked.Valid action label (rule takenValues premises outputs) before := by
  obtain ⟨reads, readPresent, readLabels⟩ := GuardedMultisetRewriting.exists_list_of_mem label before.present premises available
  obtain ⟨made, distinct, fresh, madeLabels⟩ := ExactRequestExecution.fresh_outputs before.present outputs
  let picked : Selection (Occurrence (T := T)) := ⟨taken, reads, made⟩
  refine ⟨picked, rfl, distinctTaken, distinct, ?_, ?_, madeLabels, ?_, ?_, ?_⟩
  · simpa [rule, picked] using (congrArg List.length takeLabels).symm
  · simpa [rule, picked] using (congrArg List.length readLabels).symm
  · refine ⟨?_, ?_, ?_, ?_, by simp [picked, Selection.commit]⟩
    · intro occurrence member
      exact takePresent occurrence (by simpa [picked, Selection.commit] using member)
    · intro occurrence member
      exact readPresent occurrence (by simpa [picked, Selection.commit] using member)
    · apply Finset.disjoint_left.mpr
      intro occurrence removed kept
      have selected : occurrence ∈ reads := by simpa [picked, Selection.commit] using kept
      have valuePresent : label occurrence ∈ premises := by
        rw [← readLabels]
        exact List.mem_map.mpr ⟨occurrence, selected, rfl⟩
      exact separate occurrence (readPresent occurrence selected) valuePresent (by simpa [picked, Selection.commit] using removed)
    · apply Finset.disjoint_left.mpr
      intro occurrence created old
      exact fresh occurrence (by simpa [picked, Selection.commit] using created) old
  · obtain ⟨assignment, solved⟩ := background
    refine ⟨assignment, ?_⟩
    change action.Models assignment (before.equations ++ Selection.equations label takenValues taken ++
      Selection.equations label premises reads ++ [])
    rw [← takeLabels, ← readLabels]
    simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true]
    exact ⟨⟨solved, RequestActivation.self_equations action assignment label taken⟩,
      RequestActivation.self_equations action assignment label reads⟩
  · intro check member
    cases member

/-- When the selected interpretation is rigid equality, its actual input
equations recover exact ordered labels. This applies to ground clients;
it does not replace two-way solving in a nonrigid term layer. -/
theorem rigid_input_labels (action : SubstitutionAction T S)
    (rigid : ∀ assignment left right, action.E (action.apply assignment left)
      (action.apply assignment right) ↔ left = right)
    {picked : Selection (Occurrence (T := T))} {source : RuleInstance T}
    {before : Configuration T (Occurrence (T := T))}
    (valid : picked.Valid action label source before) :
    picked.taken.map label = source.take ∧ picked.read.map label = source.read := by
  obtain ⟨assignment,solved⟩ := valid.consistent
  have inputs := Selection.models_problem action valid solved
  have recover {patterns : List T} {selected : List (Occurrence (T := T))}
      (matched : List.Forall₂ (fun value occurrence =>
        action.E (action.apply assignment value) (action.apply assignment (label occurrence))) patterns selected) :
      selected.map label = patterns := by
    have equal := matched.imp (fun value occurrence same => (rigid assignment value (label occurrence)).mp same)
    have rows : List.Forall₂ Eq patterns (selected.map label) := by
      simpa only [List.forall₂_map_right_iff] using equal
    have same : patterns = selected.map label := by simpa only [List.forall₂_eq_eq_eq] using rows
    exact same.symm
  exact ⟨recover inputs.2.1,recover inputs.2.2.1⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactInteractionExecution
