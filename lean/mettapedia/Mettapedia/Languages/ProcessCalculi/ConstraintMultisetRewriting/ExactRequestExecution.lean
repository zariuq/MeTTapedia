import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestActivation

/-!
# Physical execution of an exact locally computed request result

An existing request occurrence and its actual ordered premise values determine
a valid ordinary consume/read/produce selection. Fresh output occurrences
preserve duplicates; the construction does not classify data as proof or grant
publication authority. Its caller must still provide the installed activation
and output permissions of the actual authority system.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactRequestExecution

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {T S : Type*} [DecidableEq T]
abbrev Occurrence := IndexedOccurrences.Occurrence T
abbrev label : Occurrence (T := T) → T := IndexedOccurrences.label

theorem fresh_outputs (world : Finset (Occurrence (T := T))) (values : List T) :
    ∃ outputs : List (Occurrence (T := T)), outputs.Nodup ∧
      (∀ occurrence ∈ outputs, occurrence ∉ world) ∧ outputs.map label = values := by
  induction values generalizing world with
  | nil => exact ⟨[], by simp, by simp, rfl⟩
  | cons first rest ih =>
      obtain ⟨occurrence, fresh, readback⟩ := IndexedOccurrences.supply world first
      obtain ⟨others, distinct, freshOthers, labels⟩ := ih (insert occurrence world)
      refine ⟨occurrence :: others, List.nodup_cons.mpr ⟨?_, distinct⟩, ?_, ?_⟩
      · intro member
        exact freshOthers occurrence member (Finset.mem_insert_self ..)
      · intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact fresh
        · intro present
          exact freshOthers item member (Finset.mem_insert_of_mem present)
      · simp [readback, labels]

def rule (request : T) (premises outputs : List T) : RuleInstance T :=
  ⟨[request], premises, [], [], outputs⟩

theorem selection (action : SubstitutionAction T S) (requestValue : T) (premises outputs : List T)
    (before : Configuration T (Occurrence (T := T)))
    (background : action.Consistent before.equations)
    (request : Occurrence (T := T)) (present : request ∈ before.present) (readback : label request = requestValue)
    (available : ∀ value ∈ premises, ∃ occurrence ∈ before.present, label occurrence = value)
    (separate : ∀ occurrence ∈ before.present, label occurrence ∈ premises → occurrence ≠ request) :
    ∃ picked : Selection (Occurrence (T := T)),
      picked.taken = [request] ∧ picked.Valid action label (rule requestValue premises outputs) before := by
  obtain ⟨reads, readPresent, readLabels⟩ := GuardedMultisetRewriting.exists_list_of_mem label before.present premises available
  obtain ⟨made, distinct, fresh, madeLabels⟩ := fresh_outputs before.present outputs
  let picked : Selection (Occurrence (T := T)) := ⟨[request], reads, made⟩
  refine ⟨picked, rfl, by simp [picked], distinct, rfl, ?_, madeLabels, ?_, ?_, ?_⟩
  · simpa [rule, picked] using (congrArg List.length readLabels).symm
  · refine ⟨?_, ?_, ?_, ?_, by simp [picked, Selection.commit]⟩
    · simpa [picked, Selection.commit] using present
    · intro occurrence member
      exact readPresent occurrence (by simpa [picked, Selection.commit] using member)
    · apply Finset.disjoint_left.mpr
      intro occurrence taken kept
      have same : occurrence = request := by simpa [picked, Selection.commit] using taken
      have selected : occurrence ∈ reads := by simpa [picked, Selection.commit] using kept
      have valuePresent : label occurrence ∈ premises := by
        rw [← readLabels]
        exact List.mem_map.mpr ⟨occurrence, selected, rfl⟩
      exact separate occurrence (readPresent occurrence selected) valuePresent same
    · apply Finset.disjoint_left.mpr
      intro occurrence created old
      exact fresh occurrence (by simpa [picked, Selection.commit] using created) old
  · obtain ⟨assignment, solved⟩ := background
    refine ⟨assignment, ?_⟩
    change action.Models assignment (before.equations ++ Selection.equations label [requestValue] [request] ++
      Selection.equations label premises reads ++ [])
    rw [← readback, ← readLabels]
    simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true]
    exact ⟨⟨solved, RequestActivation.self_equations action assignment label [request]⟩,
      RequestActivation.self_equations action assignment label reads⟩
  · intro check member
    cases member

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactRequestExecution
