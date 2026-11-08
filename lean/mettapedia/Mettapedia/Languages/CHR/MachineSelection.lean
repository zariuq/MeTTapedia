import Mettapedia.Languages.CHR.MachineStore

/-! Operational selections and the machine's search. A selection of the
operational semantics over a coherent machine store, with the active
constraint at its head position, is reached by the search that `scan`
starts for that occurrence, with the same picks and under an environment the
selection's environment extends. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {inputs : List α} {outputs : List β}, inputs.mapM f = some outputs → outputs.length = inputs.length
  | [], outputs, mapped => by simp at mapped; simp [← mapped]
  | first :: rest, outputs, mapped => by
    rw [List.mapM_cons] at mapped
    cases head : f first with
    | none => simp [head] at mapped
    | some value =>
      cases tail : rest.mapM f with
      | none => simp [head, tail] at mapped
      | some values =>
        simp only [head, tail, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at mapped
        subst mapped
        simp [mapM_length tail]

section Bridge

variable (store : Store) (position active : Nat) (values : List Value)

theorem allFit_intro (environment : Environment) :
    ∀ (index : Nat) (heads : List Head) (occurrences : List Occurrence),
      List.Forall₂ (fun head occurrence => head.instantiate environment = some occurrence.constraint)
        heads occurrences →
      (∀ occurrence ∈ occurrences, occurrence ∈ contents store) →
      (∀ (offset : Nat) (occurrence : Occurrence), occurrences[offset]? = some occurrence →
        (index + offset = position ↔ occurrence.id = active)) →
      (∀ occurrence ∈ occurrences, occurrence.id = active → occurrence.constraint.arguments = values) →
      Coherent store →
      AllFit store position active values index heads occurrences
  | _, [], [], _, _, _, _, _ => trivial
  | index, head :: heads, occurrence :: occurrences, instantiated, stored, located, activeValues, coherent => by
    obtain ⟨first, rest⟩ := List.forall₂_cons.mp instantiated
    refine ⟨?_, allFit_intro environment (index + 1) heads occurrences rest
      (fun later member => stored later (List.mem_cons_of_mem _ member))
      (fun offset later found => by
        have shifted := located (offset + 1) later (by simpa using found)
        rw [show index + (offset + 1) = index + 1 + offset by omega] at shifted
        exact shifted)
      (fun later member => activeValues later (List.mem_cons_of_mem _ member)) coherent⟩
    have here := located 0 occurrence rfl
    rw [Nat.add_zero] at here
    unfold Fits
    obtain ⟨sameName, arguments⟩ := head_instantiate_some first
    by_cases isPosition : index = position
    · simp only [isPosition, if_true]
      have isActive := here.mp isPosition
      exact ⟨isActive, activeValues occurrence (by simp) isActive⟩
    · simp only [isPosition, if_false]
      refine ⟨?_, fun isActive => isPosition (here.mpr isActive)⟩
      have inSlot := slot_of_contents coherent (stored occurrence (by simp))
      have length : head.arguments.length = occurrence.constraint.arguments.length := by
        rw [instantiateTerms_eq] at arguments
        exact (mapM_length arguments).symm
      simpa [Head.key, sameName, length] using inSlot

end Bridge

#print axioms allFit_intro

end Mettapedia.Languages.CHR.Machine
