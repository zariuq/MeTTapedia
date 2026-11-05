import Mathlib.Data.List.Basic

/-! Successful optional traversal preserves ordered input/output relations
and every projection respected by each individual result.
-/

set_option autoImplicit false

namespace Mettapedia.Data.List

universe u v w

theorem option_mapM_forall₂ {α : Type u} {β : Type v} (emit : α → Option β) (inputs : List α) (outputs : List β)
    (read : inputs.mapM emit = some outputs) :
    List.Forall₂ (fun input output => emit input = some output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil =>
      have same : [] = outputs := by simpa using read
      subst outputs
      exact .nil
  | cons first rest ih =>
      cases firstRead : emit first with
      | none => simp [List.mapM_cons, firstRead] at read
      | some head =>
        cases restRead : rest.mapM emit with
        | none => simp [List.mapM_cons, firstRead, restRead] at read
        | some tail =>
          have same : head :: tail = outputs := by simpa [List.mapM_cons, firstRead, restRead] using read
          subst outputs
          exact .cons firstRead (ih tail restRead)

theorem option_mapM_input {α : Type u} {β : Type v} (emit : α → Option β) (inputs : List α)
    {outputs : List β} (read : inputs.mapM emit = some outputs) (input : α) (member : input ∈ inputs) :
    ∃ output, emit input = some output := by
  have graph := option_mapM_forall₂ emit inputs outputs read
  clear read
  induction graph with
  | nil => cases member
  | @cons first head rest tail computed graph ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨head, computed⟩
      · exact ih later

theorem option_mapM_origin {α : Type u} {β : Type v} (emit : α → Option β) (inputs : List α) (outputs : List β)
    (read : inputs.mapM emit = some outputs) (output : β) (member : output ∈ outputs) :
    ∃ input ∈ inputs, emit input = some output := by
  have graph := option_mapM_forall₂ emit inputs outputs read
  clear read
  induction graph with
  | nil => cases member
  | @cons first head rest tail computed graph ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨first, List.mem_cons_self, computed⟩
      · obtain ⟨input, present, result⟩ := ih later
        exact ⟨input, List.mem_cons_of_mem first present, result⟩

theorem option_mapM_projection {α : Type u} {β : Type v} {γ : Type w}
    (emit : α → Option β) (inputs : List α) (outputs : List β)
    (inputKey : α → γ) (outputKey : β → γ) (read : inputs.mapM emit = some outputs)
    (preserved : ∀ input output, emit input = some output → outputKey output = inputKey input) :
    outputs.map outputKey = inputs.map inputKey := by
  have graph := option_mapM_forall₂ emit inputs outputs read
  clear read
  induction graph with
  | nil => rfl
  | @cons first head rest tail computed graph ih =>
      simp only [List.map_cons, preserved first head computed, ih]

theorem option_mapM_exists {α : Type u} {β : Type v} (emit : α → Option β) (inputs : List α)
    (each : ∀ input ∈ inputs, ∃ output, emit input = some output) :
    ∃ outputs, inputs.mapM emit = some outputs := by
  induction inputs with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨head, computed⟩ := each first List.mem_cons_self
      obtain ⟨tail, remaining⟩ := ih (fun input present => each input (List.mem_cons_of_mem first present))
      exact ⟨head :: tail, by simp [List.mapM_cons, computed, remaining]⟩

#print axioms option_mapM_forall₂
#print axioms option_mapM_input
#print axioms option_mapM_origin
#print axioms option_mapM_projection
#print axioms option_mapM_exists

end Mettapedia.Data.List
