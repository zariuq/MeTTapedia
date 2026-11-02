import Mathlib.Data.List.Basic

/-! A successful ordered exception traversal retains an input origin for
every output occurrence. No injectivity or distinctness is required.
-/

set_option autoImplicit false

namespace Mettapedia.Data.List

theorem mapM_success_forall₂ {α β ε : Type} (emit : α → Except ε β) (inputs : List α) (outputs : List β)
    (read : inputs.mapM emit = .ok outputs) : List.Forall₂ (fun input output => emit input = .ok output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil =>
    have same : [] = outputs := by simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] using read
    subst outputs
    exact .nil
  | cons first rest ih =>
    cases firstRead : emit first with
    | error reason => simp only [List.mapM_cons, firstRead, bind, Except.bind] at read; cases read
    | ok head =>
      cases restRead : rest.mapM emit with
      | error reason => simp only [List.mapM_cons, firstRead, restRead, bind, Except.bind] at read; cases read
      | ok tail =>
        have same : head :: tail = outputs := by
          simpa only [List.mapM_cons, firstRead, restRead, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using read
        subst outputs
        exact .cons firstRead (ih tail restRead)

theorem mapM_success_origin {α β ε : Type} (emit : α → Except ε β) (inputs : List α) (outputs : List β)
    (read : inputs.mapM emit = .ok outputs) (output : β) (member : output ∈ outputs) :
    ∃ input ∈ inputs, emit input = .ok output := by
  have graph := mapM_success_forall₂ emit inputs outputs read
  clear read
  induction graph with
  | nil => cases member
  | @cons first head rest tail computed graph ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨first, List.mem_cons_self, computed⟩
    · obtain ⟨input, present, result⟩ := ih later
      exact ⟨input, List.mem_cons_of_mem first present, result⟩

#print axioms mapM_success_forall₂
#print axioms mapM_success_origin

end Mettapedia.Data.List
