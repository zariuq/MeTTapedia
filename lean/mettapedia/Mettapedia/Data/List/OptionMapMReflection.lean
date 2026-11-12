import Mettapedia.Data.List.OptionMapM

/-! Reflection of successful optional traversals from ordered relations. -/

set_option autoImplicit false

namespace Mettapedia.Data.List

universe u v

theorem option_mapM_of_forall₂ {α : Type u} {β : Type v} (emit : α → Option β)
    {inputs : List α} {outputs : List β}
    (graph : List.Forall₂ (fun input output => emit input = some output) inputs outputs) :
    inputs.mapM emit = some outputs := by
  induction graph with
  | nil => rfl
  | cons head tail ih => simp [List.mapM_cons,head,ih]

theorem option_mapM_iff_forall₂ {α : Type u} {β : Type v} (emit : α → Option β)
    (inputs : List α) (outputs : List β) :
    inputs.mapM emit = some outputs ↔ List.Forall₂ (fun input output => emit input = some output) inputs outputs :=
  ⟨option_mapM_forall₂ emit inputs outputs,option_mapM_of_forall₂ emit⟩

theorem option_mapM_relation {α : Type u} {β : Type v} (emit : α → Option β)
    (relation : α → β → Prop)
    (each : ∀ input output, emit input = some output ↔ relation input output)
    (inputs : List α) (outputs : List β) :
    inputs.mapM emit = some outputs ↔ List.Forall₂ relation inputs outputs := by
  rw [option_mapM_iff_forall₂]
  constructor
  · intro graph
    induction graph with
    | nil => exact .nil
    | cons head tail ih => exact .cons ((each _ _).mp head) ih
  · intro graph
    induction graph with
    | nil => exact .nil
    | cons head tail ih => exact .cons ((each _ _).mpr head) ih

end Mettapedia.Data.List
