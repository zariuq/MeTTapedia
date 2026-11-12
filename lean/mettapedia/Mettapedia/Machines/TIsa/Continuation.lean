import Mettapedia.Machines.TIsa.Control

/-!
# Continuations for arbitrary finite transform effects

Attach one linear control token to an existing cell recipe. Its data guard
and finite read/write footprint remain unchanged. This composes register,
memory and result operations without adding an instruction interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Control

open Cells CellEffects

universe u
variable {Key : Type u} [DecidableEq Key]

structure Edge (Key : Type u) where
  activation : Nat
  point : Word
  next : Word
  effect : Recipe Key

def Edge.recipe (edge : Edge Key) : Recipe (Location Key) where
  inputs := .inl edge.activation :: edge.effect.inputs.map Sum.inr
  outputs := .inl edge.activation :: edge.effect.outputs.map Sum.inr
  guard := fun inputs outputs => match inputs, outputs with
    | point :: arguments, next :: results =>
        point == edge.point && next == edge.next && edge.effect.guard arguments results
    | _, _ => false

omit [DecidableEq Key] in
theorem Edge.guard_iff (edge : Edge Key) (before after : Location Key → Word) :
    edge.recipe.guard (edge.recipe.inputs.map before) (edge.recipe.outputs.map after) = true ↔
      before (.inl edge.activation) = edge.point ∧ after (.inl edge.activation) = edge.next ∧
      edge.effect.guard (edge.effect.inputs.map (fun key => before (.inr key)))
        (edge.effect.outputs.map (fun key => after (.inr key))) = true := by
  simp [recipe, Bool.and_eq_true, and_assoc, List.map_map, Function.comp_def]

def Edge.finish (edge : Edge Key) (before after : Location Key → Word) : Location Key → Word
  | .inl activation => if activation = edge.activation then edge.next else before (.inl activation)
  | .inr key => overwrite edge.effect.writes (fun key => before (.inr key)) (fun key => after (.inr key)) key

theorem Edge.overwrite_eq (edge : Edge Key) (before after : Location Key → Word)
    (next : after (.inl edge.activation) = edge.next) :
    overwrite edge.recipe.writes before after = edge.finish before after := by
  funext location
  cases location with
  | inl activation =>
      by_cases same : activation = edge.activation
      · subst activation
        simp [overwrite, Recipe.writes, recipe, finish, next]
      · simp [overwrite, Recipe.writes, recipe, finish, same]
  | inr key =>
      simp [overwrite, Recipe.writes, recipe, finish]

/-- A control edge and its data operation are one existing resource firing. -/
theorem Edge.realized (edge : Edge Key) (keys : Finset (Location Key))
    (before after : Location Key → Word) (included : edge.recipe.support ⊆ keys)
    (guarded : edge.recipe.guard (edge.recipe.inputs.map before) (edge.recipe.outputs.map after) = true) :
    ∃ invocation : Invocation edge.recipe,
      CellEffects.system.Enables (encode keys before) invocation ∧
      CellEffects.system.fire (encode keys before) invocation = encode keys (edge.finish before after) := by
  obtain ⟨invocation, enabled, endpoint⟩ := effect_realized edge.recipe keys before after included guarded
  exact ⟨invocation, enabled, by rw [endpoint, edge.overwrite_eq before after
    ((edge.guard_iff before after).mp guarded).2.1]⟩

def edgeProgram (edges : List (Edge Key)) := CellEffects.profile (edges.map Edge.recipe)

theorem Edge.finish_of_no_outputs (edge : Edge Key) (empty : edge.effect.outputs = [])
    (before after : Location Key → Word) :
    edge.finish before after = Function.update before (.inl edge.activation) edge.next := by
  funext location
  cases location with
  | inl other =>
      by_cases same : other = edge.activation
      · subst other; simp [Edge.finish]
      · simp [Edge.finish, same]
  | inr data => simp [Edge.finish, overwrite, Recipe.writes, empty]

/-- A failed operation may transfer control without changing any data resource. -/
theorem Edge.readonly_realized (edge : Edge Key) (empty : edge.effect.outputs = [])
    (keys : Finset (Location Key)) (before after : Location Key → Word)
    (included : edge.recipe.support ⊆ keys)
    (guarded : edge.recipe.guard (edge.recipe.inputs.map before) (edge.recipe.outputs.map after) = true) :
    ∃ invocation : Invocation edge.recipe,
      CellEffects.system.Enables (encode keys before) invocation ∧
      CellEffects.system.fire (encode keys before) invocation =
        encode keys (Function.update before (.inl edge.activation) edge.next) := by
  obtain ⟨invocation, enabled, endpoint⟩ := edge.realized keys before after included guarded
  exact ⟨invocation, enabled, by rw [endpoint, edge.finish_of_no_outputs empty]⟩

theorem edgeProgram_rewrite_iff (edges : List (Edge Key)) (keys : Finset (Location Key))
    (before : Location Key → Word) (result : Multiset (Cell (Location Key))) :
    (edgeProgram edges).theory.rewrites (encode keys before) result ↔
      ∃ edge ∈ edges, ∃ after : Location Key → Word,
        edge.recipe.support ⊆ keys ∧ before (.inl edge.activation) = edge.point ∧
        after (.inl edge.activation) = edge.next ∧
        edge.effect.guard (edge.effect.inputs.map (fun key => before (.inr key)))
          (edge.effect.outputs.map (fun key => after (.inr key))) = true ∧
        result = encode keys (edge.finish before after) := by
  rw [edgeProgram, profile_rewrite_iff]
  constructor
  · rintro ⟨recipe, member, after, included, guarded, endpoint⟩
    obtain ⟨edge, source, rfl⟩ := List.mem_map.mp member
    obtain ⟨point, next, guarded⟩ := (edge.guard_iff before after).mp guarded
    exact ⟨edge, source, after, included, point, next, guarded,
      by rw [endpoint, edge.overwrite_eq before after next]⟩
  · rintro ⟨edge, source, after, included, point, next, guarded, rfl⟩
    exact ⟨edge.recipe, List.mem_map.mpr ⟨edge, source, rfl⟩, after, included,
      (edge.guard_iff before after).mpr ⟨point, next, guarded⟩,
      congrArg (encode keys) (edge.overwrite_eq before after next).symm⟩

end Mettapedia.Machines.TIsa.Control
