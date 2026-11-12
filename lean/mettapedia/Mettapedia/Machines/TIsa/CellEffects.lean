import Mettapedia.Machines.TIsa.Cells

/-!
# Finite machine-cell effects in the resource calculus

A recipe's guard sees only its listed input and output words. Mutable cells
are taken and replaced; the other input cells are kept. This finite interface
also covers multi-byte stores and simultaneous control/data updates without
introducing another machine state or transaction semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.CellEffects

open Cells Mettapedia.GSLT.Causality.ResourceInteraction

universe u
variable {Key : Type u} [DecidableEq Key]

omit [DecidableEq Key] in
theorem encode_disjUnion (left right : Finset Key) (apart : Disjoint left right)
    (values : Key → Word) :
    encode (left.disjUnion right apart) values = encode left values + encode right values := by
  exact Multiset.map_add _ _ _

theorem encode_union (left right : Finset Key) (apart : Disjoint left right)
    (values : Key → Word) :
    encode (left ∪ right) values = encode left values + encode right values := by
  have same : left.disjUnion right apart = left ∪ right := by ext key; simp
  rw [← same, encode_disjUnion]

theorem encode_partition (keys written : Finset Key) (included : written ⊆ keys)
    (values : Key → Word) :
    encode keys values = encode written values + encode (keys \ written) values := by
  calc
    encode keys values = encode (written ∪ (keys \ written)) values :=
      congrArg (fun scope => encode scope values) (Finset.union_sdiff_of_subset included).symm
    _ = encode written values + encode (keys \ written) values :=
      encode_union written (keys \ written) Finset.disjoint_sdiff values

def overwrite (written : Finset Key) (before after : Key → Word) : Key → Word :=
  fun key => if key ∈ written then after key else before key

theorem encode_overwrite (keys written : Finset Key) (included : written ⊆ keys)
    (before after : Key → Word) :
    encode keys (overwrite written before after) =
      encode written after + encode (keys \ written) before := by
  rw [encode_partition keys written included]
  have changed : encode written (overwrite written before after) = encode written after := by
    apply encode_congr
    intro key member
    exact if_pos member
  have unchanged : encode (keys \ written) (overwrite written before after) =
      encode (keys \ written) before := by
    apply encode_congr
    intro key member
    exact if_neg (Finset.mem_sdiff.mp member).2
  rw [changed, unchanged]

structure Recipe (Key : Type u) where
  inputs : List Key
  outputs : List Key
  guard : List Word → List Word → Bool

def Recipe.writes (recipe : Recipe Key) : Finset Key := recipe.outputs.toFinset

def Recipe.support (recipe : Recipe Key) : Finset Key :=
  recipe.writes ∪ recipe.inputs.toFinset

def Recipe.reads (recipe : Recipe Key) : Finset Key :=
  recipe.inputs.toFinset \ recipe.writes

structure Invocation (recipe : Recipe Key) where
  before : Key → Word
  after : Key → Word
  guarded : recipe.guard (recipe.inputs.map before) (recipe.outputs.map after) = true

def system : System (Cell Key) where
  Site := Recipe Key
  Instance := Invocation
  consume := fun {recipe} invocation => encode recipe.writes invocation.before
  read := fun {recipe} invocation => encode recipe.reads invocation.before
  produce := fun {recipe} invocation => encode recipe.writes invocation.after

theorem demand_eq (recipe : Recipe Key) (invocation : Invocation recipe) :
    system.consume invocation + system.read invocation = encode recipe.support invocation.before := by
  change encode recipe.writes invocation.before +
    encode (recipe.inputs.toFinset \ recipe.writes) invocation.before = _
  rw [← encode_union _ _ Finset.disjoint_sdiff]
  congr 1
  ext key
  simp [Recipe.support]

theorem enabled_iff (recipe : Recipe Key) (invocation : Invocation recipe)
    (keys : Finset Key) (values : Key → Word) :
    system.Enables (encode keys values) invocation ↔
      recipe.support ⊆ keys ∧ ∀ key ∈ recipe.support, invocation.before key = values key := by
  unfold System.Enables
  rw [demand_eq, encode_le_iff]

theorem enabled_guard (recipe : Recipe Key) (invocation : Invocation recipe)
    (keys : Finset Key) (values : Key → Word)
    (enabled : system.Enables (encode keys values) invocation) :
    recipe.guard (recipe.inputs.map values) (recipe.outputs.map invocation.after) = true := by
  obtain ⟨_, agree⟩ := (enabled_iff recipe invocation keys values).mp enabled
  have same : recipe.inputs.map invocation.before = recipe.inputs.map values := by
    apply List.map_congr_left
    intro key member
    exact agree key (by simp [Recipe.support, member])
  rw [← same]
  exact invocation.guarded

theorem fire_refines_overwrite (recipe : Recipe Key) (invocation : Invocation recipe)
    (keys : Finset Key) (values : Key → Word)
    (enabled : system.Enables (encode keys values) invocation) :
    system.fire (encode keys values) invocation =
      encode keys (overwrite recipe.writes values invocation.after) := by
  obtain ⟨included, agree⟩ := (enabled_iff recipe invocation keys values).mp enabled
  have writesIncluded : recipe.writes ⊆ keys :=
    fun key member => included (Finset.mem_union_left _ member)
  have original : encode recipe.writes invocation.before = encode recipe.writes values := by
    apply encode_congr
    intro key member
    exact agree key (Finset.mem_union_left _ member)
  change encode keys values - encode recipe.writes invocation.before + encode recipe.writes invocation.after = _
  rw [original, encode_partition keys recipe.writes writesIncluded]
  rw [encode_overwrite keys recipe.writes writesIncluded]
  rw [add_tsub_cancel_left]
  exact add_comm _ _

theorem overwrite_outside (recipe : Recipe Key) (before after : Key → Word) (key : Key)
    (untouched : key ∉ recipe.writes) : overwrite recipe.writes before after key = before key :=
  if_neg untouched

theorem effect_realized (recipe : Recipe Key) (keys : Finset Key) (before after : Key → Word)
    (included : recipe.support ⊆ keys)
    (guarded : recipe.guard (recipe.inputs.map before) (recipe.outputs.map after) = true) :
    ∃ invocation : Invocation recipe,
      system.Enables (encode keys before) invocation ∧
      system.fire (encode keys before) invocation = encode keys (overwrite recipe.writes before after) := by
  let invocation : Invocation recipe := ⟨before, after, guarded⟩
  have enabled : system.Enables (encode keys before) invocation :=
    (enabled_iff recipe invocation keys before).mpr ⟨included, fun _ _ => rfl⟩
  exact ⟨invocation, enabled, fire_refines_overwrite recipe invocation keys before enabled⟩

/-- The only successors on canonical cells satisfy the declared finite guard. -/
theorem rewrite_iff (keys : Finset Key) (before : Key → Word) (result : Multiset (Cell Key)) :
    (system (Key := Key)).theory.rewrites (encode keys before) result ↔
      ∃ recipe : Recipe Key, ∃ after : Key → Word,
        recipe.support ⊆ keys ∧
        recipe.guard (recipe.inputs.map before) (recipe.outputs.map after) = true ∧
        result = encode keys (overwrite recipe.writes before after) := by
  constructor
  · rintro ⟨recipe, invocation, enabled, rfl⟩
    exact ⟨recipe, invocation.after, ((enabled_iff recipe invocation keys before).mp enabled).1,
      enabled_guard recipe invocation keys before enabled,
      fire_refines_overwrite recipe invocation keys before enabled⟩
  · rintro ⟨recipe, after, included, guarded, rfl⟩
    obtain ⟨invocation, enabled, same⟩ := effect_realized recipe keys before after included guarded
    exact ⟨recipe, invocation, enabled, same.symm⟩

/-- Specialization selects actual source recipes, not arbitrary new callbacks. -/
def profile (recipes : List (Recipe Key)) : System.{u, u} (Cell Key) where
  Site := ULift.{u} (Fin recipes.length)
  Instance := fun index => Invocation recipes[index.down]
  consume := fun {index} invocation => encode recipes[index.down].writes invocation.before
  read := fun {index} invocation => encode recipes[index.down].reads invocation.before
  produce := fun {index} invocation => encode recipes[index.down].writes invocation.after

/-- Both directions of finite-profile hosting retain the selected source rule. -/
theorem profile_rewrite_iff (recipes : List (Recipe Key)) (keys : Finset Key)
    (before : Key → Word) (result : Multiset (Cell Key)) :
    (profile recipes).theory.rewrites (encode keys before) result ↔
      ∃ recipe ∈ recipes, ∃ after : Key → Word,
        recipe.support ⊆ keys ∧
        recipe.guard (recipe.inputs.map before) (recipe.outputs.map after) = true ∧
        result = encode keys (overwrite recipe.writes before after) := by
  constructor
  · rintro ⟨index, invocation, enabled, rfl⟩
    have baseEnabled : system.Enables (encode keys before) invocation := enabled
    refine ⟨recipes[index.down], List.getElem_mem index.down.isLt, invocation.after,
      ((enabled_iff _ invocation keys before).mp baseEnabled).1,
      enabled_guard _ invocation keys before baseEnabled, ?_⟩
    exact fire_refines_overwrite _ invocation keys before baseEnabled
  · rintro ⟨recipe, member, after, included, guarded, rfl⟩
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    let invocation : Invocation recipes[index] := ⟨before, after, guarded⟩
    have enabled : system.Enables (encode keys before) invocation :=
      (enabled_iff _ invocation keys before).mpr ⟨included, fun _ _ => rfl⟩
    exact ⟨ULift.up index, invocation, enabled, (fire_refines_overwrite _ invocation keys before enabled).symm⟩

end Mettapedia.Machines.TIsa.CellEffects
