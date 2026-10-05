import Mathlib.Data.List.Basic

/-!
# Ordered dependency identities

An existing dependency keeps its position. Newly encountered identities append
in encounter order, once each. This is identity deduplication, not occurrence
deduplication: the entries owned by a dependency may still contain duplicates.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyIds

universe u
variable {Id : Type u} [DecidableEq Id]

def insertDep (deps : List Id) (source : Id) : List Id :=
  if source ∈ deps then deps else deps ++ [source]

def insertDeps (deps sources : List Id) : List Id :=
  sources.foldl insertDep deps

theorem insertDep_of_mem {deps : List Id} {source : Id}
    (present : source ∈ deps) : insertDep deps source = deps := if_pos present

theorem insertDep_of_not_mem {deps : List Id} {source : Id}
    (absent : source ∉ deps) : insertDep deps source = deps ++ [source] := if_neg absent

theorem mem_insertDep {deps : List Id} {source member : Id} :
    member ∈ insertDep deps source ↔ member ∈ deps ∨ member = source := by
  by_cases present : source ∈ deps
  · rw [insertDep_of_mem present]
    exact ⟨Or.inl, fun included => included.elim id fun same => same ▸ present⟩
  · rw [insertDep_of_not_mem present, List.mem_append, List.mem_singleton]

theorem prefix_insertDep (deps : List Id) (source : Id) : deps <+: insertDep deps source := by
  by_cases present : source ∈ deps
  · rw [insertDep_of_mem present]
    exact List.prefix_refl _
  · rw [insertDep_of_not_mem present]
    exact List.prefix_append deps [source]

theorem nodup_insertDep {deps : List Id} (source : Id) (distinct : deps.Nodup) :
    (insertDep deps source).Nodup := by
  by_cases present : source ∈ deps
  · rwa [insertDep_of_mem present]
  · rw [insertDep_of_not_mem present, List.nodup_append]
    refine ⟨distinct, by simp, ?_⟩
    rintro member included other singleton rfl
    exact present (List.mem_singleton.mp singleton ▸ included)

@[simp] theorem insertDeps_nil (deps : List Id) : insertDeps deps [] = deps := rfl

@[simp] theorem insertDeps_cons (deps : List Id) (source : Id) (sources : List Id) :
    insertDeps deps (source :: sources) = insertDeps (insertDep deps source) sources := rfl

theorem mem_insertDeps {deps sources : List Id} {member : Id} :
    member ∈ insertDeps deps sources ↔ member ∈ deps ∨ member ∈ sources := by
  induction sources generalizing deps with
  | nil => simp
  | cons source sources ih =>
      rw [insertDeps_cons, ih, mem_insertDep, List.mem_cons, or_assoc]

theorem prefix_insertDeps (deps sources : List Id) : deps <+: insertDeps deps sources := by
  induction sources generalizing deps with
  | nil => exact List.prefix_refl deps
  | cons source sources ih => exact (prefix_insertDep deps source).trans (ih _)

theorem nodup_insertDeps {deps : List Id} (sources : List Id) (distinct : deps.Nodup) :
    (insertDeps deps sources).Nodup := by
  induction sources generalizing deps with
  | nil => exact distinct
  | cons source sources ih => exact ih (nodup_insertDep source distinct)

theorem insertDeps_of_forall_mem {deps sources : List Id}
    (present : ∀ source ∈ sources, source ∈ deps) : insertDeps deps sources = deps := by
  induction sources with
  | nil => rfl
  | cons source sources ih =>
      rw [insertDeps_cons, insertDep_of_mem (present source List.mem_cons_self)]
      exact ih fun member included => present member (List.mem_cons_of_mem source included)

theorem insertDeps_insertDeps_self (deps sources : List Id) :
    insertDeps (insertDeps deps sources) sources = insertDeps deps sources :=
  insertDeps_of_forall_mem fun _ included => mem_insertDeps.mpr (Or.inr included)

theorem map_insertDep {Other : Type*} [DecidableEq Other]
    (encode : Id → Other) (injective : Function.Injective encode)
    (deps : List Id) (source : Id) :
    (insertDep deps source).map encode = insertDep (deps.map encode) (encode source) := by
  have membership : encode source ∈ deps.map encode ↔ source ∈ deps := by
    rw [List.mem_map]
    constructor
    · rintro ⟨member, included, same⟩
      exact injective same ▸ included
    · intro included
      exact ⟨source, included, rfl⟩
  by_cases present : source ∈ deps <;> simp [insertDep, present, membership]

theorem map_insertDeps {Other : Type*} [DecidableEq Other]
    (encode : Id → Other) (injective : Function.Injective encode)
    (deps sources : List Id) :
    (insertDeps deps sources).map encode = insertDeps (deps.map encode) (sources.map encode) := by
  induction sources generalizing deps with
  | nil => simp
  | cons source sources ih => simp [ih, map_insertDep encode injective]

end Mettapedia.Machines.OrderedDependencyIds
