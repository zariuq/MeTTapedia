import Mettapedia.GSLT.Parsing.PackedForestSelection

/-! Finite catalogues over the existing packed-forest extraction operation.
A closed catalogue covers every finite selected unfolding, including forests
with cycles. Closure is checked rather than inferred from a depth budget. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PackedForestCatalogue

open PackedForestSelection

universe u v

mutual
  private def equalTree {Family : Type v} [DecidableEq Family] :
      (left right : Derivation Family) → Decidable (left = right)
    | .node first children, .node second others =>
      if same : first = second then
        match equalTrees children others with
        | isTrue rest => isTrue (by subst_vars; rfl)
        | isFalse rest => isFalse (by intro h; cases h; exact rest rfl)
      else isFalse (by intro h; cases h; exact same rfl)

  private def equalTrees {Family : Type v} [DecidableEq Family] :
      (left right : List (Derivation Family)) → Decidable (left = right)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | first :: rest, second :: others =>
      match equalTree first second, equalTrees rest others with
      | isTrue same, isTrue tail => isTrue (by subst_vars; rfl)
      | isFalse same, _ => isFalse (by intro h; cases h; exact same rfl)
      | _, isFalse tail => isFalse (by intro h; cases h; exact tail rfl)
end

instance {Family : Type v} [DecidableEq Family] : DecidableEq (Derivation Family) := equalTree

variable {Key : Type u} {Family : Type v}

/- Independent finite-tree semantics of selected families and their ordered
child references. Repeated child references are separate choices. -/
mutual
inductive Unfolds (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool) :
    Key → Derivation Family → Prop where
  | node {key : Key} {family : Family} {values : List (Derivation Family)}
      (member : family ∈ families key) (selected : allow family = true)
      (nested : ChildrenUnfold families children allow (children family) values) :
      Unfolds families children allow key (.node family values)

inductive ChildrenUnfold (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool) :
    List Key → List (Derivation Family) → Prop where
  | nil : ChildrenUnfold families children allow [] []
  | cons {key : Key} {keys : List Key} {tree : Derivation Family} {trees : List (Derivation Family)}
      (head : Unfolds families children allow key tree)
      (tail : ChildrenUnfold families children allow keys trees) :
      ChildrenUnfold families children allow (key :: keys) (tree :: trees)
end

theorem children_iff (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (keys : List Key) (values : List (Derivation Family)) :
    ChildrenUnfold families children allow keys values ↔
      List.Forall₂ (Unfolds families children allow) keys values := by
  constructor
  · intro source
    induction keys generalizing values with
    | nil => cases source; exact .nil
    | cons key keys ih => cases source with | cons head rest => exact .cons head (ih _ rest)
  · intro source
    induction source with
    | nil => exact .nil
    | cons head _ ih => exact .cons head ih

def next (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (cache : Key → List (Derivation Family)) (key : Key) : List (Derivation Family) :=
  (families key).flatMap fun family =>
    if allow family then (combinations ((children family).map cache)).map (.node family) else []

theorem next_extract (families : Key → List Family) (children : Family → List Key)
    (allow : Family → Bool) (depth : Nat) (key : Key) :
    next families children allow (extract families children allow depth) key =
      extract families children allow (depth + 1) key := rfl

theorem combinations_mem {α : Type v} (choices : List (List α)) (values : List α) :
    values ∈ combinations choices ↔ List.Forall₂ (fun candidates value => value ∈ candidates) choices values := by
  induction choices generalizing values with
  | nil => cases values <;> simp [combinations]
  | cons first rest ih =>
    cases values with
    | nil => simp [combinations]
    | cons value tail => simp [combinations, ih, List.forall₂_cons]

theorem next_mem (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (cache : Key → List (Derivation Family)) (key : Key) (value : Derivation Family) :
    value ∈ next families children allow cache key ↔
      ∃ family ∈ families key, allow family = true ∧ ∃ nested,
        List.Forall₂ (fun child tree => tree ∈ cache child) (children family) nested ∧
        value = .node family nested := by
  simp only [next, List.mem_flatMap]
  constructor
  · rintro ⟨family, member, produced⟩
    split at produced
    · rename_i selected
      obtain ⟨nested, inside, same⟩ := List.mem_map.mp produced
      refine ⟨family, member, selected, nested, ?_, same.symm⟩
      exact List.forall₂_map_left_iff.mp ((combinations_mem _ _).mp inside)
    · simp at produced
  · rintro ⟨family, member, selected, nested, available, rfl⟩
    refine ⟨family, member, ?_⟩
    rw [if_pos selected]
    exact List.mem_map.mpr ⟨nested, (combinations_mem _ _).mpr
      (List.forall₂_map_left_iff.mpr available), rfl⟩

def Sound (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (cache : Key → List (Derivation Family)) : Prop :=
  ∀ key tree, tree ∈ cache key → Unfolds families children allow key tree

theorem next_sound (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (cache : Key → List (Derivation Family)) (sound : Sound families children allow cache) :
    Sound families children allow (next families children allow cache) := by
  intro key tree member
  obtain ⟨family, present, selected, nested, available, rfl⟩ := (next_mem _ _ _ _ _ _).mp member
  exact .node present selected ((children_iff _ _ _ _ _).mpr
    (available.imp (fun child value member => sound child value member)))

theorem closed_complete (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (cache : Key → List (Derivation Family))
    (closed : ∀ key, next families children allow cache key ⊆ cache key)
    {key : Key} {tree : Derivation Family} (source : Unfolds families children allow key tree) :
    tree ∈ cache key := by
  induction source using Unfolds.rec
    (motive_2 := fun keys trees _ => List.Forall₂ (fun key tree => tree ∈ cache key) keys trees) with
  | node member selected _ ih =>
    apply closed _
    apply (next_mem _ _ _ _ _ _).mpr
    exact ⟨_, member, selected, _, ih, rfl⟩
  | nil => exact .nil
  | cons _ _ head rest => exact .cons head rest

end Mettapedia.GSLT.Parsing.PackedForestCatalogue
