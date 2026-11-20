import Mettapedia.Machines.Specialization.CopyingCollector

/-!
# Relocating roots of a prepared frame

A slot holds a scalar or an address. Copying visits the root closure,
then translates the addressed slots into the copied table. Position,
scalar tags, root observations and identity sharing are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.FrameRelocation

open CopyingCollector RationalTermGraph

variable {Scalar Address Label : Type} [DecidableEq Address]

def roots : List (Scalar ⊕ Address) → List Address :=
  List.filterMap (fun slot => match slot with
    | .inl _ => none
    | .inr address => some address)

def relocateSlot (table : KeyedTable Address Label) :
    Scalar ⊕ Address → Option (Scalar ⊕ table.Node)
  | .inl scalar => some (.inl scalar)
  | .inr address => (table.node? address).map Sum.inr

def SlotRelated (graph : Graph Address Label) (table : KeyedTable Address Label) :
    Scalar ⊕ Address → Scalar ⊕ table.Node → Prop
  | .inl old, .inl after => old = after
  | .inr old, .inr after => table.key after = old ∧ Bisimilar graph table.graph old after
  | .inl _, .inr _ | .inr _, .inl _ => False

theorem relocateSlot_exact (graph : Graph Address Label) {initial : List Address}
    (inventory : Inventory graph initial) {before : Scalar ⊕ Address}
    {after : Scalar ⊕ inventory.table.Node}
    (moves : relocateSlot inventory.table before = some after) :
    SlotRelated graph inventory.table before after := by
  cases before with
  | inl scalar =>
    cases moves
    rfl
  | inr address =>
    obtain ⟨node, found, rfl⟩ := Option.map_eq_some_iff.mp moves
    exact ⟨(inventory.table.node?_eq_some_iff _ _).mp found, inventory.relocates_terms found⟩

/-- Translate only after copying has succeeded and all live roots are
available. A refusal contains no partially rewritten frame. -/
def relocate (table : KeyedTable Address Label) (frame : List (Scalar ⊕ Address)) :
    Option (List (Scalar ⊕ table.Node)) := frame.mapM (relocateSlot table)

private theorem relocate_cons (table : KeyedTable Address Label) (slot : Scalar ⊕ Address)
    (rest : List (Scalar ⊕ Address)) :
    relocate table (slot :: rest) = (relocateSlot table slot).bind fun moved =>
      (relocate table rest).map (List.cons moved) := by
  simp only [relocate, List.mapM_cons]
  cases relocateSlot table slot <;> cases rest.mapM (relocateSlot table) <;> rfl

theorem relocate_exact (graph : Graph Address Label) {initial : List Address}
    (inventory : Inventory graph initial) {before : List (Scalar ⊕ Address)}
    {after : List (Scalar ⊕ inventory.table.Node)}
    (result : relocate inventory.table before = some after) :
    List.Forall₂ (SlotRelated graph inventory.table) before after := by
  induction before generalizing after with
  | nil =>
    cases result
    exact .nil
  | cons slot rest ih =>
    rw [relocate_cons] at result
    obtain ⟨value, moved, following⟩ := Option.bind_eq_some_iff.mp result
    obtain ⟨retained, later, rfl⟩ := Option.map_eq_some_iff.mp following
    exact .cons (relocateSlot_exact graph inventory moved) (ih later)

theorem relocate_complete (graph : Graph Address Label) {initial : List Address}
    (inventory : Inventory graph initial) (frame : List (Scalar ⊕ Address))
    (visible : roots frame ⊆ initial) :
    ∃ moved, relocate inventory.table frame = some moved := by
  induction frame with
  | nil => exact ⟨[], rfl⟩
  | cons slot rest ih =>
    have carried : roots rest ⊆ initial := by
      intro address member
      apply visible
      cases slot with
      | inl scalar => simpa only [roots, List.filterMap_cons] using member
      | inr root =>
        simp only [roots, List.filterMap_cons]
        exact List.mem_cons_of_mem root member
    obtain ⟨rest', done⟩ := ih carried
    obtain ⟨first, found⟩ : ∃ first, relocateSlot inventory.table slot = some first := by
      cases slot with
      | inl scalar => exact ⟨.inl scalar, rfl⟩
      | inr address =>
        have isRoot : address ∈ initial := visible (by simp [roots])
        obtain ⟨node, mapped, _, _⟩ :=
          inventory.reads_copy address ⟨address, isRoot, .root⟩
        exact ⟨.inr node, by simp [relocateSlot, mapped]⟩
    refine ⟨first :: rest', ?_⟩
    rw [relocate_cons, found]
    simp [done]

theorem relocated_roots_share_exactly {table : KeyedTable Address Label}
    {first second : Address} {first' second' : table.Node}
    (left : table.node? first = some first') (right : table.node? second = some second') :
    first' = second' ↔ first = second := by
  have a := (table.node?_eq_some_iff _ _).mp left
  have b := (table.node?_eq_some_iff _ _).mp right
  rw [← a, ← b]
  exact ⟨congrArg _, fun same => table.key_injective same⟩

/-- All observed depths of a relocated addressed slot agree, including
ordered repeated children. -/
theorem relocated_slot_observation (graph : Graph Address Label) {initial : List Address}
    (inventory : Inventory graph initial) {address : Address} {node : inventory.table.Node}
    (moved : inventory.table.node? address = some node) (depth : Nat) :
    observe graph depth address = observe inventory.table.graph depth node := by
  have follows := inventory.relocates_terms moved
  exact (bisimilar_iff_observe_eq.mp follows) depth

namespace Controls

private def graph : Graph Nat String where
  label node := if node = 4 then "outer" else "inner"
  children node := if node = 4 then [6, 6] else []

private def frame : List (Int ⊕ Nat) := [.inl 8, .inr 4, .inr 4, .inr 6]

private def relocateWithRoom (capacity : Nat) : Option (List (Int ⊕ Nat)) :=
  (discover graph (roots frame) capacity).bind fun copied =>
    (relocate copied.table frame).map (List.map (Sum.map id Fin.val))

theorem unboxed_values_and_repeated_roots_survive_collection :
    relocateWithRoom 2 = some [.inl 8, .inr 0, .inr 0, .inr 1] := by decide +kernel

theorem an_incomplete_root_copy_has_no_frame_publication : relocateWithRoom 1 = none := by decide +kernel

end Controls

end Mettapedia.Machines.Specialization.FrameRelocation
