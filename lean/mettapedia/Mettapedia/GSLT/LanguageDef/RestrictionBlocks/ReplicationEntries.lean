import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationClasses

/-!
# Entries of a block by places

The class of a place among some live places is the live places linked to it (`classIn`), and a pattern is an entry
of the live places when it is the entry of the class of one of them (`IsEntry`). The entries of the classes the
places are grouped into are exactly these (`mem_build_entries`).

Classes follow the places along a map telling them apart and keeping which share a restriction
(`linkedIn_map_iff`), and they lose only the removed places when removing places reroutes no path
(`classIn_filter`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {block : ReplicationBlock}

/-! ## Classes of places -/

open Classical in
/-- **The class of a place** among some live places: the live places linked to it. -/
noncomputable def classIn (block : ReplicationBlock) (form : Prenex) (live : List Nat) (place : Nat) : List Nat :=
  live.filter fun other => Linked.LinkedIn (keysAt block form) live place other

theorem mem_classIn {form : Prenex} {live : List Nat} {place other : Nat} :
    other ∈ classIn block form live place ↔ other ∈ live ∧ Linked.LinkedIn (keysAt block form) live place other := by
  classical
  unfold classIn
  simp

/-- **A pattern is an entry of some live places** when it is the entry of the class of one of them. -/
def IsEntry (block : ReplicationBlock) (form : Prenex) (live : List Nat) (pattern : Pattern) : Prop :=
  ∃ place ∈ live, entryOf block form (classIn block form live place) = pattern

/-- The entry of places forgets their order. -/
theorem entryOf_perm (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {form : Prenex} (atomic : form.Atomic block.toBlock) {first second : List Nat}
    (inside : ∀ place ∈ first, place < form.components.length) (permutation : first.Perm second) :
    entryOf block form first = entryOf block form second := by
  unfold entryOf restrictTo
  rw [normal_perm fresh restrictFresh (permutation.map _) (fun component member => by
    obtain ⟨place, inFirst, rfl⟩ := List.mem_map.mp member
    exact atomic _ (placeValue_mem (inside place inFirst)))]

/-- **The entries of the classes the live places are grouped into** are the entries of the live places. -/
theorem mem_build_entries (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) {form : Prenex} (atomic : form.Atomic block.toBlock)
    {live : List Nat} (nodup : live.Nodup) (inside : ∀ place ∈ live, place < form.components.length)
    (pattern : Pattern) :
    pattern ∈ (Linked.build (keysAt block form) live).map (entryOf block form) ↔ IsEntry block form live pattern := by
  have grouping := Linked.build_grouping (keys := keysAt block form) live
  have classPerm : ∀ group ∈ Linked.build (keysAt block form) live, ∀ place ∈ group,
      group.Perm (classIn block form live place) := by
    intro group member place inGroup
    have groupNodup := grouping.group_nodup nodup member
    have classNodup : (classIn block form live place).Nodup := by
      classical
      unfold classIn
      exact nodup.filter _
    rw [List.perm_ext_iff_of_nodup groupNodup classNodup]
    intro other
    rw [mem_classIn, grouping.mem_iff member inGroup other]
    exact ⟨fun linked => ⟨grouping.mem_items member ((grouping.mem_iff member inGroup other).mpr linked), linked⟩,
      fun ⟨_, linked⟩ => linked⟩
  constructor
  · intro mapped
    obtain ⟨group, member, rfl⟩ := List.mem_map.mp mapped
    obtain ⟨place, inGroup⟩ := List.exists_mem_of_ne_nil _ (grouping.nonempty group member)
    refine ⟨place, grouping.mem_items member inGroup, ?_⟩
    exact (entryOf_perm fresh restrictFresh atomic (fun other inClass => inside other (mem_classIn.mp inClass).1)
      (classPerm group member place inGroup).symm)
  · rintro ⟨place, inLive, rfl⟩
    obtain ⟨group, member, inGroup⟩ := grouping.exists_group inLive
    exact List.mem_map.mpr ⟨group, member, entryOf_perm fresh restrictFresh atomic
      (fun other inGroup' => inside other (grouping.mem_items member inGroup')) (classPerm group member place inGroup)⟩

/-! ## Classes along maps of places -/

/-- **Linked places stay linked along a map telling them apart and keeping which share a restriction.** -/
theorem linkedIn_map_iff {keys keys' : Nat → List Nat} {items : List Nat} (map : Nat → Nat)
    (injective : ∀ first ∈ items, ∀ second ∈ items, map first = map second → first = second)
    (shares : ∀ first ∈ items, ∀ second ∈ items, Linked.Shares keys' (map first) (map second) ↔
      Linked.Shares keys first second)
    {first second : Nat} (inFirst : first ∈ items) (inSecond : second ∈ items) :
    Linked.LinkedIn keys' (items.map map) (map first) (map second) ↔ Linked.LinkedIn keys items first second := by
  constructor
  · intro linked
    suffices general : ∀ target, Linked.LinkedIn keys' (items.map map) (map first) target →
        ∀ original ∈ items, target = map original → Linked.LinkedIn keys items first original from
      general _ linked second inSecond rfl
    intro target path
    induction path with
    | refl =>
        intro original inOriginal same
        rw [injective first inFirst original inOriginal same]
        exact Relation.ReflTransGen.refl
    | tail _ step reached =>
        intro original inOriginal same
        obtain ⟨inMiddle, _, sharing⟩ := step
        obtain ⟨middle, inItems, rfl⟩ := List.mem_map.mp inMiddle
        subst same
        exact (reached middle inItems rfl).tail ⟨inItems, inOriginal, (shares middle inItems original inOriginal).mp sharing⟩
  · intro linked
    clear inSecond
    induction linked with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step reached =>
        obtain ⟨inMiddle, inLast, sharing⟩ := step
        exact reached.tail ⟨List.mem_map_of_mem inMiddle, List.mem_map_of_mem inLast,
          (shares _ inMiddle _ inLast).mpr sharing⟩

/-- **Removing places that reroute no path keeps the classes of the others, without the removed places.** -/
theorem classIn_filter {form : Prenex} {live : List Nat} (removed : Nat → Bool)
    (reroute : ∀ first ∈ live, removed first = false → ∀ second ∈ live, removed second = false →
      Linked.LinkedIn (keysAt block form) live first second →
      Linked.LinkedIn (keysAt block form) (live.filter fun place => !removed place) first second)
    {place : Nat} (inLive : place ∈ live) (kept : removed place = false) :
    ∀ other, other ∈ classIn block form (live.filter fun place => !removed place) place ↔
      other ∈ (classIn block form live place).filter fun place => !removed place := by
  intro other
  rw [List.mem_filter, mem_classIn, mem_classIn, List.mem_filter]
  constructor
  · rintro ⟨⟨inOther, otherKept⟩, linked⟩
    exact ⟨⟨inOther, linked.mono fun element member => (List.mem_filter.mp member).1⟩, otherKept⟩
  · rintro ⟨⟨inOther, linked⟩, otherKept⟩
    exact ⟨⟨inOther, otherKept⟩, reroute place inLive kept other inOther (by simpa using otherKept) linked⟩

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
