import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Linked
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Molecules

/-!
# The groups through restrictions are linked groups

The groups of a block's components through allowed restrictions (`groupsThrough`) are the linked groups of the
components, each keyed by the allowed restrictions it uses (`throughKeys`), read as groups (`asGroup`): the
restrictions they use in increasing order, and their components (`groupsThrough_map`). The components may be
named by any items, such as their places in a block, so that equal components stay apart.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {ι : Type}

/-- The keys of an item through allowed restrictions: the allowed restrictions of the block its component uses. -/
def throughKeys (allowed : List Nat) (count : Nat) (value : ι → Pattern) (item : ι) : List Nat :=
  (usedRestrictions count (value item)).filter allowed.contains

/-- The allowed restrictions a list of items uses, in increasing order. -/
def restrictionsOf (allowed : List Nat) (count : Nat) (value : ι → Pattern) (items : List ι) : List Nat :=
  (List.range count).filter fun index => items.any fun item => (throughKeys allowed count value item).contains index

/-- **A list of items read as a group**: the allowed restrictions they use, and their components. -/
def asGroup (allowed : List Nat) (count : Nat) (value : ι → Pattern) (items : List ι) : Group :=
  ⟨restrictionsOf allowed count value items, items.map value⟩

theorem throughKeys_lt {allowed : List Nat} {count : Nat} {value : ι → Pattern} {item : ι} {index : Nat}
    (member : index ∈ throughKeys allowed count value item) : index < count := by
  unfold throughKeys usedRestrictions at member
  exact List.mem_range.mp (List.mem_filter.mp (List.mem_filter.mp member).1).1

theorem mem_restrictionsOf {allowed : List Nat} {count : Nat} {value : ι → Pattern} {items : List ι}
    {index : Nat} : index ∈ restrictionsOf allowed count value items ↔
      ∃ item ∈ items, index ∈ throughKeys allowed count value item := by
  unfold restrictionsOf
  simp only [List.mem_filter, List.mem_range, List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨-, item, member, listed⟩
    exact ⟨item, member, listed⟩
  · rintro ⟨item, member, listed⟩
    exact ⟨throughKeys_lt listed, item, member, listed⟩

/-- **A component shares an allowed restriction with a group exactly when it touches one of its items.** -/
theorem shares_asGroup (allowed : List Nat) (count : Nat) (value : ι → Pattern) (item : ι) (items : List ι) :
    shares (throughKeys allowed count value item) (asGroup allowed count value items).restrictions =
      Linked.touches (throughKeys allowed count value) item items := by
  apply Bool.eq_iff_iff.mpr
  rw [Linked.touches_iff]
  simp only [shares, asGroup, List.any_eq_true, List.contains_iff_mem, mem_restrictionsOf, Linked.Shares]
  constructor
  · rintro ⟨key, inItem, other, member, inOther⟩
    exact ⟨other, member, key, inItem, inOther⟩
  · rintro ⟨other, member, key, inItem, inOther⟩
    exact ⟨key, inItem, other, member, inOther⟩

/-- **Merging a component is merging its item.** -/
theorem insertUsing_asGroup (allowed : List Nat) (count : Nat) (value : ι → Pattern) (item : ι)
    (groups : List (List ι)) :
    insertUsing count (throughKeys allowed count value item) (value item)
        (groups.map (asGroup allowed count value)) =
      (Linked.insert (throughKeys allowed count value) item groups).map (asGroup allowed count value) := by
  have touching : ∀ group : List ι, shares (throughKeys allowed count value item)
      (asGroup allowed count value group).restrictions =
        Linked.touches (throughKeys allowed count value) item group :=
    shares_asGroup allowed count value item
  simp only [insertUsing, Linked.insert, List.map_append, List.map_cons, List.map_nil, List.filter_map,
    Function.comp_def, touching]
  congr 2
  simp only [asGroup, Group.mk.injEq]
  constructor
  · unfold restrictionsOf
    apply List.filter_congr
    intro index _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem, List.mem_map, List.mem_filter,
      List.mem_append, List.mem_flatten, List.mem_singleton]
    constructor
    · rintro (inItem | ⟨group, ⟨original, ⟨originalMember, touched⟩, rfl⟩, inGroup⟩)
      · exact ⟨item, .inr rfl, inItem⟩
      · obtain ⟨other, otherMember, listed⟩ := mem_restrictionsOf.mp inGroup
        exact ⟨other, .inl ⟨original, ⟨originalMember, touched⟩, otherMember⟩, listed⟩
    · rintro ⟨other, (⟨original, ⟨originalMember, touched⟩, otherMember⟩ | rfl), listed⟩
      · exact .inr ⟨_, ⟨original, ⟨originalMember, touched⟩, rfl⟩,
          mem_restrictionsOf.mpr ⟨other, otherMember, listed⟩⟩
      · exact .inl listed
  · simp [List.flatMap, List.map_flatten, asGroup, Function.comp_def]

/-- **The groups through allowed restrictions are the linked groups of the components' items.** -/
theorem groupsThrough_map (allowed : List Nat) (count : Nat) (value : ι → Pattern) (items : List ι) :
    groupsThrough allowed count (items.map value) =
      (Linked.build (throughKeys allowed count value) items).map (asGroup allowed count value) := by
  unfold groupsThrough Linked.build
  rw [List.foldl_map]
  suffices general : ∀ (groups : List (List ι)) (rest : List ι),
      rest.foldl (fun groups item => insertUsing count
          ((usedRestrictions count (value item)).filter allowed.contains) (value item) groups)
        (groups.map (asGroup allowed count value)) =
      (rest.foldl (fun groups item => Linked.insert (throughKeys allowed count value) item groups) groups).map
        (asGroup allowed count value) by
    simpa using general [] items
  intro groups rest
  induction rest generalizing groups with
  | nil => rfl
  | cons item rest recurse =>
      simp only [List.foldl_cons]
      rw [show insertUsing count ((usedRestrictions count (value item)).filter allowed.contains) (value item)
          (groups.map (asGroup allowed count value)) =
          (Linked.insert (throughKeys allowed count value) item groups).map (asGroup allowed count value) from
        insertUsing_asGroup allowed count value item groups]
      exact recurse _

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
