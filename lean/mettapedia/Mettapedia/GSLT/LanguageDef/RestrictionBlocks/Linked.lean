import Mathlib.Logic.Relation
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup

/-!
# Linked groups

Items with keys fall into **linked groups**: two items are in one group when a chain of items links them, each
consecutive pair sharing a key. `build` computes the groups by merging items in order, each item joining the groups
it shares a key with (`insert`).

A list of groups is a **grouping** of a list of items (`Grouping`) when its groups hold the items, are nonempty,
share no key across groups, and are each linked inside. A grouping of distinct items is unique up to the order of
the groups and of their members (`Grouping.unique`), and `build` gives one (`build_grouping`).

The groups of a block's components through restrictions (`groupsThrough`) are the linked groups of its components,
keyed by the restrictions they use.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Linked

variable {α : Type} (keys : α → List Nat)

/-- Two items share a key. -/
def Shares (first second : α) : Prop := ∃ key ∈ keys first, key ∈ keys second

variable {keys}

theorem Shares.symm {first second : α} (shares : Shares keys first second) : Shares keys second first :=
  let ⟨key, inFirst, inSecond⟩ := shares
  ⟨key, inSecond, inFirst⟩

variable (keys)

/-- Linked inside a list: a chain of its items, each consecutive pair sharing a key. -/
def LinkedIn (items : List α) : α → α → Prop :=
  Relation.ReflTransGen fun first second => first ∈ items ∧ second ∈ items ∧ Shares keys first second

/-- Whether an item shares a key with an item of a group. -/
def touches (item : α) (group : List α) : Bool :=
  group.any fun other => (keys item).any fun key => (keys other).contains key

/-- **Merge an item into the groups**: the groups it shares a key with join it, last. -/
def insert (item : α) (groups : List (List α)) : List (List α) :=
  groups.filter (fun group => !touches keys item group) ++
    [(groups.filter (touches keys item)).flatten ++ [item]]

/-- **The linked groups of a list of items**, merging the items in order. -/
def build (items : List α) : List (List α) :=
  items.foldl (fun groups item => insert keys item groups) []

/-- **A grouping of a list of items**: groups holding the items, nonempty, sharing no key across groups, each
linked inside. -/
structure Grouping (items : List α) (groups : List (List α)) : Prop where
  perm : groups.flatten.Perm items
  nonempty : ∀ group ∈ groups, group ≠ []
  apart : groups.Pairwise fun group other => ∀ first ∈ group, ∀ second ∈ other, ¬ Shares keys first second
  linked : ∀ group ∈ groups, ∀ first ∈ group, ∀ second ∈ group, LinkedIn keys group first second

variable {keys}

/-- Two different members of a pairwise list are related, for a symmetric relation. -/
theorem rel_of_pairwise {β : Type} {relation : β → β → Prop} (symm : ∀ first second, relation first second →
    relation second first) : ∀ {list : List β}, list.Pairwise relation → ∀ {first second : β}, first ∈ list →
      second ∈ list → first ≠ second → relation first second
  | [], _, _, _, inFirst, _, _ => absurd inFirst List.not_mem_nil
  | head :: tail, pairwise, first, second, inFirst, inSecond, different => by
      rw [List.pairwise_cons] at pairwise
      rcases List.mem_cons.mp inFirst with rfl | inFirst'
      · rcases List.mem_cons.mp inSecond with rfl | inSecond'
        · exact absurd rfl different
        · exact pairwise.1 second inSecond'
      · rcases List.mem_cons.mp inSecond with rfl | inSecond'
        · exact symm _ _ (pairwise.1 first inFirst')
        · exact rel_of_pairwise symm pairwise.2 inFirst' inSecond' different

theorem touches_iff {item : α} {group : List α} :
    touches keys item group = true ↔ ∃ other ∈ group, Shares keys item other := by
  simp [touches, Shares]

theorem LinkedIn.mono {items items' : List α} (subset : items ⊆ items') {first second : α}
    (linked : LinkedIn keys items first second) : LinkedIn keys items' first second := by
  induction linked with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step reached =>
      obtain ⟨inFirst, inSecond, shares⟩ := step
      exact reached.tail ⟨subset inFirst, subset inSecond, shares⟩

theorem LinkedIn.symm {items : List α} {first second : α} (linked : LinkedIn keys items first second) :
    LinkedIn keys items second first := by
  induction linked with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step reached =>
      obtain ⟨inFirst, inSecond, shares⟩ := step
      exact Relation.ReflTransGen.head ⟨inSecond, inFirst, shares.symm⟩ reached

theorem LinkedIn.single {items : List α} {first second : α} (inFirst : first ∈ items) (inSecond : second ∈ items)
    (shares : Shares keys first second) : LinkedIn keys items first second :=
  Relation.ReflTransGen.single ⟨inFirst, inSecond, shares⟩

/-- **The empty list of groups groups no items.** -/
theorem grouping_nil : Grouping keys ([] : List α) [] where
  perm := by simp
  nonempty := by simp
  apart := by simp
  linked := by simp

/-- **Merging an item keeps a grouping**, of the items with the new one last. -/
theorem Grouping.insert {items : List α} {groups : List (List α)} (grouping : Grouping keys items groups)
    (item : α) : Grouping keys (items ++ [item]) (Linked.insert keys item groups) := by
  set apart := groups.filter fun group => !touches keys item group
  set joined := groups.filter (touches keys item)
  have split : (apart ++ joined).Perm groups := by
    have := List.filter_append_perm (fun group => !touches keys item group) groups
    simpa [apart, joined, Bool.not_not] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Linked.insert, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    have flat : (apart.flatten ++ joined.flatten).Perm groups.flatten := by
      rw [← List.flatten_append]
      exact split.flatten
    rw [← List.append_assoc]
    exact (flat.append_right _).trans (grouping.perm.append_right _)
  · intro group member
    simp only [Linked.insert, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact grouping.nonempty group (List.mem_filter.mp member).1
    · simp
  · simp only [Linked.insert]
    rw [List.pairwise_append]
    refine ⟨(grouping.apart.sublist List.filter_sublist), List.pairwise_singleton _ _, ?_⟩
    intro group member merged mergedMember first inFirst second inSecond shares
    simp only [List.mem_singleton] at mergedMember
    subst mergedMember
    have notTouching : touches keys item group = false := by
      simpa [apart] using (List.mem_filter.mp member).2
    simp only [List.mem_append, List.mem_flatten, List.mem_singleton] at inSecond
    rcases inSecond with ⟨other, otherMember, inOther⟩ | rfl
    · have groupMember := (List.mem_filter.mp member).1
      have otherGroups := (List.mem_filter.mp otherMember).1
      have touching := (List.mem_filter.mp otherMember).2
      have different : group ≠ other := by
        rintro rfl
        rw [notTouching] at touching
        cases touching
      exact (rel_of_pairwise (fun _ _ separate first inFirst second inSecond shares =>
        separate second inSecond first inFirst shares.symm) grouping.apart groupMember otherGroups different)
        first inFirst second inOther shares
    · have := touches_iff.mpr ⟨first, inFirst, shares.symm⟩
      rw [notTouching] at this
      cases this
  · intro group member
    simp only [Linked.insert, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact grouping.linked group (List.mem_filter.mp member).1
    · have toItem : ∀ first ∈ joined.flatten ++ [item], LinkedIn keys (joined.flatten ++ [item]) first item := by
        intro first inFirst
        simp only [List.mem_append, List.mem_flatten, List.mem_singleton] at inFirst
        rcases inFirst with ⟨other, otherMember, inOther⟩ | rfl
        · obtain ⟨touched, touchedMember, shares⟩ := touches_iff.mp (List.mem_filter.mp otherMember).2
          have within : other ⊆ joined.flatten ++ [item] := fun element member =>
            List.mem_append_left _ (List.mem_flatten.mpr ⟨other, otherMember, member⟩)
          have toTouched := (grouping.linked other (List.mem_filter.mp otherMember).1 first inOther touched
            touchedMember).mono within
          exact toTouched.tail ⟨within touchedMember, by simp, shares.symm⟩
        · exact Relation.ReflTransGen.refl
      intro first inFirst second inSecond
      exact (toItem first inFirst).trans (toItem second inSecond).symm

/-- **`build` gives a grouping.** -/
theorem build_grouping (items : List α) : Grouping keys items (build keys items) := by
  unfold build
  suffices general : ∀ (done : List α) (groups : List (List α)), Grouping keys done groups →
      Grouping keys (done ++ items) (items.foldl (fun groups item => Linked.insert keys item groups) groups) by
    simpa using general [] [] grouping_nil
  induction items with
  | nil => intro done groups grouping; simpa using grouping
  | cons item rest recurse =>
      intro done groups grouping
      simpa [List.append_assoc] using recurse (done ++ [item]) _ (grouping.insert item)

/-! ## A grouping of distinct items is unique -/

theorem Grouping.mem_items {items : List α} {groups : List (List α)} (grouping : Grouping keys items groups)
    {group : List α} (member : group ∈ groups) {item : α} (inGroup : item ∈ group) : item ∈ items :=
  grouping.perm.subset (List.mem_flatten.mpr ⟨group, member, inGroup⟩)

theorem Grouping.exists_group {items : List α} {groups : List (List α)} (grouping : Grouping keys items groups)
    {item : α} (member : item ∈ items) : ∃ group ∈ groups, item ∈ group :=
  List.mem_flatten.mp (grouping.perm.symm.subset member)

/-- **Two groups of a grouping of distinct items that share an item are one group.** -/
theorem Grouping.eq_of_mem {items : List α} {groups : List (List α)} (grouping : Grouping keys items groups)
    (nodup : items.Nodup) {first second : List α} (firstMember : first ∈ groups) (secondMember : second ∈ groups)
    {item : α} (inFirst : item ∈ first) (inSecond : item ∈ second) : first = second := by
  have flatNodup : groups.flatten.Nodup := grouping.perm.nodup_iff.mpr nodup
  rw [List.nodup_flatten] at flatNodup
  by_contra different
  exact (rel_of_pairwise (fun _ _ disjoint => List.disjoint_comm.mp disjoint) flatNodup.2
    firstMember secondMember different)
    inFirst inSecond

/-- **Items linked in the items are in one group.** -/
theorem Grouping.closed {items : List α} {groups : List (List α)} (grouping : Grouping keys items groups)
    {group : List α} (member : group ∈ groups) {first second : α} (inGroup : first ∈ group)
    (linked : LinkedIn keys items first second) : second ∈ group := by
  induction linked with
  | refl => exact inGroup
  | tail _ step reached =>
      obtain ⟨_, inItems, shares⟩ := step
      obtain ⟨other, otherMember, inOther⟩ := grouping.exists_group inItems
      by_cases same : group = other
      · exact same ▸ inOther
      · exact absurd shares (rel_of_pairwise (fun _ _ separate first inFirst second inSecond shares =>
          separate second inSecond first inFirst shares.symm) grouping.apart member otherMember same _ reached _
          inOther)

/-- **The group of an item holds exactly the items linked to it.** -/
theorem Grouping.mem_iff {items : List α} {groups : List (List α)} (grouping : Grouping keys items groups)
    {group : List α} (member : group ∈ groups) {first : α} (inGroup : first ∈ group)
    (second : α) : second ∈ group ↔ LinkedIn keys items first second :=
  ⟨fun inSecond => (grouping.linked group member first inGroup second inSecond).mono
    fun _ inGroup' => grouping.mem_items member inGroup', grouping.closed member inGroup⟩

theorem Grouping.group_nodup {items : List α} {groups : List (List α)} (grouping : Grouping keys items groups)
    (nodup : items.Nodup) {group : List α} (member : group ∈ groups) : group.Nodup := by
  have flatNodup : groups.flatten.Nodup := grouping.perm.nodup_iff.mpr nodup
  exact (List.nodup_flatten.mp flatNodup).1 group member

/-- **Groups of two groupings of distinct items sharing an item hold the same items.** -/
theorem Grouping.perm_of_mem {items : List α} {groups groups' : List (List α)} (grouping : Grouping keys items groups)
    (grouping' : Grouping keys items groups') (nodup : items.Nodup) {group group' : List α}
    (member : group ∈ groups) (member' : group' ∈ groups') {item : α} (inGroup : item ∈ group)
    (inGroup' : item ∈ group') : group.Perm group' :=
  (List.perm_ext_iff_of_nodup (grouping.group_nodup nodup member) (grouping'.group_nodup nodup member')).mpr
    fun other => (grouping.mem_iff member inGroup other).trans (grouping'.mem_iff member' inGroup' other).symm

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Linked
