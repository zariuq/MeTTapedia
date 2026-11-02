import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyGroups
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.GroupsLinked
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationForm
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.Finset.Sort

/-!
# Absorption is removing copy groups

The components of a block, by their places, form a system for absorption (`absorptionSystem`): each mentions the
restrictions it uses, the replicated ones are those of the replication, and a set of places is a copy for a
replicated component when the canonical form of its group's block is that of the component's argument.

One absorption on the block of a list of places removes a copy group of that system (`absorbOnce_step`), and finds
none exactly when there is none (`absorbOnce_none`), so absorption in rounds removes copy groups until none is left
(`absorbRounds_absorbs`). The copy test reads a group's components in any order, given a canonical form that does
not tell orders of a block's components apart.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The component at a place, inaction past the end. -/
def placeValue (block : ReplicationBlock) (components : List Pattern) (place : Nat) : Pattern :=
  components.getD place (.apply block.unit [])

/-- The restrictions of a block of `count` a component does not mention: those its copies may own. -/
def allowedFor (count : Nat) (component : Pattern) : List Nat :=
  (List.range count).filter fun index => !mentions index component

/-- **The copy test**: the canonical form of a group's block is that of the replicated argument, renumbered as the
rest of the block reads it, and is not itself a replication; every replication in the group has a smaller canonical
argument;
the group mentions every restriction the replicated component mentions. -/
def CopyTest (block : ReplicationBlock) (canonical : Pattern → Pattern) (count : Nat) (component : Pattern)
    (group : Group) : Prop :=
  canonical (copyOf block.toBlock count group) =
      canonical (rename (Prenex.groupIndex count (outsideOf count group.restrictions)) (argumentOf? component)) ∧
    isReplicated block (canonical (copyOf block.toBlock count group)) = false ∧
    (∀ member ∈ group.components, isReplicated block member = true →
      size (canonical (argumentOf? member)) < size (canonical (argumentOf? component))) ∧
    ∀ index < count, mentions index component = true → ∃ member ∈ group.components, mentions index member = true

/-- **The absorption system of a block's components**, by place. -/
def absorptionSystem (block : ReplicationBlock) (canonical : Pattern → Pattern) (count : Nat)
    (components : List Pattern) (height : Nat → Nat) : CopyGroups.System Nat where
  mentions place := (usedRestrictions count (placeValue block components place)).toFinset
  replicated place := isReplicated block (placeValue block components place) = true
  copy group place := CopyTest block canonical count (placeValue block components place)
    (asGroup (allowedFor count (placeValue block components place)) count (placeValue block components)
      (group.sort (· ≤ ·)))
  height := height

/-- A canonical form that does not tell orders of a group's components apart. -/
def OrderBlind (block : ReplicationBlock) (canonical : Pattern → Pattern) : Prop :=
  ∀ (count : Nat) (restrictions : List Nat) (first second : List Pattern), first.Perm second →
    canonical (copyOf block.toBlock count ⟨restrictions, first⟩) =
      canonical (copyOf block.toBlock count ⟨restrictions, second⟩)

/-- A canonical form whose copy test does not read the order of a group of a block's places. -/
def BlindOn (block : ReplicationBlock) (canonical : Pattern → Pattern) (count : Nat) (components : List Pattern) :
    Prop :=
  ∀ (place : Nat) (group : List Nat), place < components.length →
    isReplicated block (placeValue block components place) = true → place ∉ group → group.Nodup →
    (∀ member ∈ group, member < components.length) →
    (CopyTest block canonical count (placeValue block components place)
        (asGroup (allowedFor count (placeValue block components place)) count (placeValue block components)
          (group.toFinset.sort (· ≤ ·))) ↔
      CopyTest block canonical count (placeValue block components place)
        (asGroup (allowedFor count (placeValue block components place)) count (placeValue block components) group))

/-- **The Boolean test of one absorption is the copy test.** -/
theorem copyTest_iff_bool (block : ReplicationBlock) (canonical : Pattern → Pattern) (count : Nat) {label : String}
    {argument component : Pattern} (componentIs : component = .apply label [argument]) (group : Group) :
    ((canonical (copyOf block.toBlock count group) ==
          canonical (rename (Prenex.groupIndex count (outsideOf count group.restrictions)) argument)) &&
        !isReplicated block (canonical (copyOf block.toBlock count group)) &&
        group.components.all (fun member =>
          !isReplicated block member || decide (size (canonical (argumentOf? member)) < size (canonical argument))) &&
        (List.range count).all (fun index =>
          !mentions index (.apply label [argument]) || group.components.any (mentions index))) = true ↔
      CopyTest block canonical count component group := by
  subst componentIs
  unfold CopyTest
  simp only [argumentOf?, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true,
    List.mem_range, List.any_eq_true]
  constructor
  · rintro ⟨⟨⟨same, notReplicated⟩, smaller⟩, mentioned⟩
    refine ⟨same, notReplicated, fun member inGroup replicated => ?_, fun index below mentionedHere => ?_⟩
    · rcases smaller member inGroup with notReplicated' | small
      · rw [replicated] at notReplicated'
        cases notReplicated'
      · exact of_decide_eq_true small
    · rcases mentioned index below with notMentioned | witness
      · rw [mentionedHere] at notMentioned
        cases notMentioned
      · exact witness
  · rintro ⟨same, notReplicated, smaller, mentioned⟩
    refine ⟨⟨⟨same, notReplicated⟩, fun member inGroup => ?_⟩, fun index below => ?_⟩
    · cases replicated : isReplicated block member with
      | false => exact .inl rfl
      | true => exact .inr (decide_eq_true (smaller member inGroup replicated))
    · cases mentionedHere : mentions index (.apply label [argument]) with
      | false => exact .inl rfl
      | true => exact .inr (mentioned index below mentionedHere)

section System

variable {block : ReplicationBlock} {canonical : Pattern → Pattern} {count : Nat} {components : List Pattern}
  {height : Nat → Nat}

theorem mem_usedRestrictions {component : Pattern} {index : Nat} :
    index ∈ usedRestrictions count component ↔ index < count ∧ mentions index component = true := by
  simp [usedRestrictions]

/-- **Linked for a replicated component is sharing a key through the restrictions it does not mention.** -/
theorem linkFor_iff_shares (place first second : Nat) :
    (absorptionSystem block canonical count components height).LinkFor place first second ↔
      Linked.Shares (throughKeys (allowedFor count (placeValue block components place)) count
        (placeValue block components)) first second := by
  simp only [CopyGroups.System.LinkFor, absorptionSystem, Linked.Shares, throughKeys, List.mem_toFinset,
    List.mem_filter, List.contains_iff_mem, allowedFor, List.mem_range, mem_usedRestrictions,
    Bool.not_eq_true']
  constructor
  · rintro ⟨index, ⟨below, inFirst⟩, ⟨-, inSecond⟩, notPlace⟩
    have unmentioned : mentions index (placeValue block components place) = false := by
      cases mentioned : mentions index (placeValue block components place) with
      | false => rfl
      | true => exact absurd ⟨below, mentioned⟩ notPlace
    exact ⟨index, ⟨⟨below, inFirst⟩, below, unmentioned⟩, ⟨below, inSecond⟩, below, unmentioned⟩
  · rintro ⟨index, ⟨⟨below, inFirst⟩, -, unmentioned⟩, ⟨-, inSecond⟩, -⟩
    exact ⟨index, ⟨below, inFirst⟩, ⟨below, inSecond⟩, fun ⟨_, mentioned⟩ => by
      rw [mentioned] at unmentioned
      cases unmentioned⟩

theorem mem_eraseIdx_of_nodup {places : List Nat} (nodup : places.Nodup) {position : Nat}
    (inside : position < places.length) (place : Nat) :
    place ∈ places.eraseIdx position ↔ place ≠ places[position] ∧ place ∈ places := by
  rw [← List.Nodup.erase_getElem nodup position inside, List.Nodup.mem_erase_iff nodup]

theorem toFinset_eraseIdx {places : List Nat} (nodup : places.Nodup) {position : Nat}
    (inside : position < places.length) :
    (places.eraseIdx position).toFinset = places.toFinset.erase places[position] := by
  ext place
  simp only [List.mem_toFinset, Finset.mem_erase]
  exact mem_eraseIdx_of_nodup nodup inside place

/-- **A linked group of the other places is a group of the system.** -/
theorem isGroup_of_build {places : List Nat} (nodup : places.Nodup) {position : Nat}
    (inside : position < places.length) {group : List Nat}
    (member : group ∈ Linked.build (throughKeys (allowedFor count (placeValue block components places[position]))
      count (placeValue block components)) (places.eraseIdx position)) :
    (absorptionSystem block canonical count components height).IsGroup places.toFinset places[position]
      group.toFinset := by
  set keys := throughKeys (allowedFor count (placeValue block components places[position])) count
    (placeValue block components)
  have grouping := Linked.build_grouping (keys := keys) (places.eraseIdx position)
  have relink : ∀ first last, Linked.LinkedIn keys group first last →
      (absorptionSystem block canonical count components height).LinkedIn places[position] group.toFinset first
        last := by
    intro first last linked
    induction linked with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step reached =>
        obtain ⟨inFirst, inSecond, shares⟩ := step
        exact reached.tail ⟨List.mem_toFinset.mpr inFirst, List.mem_toFinset.mpr inSecond,
          (linkFor_iff_shares _ _ _).mpr shares⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro place inGroup
    rw [← toFinset_eraseIdx nodup inside, List.mem_toFinset]
    exact grouping.mem_items member (List.mem_toFinset.mp inGroup)
  · obtain ⟨place, inGroup⟩ := List.exists_mem_of_ne_nil group (grouping.nonempty group member)
    exact ⟨place, List.mem_toFinset.mpr inGroup⟩
  · intro first inFirst second inSecond
    exact relink first second (grouping.linked group member first (List.mem_toFinset.mp inFirst) second
      (List.mem_toFinset.mp inSecond))
  · intro first inFirst second inSecond link
    rw [← toFinset_eraseIdx nodup inside, List.mem_toFinset] at inSecond
    have inGroup := List.mem_toFinset.mp inFirst
    exact List.mem_toFinset.mpr (grouping.closed member inGroup (Linked.LinkedIn.single
      (grouping.mem_items member inGroup) inSecond ((linkFor_iff_shares _ _ _).mp link)))

/-- **Erasing the first match of an image**: the first item whose image passes a test is erased with its image. -/
theorem erase_map_of_find? {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (image : α → β)
    (test : β → Bool) :
    ∀ {items : List α} {found : α}, items.find? (test ∘ image) = some found →
      (items.map image).erase (image found) = (items.erase found).map image
  | [], _, found => by simp at found
  | item :: items, chosen, found => by
      simp only [List.find?_cons, Function.comp_apply] at found
      by_cases passes : test (image item) = true
      · rw [passes] at found
        cases found
        simp
      · rw [Bool.not_eq_true] at passes
        rw [passes] at found
        have chosenPasses : test (image chosen) = true := by
          simpa using List.find?_some found
        have different : image item ≠ image chosen := fun equal => by
          rw [equal, chosenPasses] at passes
          cases passes
        have differentItem : item ≠ chosen := fun equal => different (equal ▸ rfl)
        rw [List.map_cons, List.erase_cons_tail (by simpa using different), List.erase_cons_tail
          (by simpa using differentItem), List.map_cons, erase_map_of_find? image test found]

/-- The places of a group read in increasing order are the group's places. -/
theorem sort_perm {group : List Nat} (nodup : group.Nodup) : (group.toFinset.sort (· ≤ ·)).Perm group :=
  (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) nodup).mpr fun place => by simp

/-- **The copy test does not read the order of a group's places**, for a canonical form blind to orders. -/
theorem copyTest_sort (blind : OrderBlind block canonical) {component : Pattern} {allowed : List Nat}
    {group : List Nat} (nodup : group.Nodup) :
    CopyTest block canonical count component
        (asGroup allowed count (placeValue block components) (group.toFinset.sort (· ≤ ·))) ↔
      CopyTest block canonical count component (asGroup allowed count (placeValue block components) group) := by
  have restrictionsSame : restrictionsOf allowed count (placeValue block components) (group.toFinset.sort (· ≤ ·)) =
      restrictionsOf allowed count (placeValue block components) group := by
    unfold restrictionsOf
    apply List.filter_congr
    intro index _
    exact List.Perm.any_eq (sort_perm nodup)
  have permuted := (sort_perm nodup).map (placeValue block components)
  unfold CopyTest asGroup
  rw [restrictionsSame, blind count _ _ _ permuted]
  simp only [permuted.mem_iff]

/-- A canonical form blind to orders is blind on every block. -/
theorem blindOn_of_orderBlind (blind : OrderBlind block canonical) : BlindOn block canonical count components :=
  fun _ _ _ _ _ nodup _ => copyTest_sort blind nodup


/-- The keys of the places other than a replicated one: the restrictions it does not mention that they use. -/
abbrev placeKeys (block : ReplicationBlock) (count : Nat) (components : List Pattern) (place : Nat) : Nat → List Nat :=
  throughKeys (allowedFor count (placeValue block components place)) count (placeValue block components)

theorem isReplicated_apply {label : String} {argument : Pattern} (isReplicate : label = block.replicate) :
    isReplicated block (.apply label [argument]) = true := by
  simp [isReplicated, isReplicate]

/-- A replicated component is a replication. -/
theorem replicated_shape {component : Pattern} (replicated : isReplicated block component = true) :
    ∃ argument, component = .apply block.replicate [argument] := by
  match component, replicated with
  | .apply label [argument], replicated =>
      simp only [isReplicated, beq_iff_eq] at replicated
      exact ⟨argument, by rw [replicated]⟩

/-- The components of linked groups read as groups, together. -/
theorem flatMap_asGroup (allowed : List Nat) (count : Nat) (value : Nat → Pattern) :
    ∀ (groups : List (List Nat)),
      (groups.map (asGroup allowed count value)).flatMap Group.components = groups.flatten.map value
  | [] => rfl
  | group :: groups => by
      simp only [List.map_cons, List.flatMap_cons, List.flatten_cons, List.map_append, flatMap_asGroup allowed
        count value groups]
      rfl

/-- **One absorption removes a copy group of the system**, and keeps the other places, its replicated one last. -/
theorem absorbOnce_step (blind : BlindOn block canonical count components) {places : List Nat}
    (nodup : places.Nodup) (inRange : ∀ place ∈ places, place < components.length)
    {next : Prenex}
    (absorbed : absorbOnce block canonical ⟨count, places.map (placeValue block components)⟩ = some next) :
    ∃ (position : Nat) (inside : position < places.length) (group : List Nat),
      group ∈ Linked.build (placeKeys block count components places[position]) (places.eraseIdx position) ∧
      (absorptionSystem block canonical count components height).IsCopy places.toFinset places[position]
        group.toFinset ∧
      next = ⟨count, (((Linked.build (placeKeys block count components places[position])
        (places.eraseIdx position)).erase group).flatten ++ [places[position]]).map
          (placeValue block components)⟩ := by
  unfold absorbOnce at absorbed
  obtain ⟨position, positionIn, found⟩ := List.exists_of_findSome?_eq_some absorbed
  have inside : position < places.length := by simpa using List.mem_range.mp positionIn
  simp only [List.getElem?_map, List.getElem?_eq_getElem inside, Option.map_some] at found
  split at found
  swap
  · cases found
  rename_i label argument isAt
  have componentIs : placeValue block components places[position] = .apply label [argument] :=
    Option.some.inj isAt
  split_ifs at found with isReplicate
  rw [List.eraseIdx_map, groupsThrough_map, List.find?_map] at found
  have allowedIs : ((List.range count).filter fun index => !mentions index (.apply label [argument])) =
      allowedFor count (placeValue block components places[position]) := by
    rw [componentIs]
    rfl
  rw [allowedIs] at found
  obtain ⟨groupValue, foundValue, rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨group, foundGroup, rfl⟩ := Option.map_eq_some_iff.mp foundValue
  have member := List.mem_of_find?_eq_some foundGroup
  have passes := List.find?_some foundGroup
  have grouping := Linked.build_grouping (keys := placeKeys block count components places[position])
    (places.eraseIdx position)
  have groupNodup := grouping.group_nodup (nodup.eraseIdx position) member
  have argumentIs : argumentOf? (placeValue block components places[position]) = argument := by
    rw [componentIs]
    rfl
  refine ⟨position, inside, group, member, ⟨List.mem_toFinset.mpr (List.getElem_mem inside), ?_,
    isGroup_of_build nodup inside member, ?_⟩, ?_⟩
  · show isReplicated block (placeValue block components places[position]) = true
    rw [componentIs]
    exact isReplicated_apply isReplicate
  · show CopyTest block canonical count (placeValue block components places[position])
      (asGroup (allowedFor count (placeValue block components places[position])) count (placeValue block components)
        (group.toFinset.sort (· ≤ ·)))
    have placeReplicated : isReplicated block (placeValue block components places[position]) = true := by
      rw [componentIs]
      exact isReplicated_apply isReplicate
    rw [blind places[position] group (inRange _ (List.getElem_mem inside)) placeReplicated
      (fun inGroup => ((mem_eraseIdx_of_nodup nodup inside _).mp (grouping.mem_items member inGroup)).1 rfl)
      groupNodup fun element inGroup =>
        inRange element (List.mem_of_mem_eraseIdx (grouping.mem_items member inGroup))]
    simp only [Function.comp_apply] at passes
    exact (copyTest_iff_bool block canonical count componentIs _).mp passes
  · rw [erase_map_of_find? (asGroup (allowedFor count (placeValue block components places[position])) count
      (placeValue block components)) _ foundGroup, flatMap_asGroup, List.map_append, List.map_singleton]
    simp only [placeKeys, componentIs]

/-- **One absorption finds nothing exactly when the system has no copy group.** -/
theorem absorbOnce_none (blind : BlindOn block canonical count components) {places : List Nat}
    (nodup : places.Nodup) (inRange : ∀ place ∈ places, place < components.length)
    (none : absorbOnce block canonical ⟨count, places.map (placeValue block components)⟩ = none) :
    ∀ place group, ¬ (absorptionSystem block canonical count components height).IsCopy places.toFinset place group := by
  classical
  intro place group isCopy
  obtain ⟨position, inside, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp isCopy.isLive)
  obtain ⟨argument, componentIs⟩ := replicated_shape isCopy.isReplicated
  obtain ⟨member, inGroup⟩ := isCopy.isGroup.nonempty
  have memberOther : member ∈ places.eraseIdx position := by
    rw [← List.mem_toFinset, toFinset_eraseIdx nodup inside]
    exact isCopy.isGroup.subset inGroup
  set keys := placeKeys block count components places[position]
  have grouping := Linked.build_grouping (keys := keys) (places.eraseIdx position)
  obtain ⟨linked, linkedMember, inLinked⟩ := grouping.exists_group memberOther
  have linkedGroup := isGroup_of_build (canonical := canonical) (height := height) nodup inside linkedMember
  have same : group = linked.toFinset := isCopy.isGroup.eq_of_mem linkedGroup inGroup (List.mem_toFinset.mpr inLinked)
  have linkedCopy : CopyTest block canonical count (placeValue block components places[position])
      (asGroup (allowedFor count (placeValue block components places[position])) count
        (placeValue block components) linked) := by
    rw [← blind places[position] linked (inRange _ (List.getElem_mem inside)) isCopy.isReplicated
      (fun inLinked' => ((mem_eraseIdx_of_nodup nodup inside _).mp (grouping.mem_items linkedMember inLinked')).1 rfl)
      (grouping.group_nodup (nodup.eraseIdx position) linkedMember)
      fun member inLinked => inRange member (List.mem_of_mem_eraseIdx (grouping.mem_items linkedMember inLinked))]
    have := isCopy.isCopy
    rw [same] at this
    exact this
  unfold absorbOnce at none
  rw [List.findSome?_eq_none_iff] at none
  have atPosition := none position (by simpa using inside)
  simp only [List.getElem?_map, List.getElem?_eq_getElem inside, Option.map_some, componentIs] at atPosition
  simp only [ite_true, Option.map_eq_none_iff, List.find?_eq_none] at atPosition
  rw [List.eraseIdx_map, groupsThrough_map] at atPosition
  have allowedIs : ((List.range count).filter fun index => !mentions index (.apply block.replicate [argument])) =
      allowedFor count (placeValue block components places[position]) := by
    rw [componentIs]
    rfl
  rw [allowedIs] at atPosition
  have rejected := atPosition _ (List.mem_map.mpr ⟨linked, linkedMember, rfl⟩)
  have argumentIs : argumentOf? (placeValue block components places[position]) = argument := by
    rw [componentIs]
    rfl
  exact rejected ((copyTest_iff_bool block canonical count componentIs _).mpr linkedCopy)

/-- The places left after removing a linked group are the other places without it, the replicated one last. -/
theorem places_after {places : List Nat} {position : Nat} (inside : position < places.length)
    {keys : Nat → List Nat} {group : List Nat} (member : group ∈ Linked.build keys (places.eraseIdx position)) :
    places.Perm (group ++ (((Linked.build keys (places.eraseIdx position)).erase group).flatten ++
      [places[position]])) := by
  have grouping := Linked.build_grouping (keys := keys) (places.eraseIdx position)
  have around : (places[position] :: places.eraseIdx position).Perm places := List.getElem_cons_eraseIdx_perm inside
  have regroup : (places.eraseIdx position).Perm (group ++ ((Linked.build keys (places.eraseIdx position)).erase
      group).flatten) :=
    grouping.perm.symm.trans (by simpa using (List.perm_cons_erase member).flatten)
  have moved := (List.perm_append_singleton places[position]
    (group ++ ((Linked.build keys (places.eraseIdx position)).erase group).flatten)).symm
  rw [← List.append_assoc]
  exact around.symm.trans ((regroup.cons _).trans moved)

/-- **Absorption in enough rounds removes copy groups until none is left.** -/
theorem absorbRounds_absorbs (blind : BlindOn block canonical count components) :
    ∀ (rounds : Nat) {places : List Nat}, places.Nodup → (∀ place ∈ places, place < components.length) →
      places.length ≤ rounds →
      ∃ final : List Nat, final.Nodup ∧
        (absorptionSystem block canonical count components height).Absorbs places.toFinset final.toFinset ∧
        absorbRounds block canonical rounds ⟨count, places.map (placeValue block components)⟩ =
          ⟨count, final.map (placeValue block components)⟩
  | 0, places, nodup, _, short => by
      have empty : places = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp short)
      subst empty
      refine ⟨[], nodup, .done fun place group isCopy => ?_, rfl⟩
      simpa using isCopy.isLive
  | rounds + 1, places, nodup, inRange, short => by
      classical
      cases absorbed : absorbOnce block canonical ⟨count, places.map (placeValue block components)⟩ with
      | none =>
          refine ⟨places, nodup, .done (absorbOnce_none blind nodup inRange absorbed), ?_⟩
          simp only [absorbRounds, absorbed]
      | some next =>
          obtain ⟨position, inside, group, member, isCopy, rfl⟩ :=
            absorbOnce_step (height := height) blind nodup inRange absorbed
          have split := places_after inside member
          set rest := ((Linked.build (placeKeys block count components places[position])
            (places.eraseIdx position)).erase group).flatten ++ [places[position]]
          have restNodup : rest.Nodup := (split.nodup_iff.mp nodup).of_append_right
          have groupNonempty : group ≠ [] := (Linked.build_grouping (keys := placeKeys block count components
            places[position]) (places.eraseIdx position)).nonempty group member
          have shorter : rest.length ≤ rounds := by
            have lengths := split.length_eq
            rw [List.length_append] at lengths
            have positive := List.length_pos_of_ne_nil groupNonempty
            omega
          have restRange : ∀ place ∈ rest, place < components.length := fun place inRest =>
            inRange place (split.symm.subset (List.mem_append_right _ inRest))
          obtain ⟨final, finalNodup, absorbs, reached⟩ := absorbRounds_absorbs blind rounds restNodup restRange
            shorter
          have restSet : rest.toFinset = places.toFinset \ group.toFinset := by
            ext place
            simp only [List.mem_toFinset, Finset.mem_sdiff]
            have disjoint := List.disjoint_of_nodup_append (split.nodup_iff.mp nodup)
            constructor
            · intro inRest
              exact ⟨split.symm.subset (List.mem_append_right _ inRest), fun inGroup => disjoint inGroup inRest⟩
            · rintro ⟨inPlaces, notGroup⟩
              rcases List.mem_append.mp (split.subset inPlaces) with inGroup | inRest
              · exact absurd inGroup notGroup
              · exact inRest
          rw [restSet] at absorbs
          refine ⟨final, finalNodup, .step isCopy absorbs, ?_⟩
          simp only [absorbRounds, absorbed]
          exact reached


/-- **Absorption keeps exactly the places outside every copy group**, under the laws of the system, and drops
the restrictions they no longer use. -/
theorem absorb_copies (blind : BlindOn block canonical count components)
    {places : List Nat}
    (laws : (absorptionSystem block canonical count components height).Laws places.toFinset)
    (nodup : places.Nodup) (inRange : ∀ place ∈ places, place < components.length) :
    ∃ final : List Nat, final.Nodup ∧
      final.toFinset = places.toFinset \ (absorptionSystem block canonical count components height).copies
        places.toFinset ∧
      absorb block canonical ⟨count, places.map (placeValue block components)⟩ =
        (Prenex.mk count (final.map (placeValue block components))).prune := by
  obtain ⟨final, finalNodup, absorbs, reached⟩ := absorbRounds_absorbs (height := height) blind
    (places.map (placeValue block components)).length nodup inRange (by simp)
  refine ⟨final, finalNodup, absorbs.eq laws (Finset.Subset.refl _), ?_⟩
  unfold absorb
  rw [reached]

end System

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
