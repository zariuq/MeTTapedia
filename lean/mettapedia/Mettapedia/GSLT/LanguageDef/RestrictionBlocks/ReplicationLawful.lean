import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationAlike

/-!
# The laws of a block's absorption system

Given the canonical form below a block's size and the laws of every lighter block, the block's copy test is blind to
the order of a group's places (`blindOn_of_lawful`): permuted groups have similar copies.

Unbinding a block's outermost restrictions (`opening`) keeps every group whose restrictions are among those still
bound a group (`IsGroup.opened`), with the same copy and argument (`copyOf_opened`, `groupIndex_opened`), so a copy
group stays one (`IsCopy.opened`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_apply freeIn_lambda freeIn_collection liftIndex)

variable {block : ReplicationBlock}

/-! ## Blind to orders -/

/-- **A block's copy test is blind to the order of a group's places**, given the canonical form below its size and
the laws of every lighter block. -/
theorem blindOn_of_lawful {count : Nat} {components : List Pattern}
    (atomic : ∀ component ∈ components, decompose block.toBlock component = Prenex.atom component) {bound : Nat}
    (below : Below block bound) (heavy : (Prenex.mk count components).mass ≤ bound)
    (lawful : ∀ form : Prenex, form.mass < bound → form.Atomic block.toBlock →
      (blockSystem block form).Laws (places form).toFinset ∧ BlindOn block (canonicalOf block) form.count form.components) :
    BlindOn block (canonicalOf block) count components := by
  intro place group placeRange replicated notIn nodup inRange
  set value := placeValue block components with valueIs
  have sorted := sort_perm nodup
  have restrictionsSame : restrictionsOf (allowedFor count (value place)) count value (group.toFinset.sort (· ≤ ·)) =
      restrictionsOf (allowedFor count (value place)) count value group := by
    unfold restrictionsOf
    exact List.filter_congr fun index _ => sorted.any_eq
  unfold CopyTest asGroup
  rw [restrictionsSame]
  set restrictions := restrictionsOf (allowedFor count (value place)) count value group with restrictionsIs
  -- the group's weight
  have fullNodup : (place :: group).Nodup := List.nodup_cons.mpr ⟨notIn, nodup⟩
  have fullRange : ∀ member ∈ place :: group, member < components.length := by
    intro member inList
    rcases List.mem_cons.mp inList with rfl | inGroup
    · exact placeRange
    · exact inRange member inGroup
  have weights : sizeList ((place :: group).map value) ≤ sizeList components := sizeList_places_le fullNodup fullRange
  simp only [List.map_cons, sizeList] at weights
  obtain ⟨argument, componentIs⟩ := replicated_shape replicated
  have componentSize : size (value place) = size argument + 1 := by rw [componentIs]; simp [size, sizeList]
  have positive := size_pos argument
  simp only [Prenex.mass] at heavy
  have copySame : canonicalOf block (copyOf block.toBlock count
        ⟨restrictions, (group.toFinset.sort (· ≤ ·)).map value⟩) =
      canonicalOf block (copyOf block.toBlock count ⟨restrictions, group.map value⟩) := by
    set copied := copyBlock count restrictions ((group.toFinset.sort (· ≤ ·)).map value) with copiedIs
    set copied' := copyBlock count restrictions (group.map value) with copied'Is
    have groupAtoms : ∀ member ∈ group.map value, decompose block.toBlock member = Prenex.atom member := by
      intro member inMembers
      obtain ⟨item, inItems, rfl⟩ := List.mem_map.mp inMembers
      exact atomic _ (placeValue_mem (inRange item inItems))
    have sortedAtoms : ∀ member ∈ (group.toFinset.sort (· ≤ ·)).map value,
        decompose block.toBlock member = Prenex.atom member := fun member inMembers =>
      groupAtoms member ((sorted.map value).subset inMembers)
    have atomicCopy : copied.Atomic block.toBlock := atomic_map_rename sortedAtoms _
    have atomicCopy' : copied'.Atomic block.toBlock := atomic_map_rename groupAtoms _
    have usedCopy : copied.Used := by
      have := copyBlock_used (allowed := allowedFor count (value place)) (count := count) (value := value)
        (items := group.toFinset.sort (· ≤ ·))
      rwa [restrictionsSame] at this
    have usedCopy' : copied'.Used := copyBlock_used
    have massCopy' : copied'.mass ≤ bound - 1 := by
      have := copyBlock_mass (allowed := allowedFor count (value place)) (count := count) (value := value)
        (items := group)
      rw [← restrictionsIs, ← copied'Is] at this
      omega
    have massCopy : copied.mass ≤ bound - 1 := by
      have massSame : copied.mass = copied'.mass := by
        rw [copiedIs, copied'Is]
        simp only [copyBlock, Prenex.mass, sizeList_map_rename, sizeList_perm (sorted.map value)]
      omega
    have similar : SimilarR block copied copied' := by
      refine ⟨rfl, List.range copied.count, copied.components, List.Perm.refl _, ?_, ?_⟩
      · have renameId : rename (Prenex.permute copied.count (List.range copied.count)) = (id : Pattern → Pattern) := by
          rw [permute_range]
          exact funext rename_id
        rw [renameId, List.map_id]
        exact List.forall₂_same.mpr fun component _ => AlikeR.refl component
      · rw [copiedIs, copied'Is]
        exact (sorted.map value).map _
    unfold canonicalOf
    rw [copyOf_eq_copyBlock, copyOf_eq_copyBlock]
    simp only
    rw [decompose_toPattern atomicCopy usedCopy, decompose_toPattern atomicCopy' usedCopy',
      normal_similar similar (below.mono (Nat.sub_le bound 1)) massCopy massCopy' atomicCopy atomicCopy'
        fun form small formAtomic => lawful form (by omega) formAtomic]
  refine and_congr (by rw [copySame]) (and_congr (by rw [copySame]) (and_congr ?_ ?_))
  · exact forall_congr' fun member => imp_congr_left (sorted.map value).mem_iff
  · simp only [(sorted.map value).mem_iff]

/-! ## Unbinding a block's outer restrictions -/

/-- Filters of ranges with the same members are equal. -/
theorem filter_range_eq {count count' : Nat} {first second : Nat → Bool}
    (same : ∀ index, (index < count ∧ first index = true) ↔ (index < count' ∧ second index = true)) :
    (List.range count).filter first = (List.range count').filter second := by
  have sortedFirst : ((List.range count).filter first).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.imp Nat.le_of_lt).filter _
  have sortedSecond : ((List.range count').filter second).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.imp Nat.le_of_lt).filter _
  refine List.Perm.eq_of_pairwise' sortedFirst sortedSecond ((List.perm_ext_iff_of_nodup
    (List.nodup_range.filter _) (List.nodup_range.filter _)).mpr fun index => ?_)
  simp only [List.mem_filter, List.mem_range]
  exact same index

theorem mem_restrictionsOf_iff {count : Nat} {value : Nat → Pattern} {component : Pattern} {items : List Nat}
    {index : Nat} :
    index ∈ restrictionsOf (allowedFor count component) count value items ↔
      index < count ∧ mentions index component = false ∧ ∃ item ∈ items, mentions index (value item) = true := by
  rw [mem_restrictionsOf]
  unfold throughKeys
  simp only [List.mem_filter, mem_usedRestrictions, allowedFor, List.contains_iff_mem, List.mem_range,
    Bool.not_eq_true']
  constructor
  · rintro ⟨item, inItems, ⟨below, mentioned⟩, -, notMentioned⟩
    exact ⟨below, notMentioned, item, inItems, mentioned⟩
  · rintro ⟨below, notMentioned, item, inItems, mentioned⟩
    exact ⟨item, inItems, ⟨below, mentioned⟩, below, notMentioned⟩

/-- **The restrictions outside a group, the block's outer ones unbound.** -/
theorem outsideOf_opened {count opened : Nat} {restrictions : List Nat} (fewer : opened ≤ count)
    (low : ∀ index ∈ restrictions, index < opened) :
    outsideOf count restrictions =
      outsideOf opened restrictions ++ (List.range (count - opened)).map (opened + ·) := by
  unfold outsideOf
  conv_lhs => rw [show count = opened + (count - opened) by omega, List.range_add]
  rw [List.filter_append]
  congr 1
  rw [List.filter_eq_self]
  intro index member
  obtain ⟨offset, _, rfl⟩ := List.mem_map.mp member
  have notIn : opened + offset ∉ restrictions := fun inside => by have := low _ inside; omega
  simpa [List.contains_iff_mem] using notIn

theorem idxOf_map_add_range {opened size offset : Nat} (below : offset < size) :
    ((List.range size).map (opened + ·)).idxOf (opened + offset) = offset := by
  have nodup : ((List.range size).map (opened + ·)).Nodup := List.nodup_range.map fun a b same => by omega
  have atOffset : ((List.range size).map (opened + ·))[offset]'(by simpa using below) = opened + offset := by
    simp
  rw [← atOffset, nodup.idxOf_getElem]

theorem idxOf_outsideOf_opened {count opened : Nat} {restrictions : List Nat} (fewer : opened ≤ count)
    (low : ∀ index ∈ restrictions, index < opened) {index : Nat} :
    (index < opened → index ∉ restrictions → (outsideOf count restrictions).idxOf index =
      (outsideOf opened restrictions).idxOf index) ∧
    (opened ≤ index → index < count → (outsideOf count restrictions).idxOf index =
      (outsideOf opened restrictions).length + (index - opened)) := by
  rw [outsideOf_opened fewer low, List.idxOf_append]
  constructor
  · intro below notMember
    rw [if_pos (mem_outsideOf.mpr ⟨below, notMember⟩)]
  · intro above below
    rw [if_neg fun member => by have := (mem_outsideOf.mp member).1; omega]
    have shifted := idxOf_map_add_range (opened := opened) (size := count - opened) (offset := index - opened)
      (by omega)
    rw [show opened + (index - opened) = index by omega] at shifted
    rw [shifted]
    omega

/-- **Unbinding outer restrictions no group restriction reaches keeps the copy.** -/
theorem permute_split_opened {count opened : Nat} {restrictions : List Nat} (fewer : opened ≤ count)
    (nodup : restrictions.Nodup) (low : ∀ index ∈ restrictions, index < opened) (index : Nat) :
    Prenex.permute opened (splitOrder opened (outsideOf opened restrictions) restrictions) index =
      Prenex.permute count (splitOrder count (outsideOf count restrictions) restrictions) index := by
  have openedLength := outsideOf_length nodup low
  obtain ⟨inner, outer⟩ := idxOf_outsideOf_opened (index := index) fewer low
  by_cases member : index ∈ restrictions
  · rw [permute_split_inside member (low index member), permute_split_inside member (by have := low index member; omega)]
  · by_cases below : index < opened
    · rw [permute_split_outside member below, permute_split_outside member (by omega), inner below member]
    · by_cases belowCount : index < count
      · have small := length_le_of_inside nodup low
        rw [permute_split_above (Nat.le_of_not_lt below), permute_split_outside member belowCount,
          outer (Nat.le_of_not_lt below) belowCount, openedLength]
        omega
      · rw [permute_split_above (Nat.le_of_not_lt below), permute_split_above (Nat.le_of_not_lt belowCount)]

theorem copyOf_opened {count opened : Nat} {restrictions : List Nat} (fewer : opened ≤ count)
    (nodup : restrictions.Nodup) (low : ∀ index ∈ restrictions, index < opened) (components : List Pattern) :
    copyOf block.toBlock opened ⟨restrictions, components⟩ = copyOf block.toBlock count ⟨restrictions, components⟩ := by
  have same : Prenex.permute opened (splitOrder opened (outsideOf opened restrictions) restrictions) =
      Prenex.permute count (splitOrder count (outsideOf count restrictions) restrictions) :=
    funext (permute_split_opened fewer nodup low)
  unfold copyOf
  simp only
  rw [same]

theorem groupIndex_opened {count opened : Nat} {restrictions : List Nat} (fewer : opened ≤ count)
    (nodup : restrictions.Nodup) (low : ∀ index ∈ restrictions, index < opened) {index : Nat}
    (outside : index < opened → index ∉ restrictions) :
    Prenex.groupIndex opened (outsideOf opened restrictions) index =
      Prenex.groupIndex count (outsideOf count restrictions) index := by
  have openedLength := outsideOf_length nodup low
  have countLength := outsideOf_length (count := count) nodup fun index member => by have := low index member; omega
  have small := length_le_of_inside nodup low
  obtain ⟨inner, outer⟩ := idxOf_outsideOf_opened (index := index) fewer low
  by_cases below : index < opened
  · rw [groupIndex_below below, groupIndex_below (by omega), inner below (outside below)]
  · by_cases belowCount : index < count
    · rw [groupIndex_above (Nat.le_of_not_lt below), groupIndex_below belowCount,
        outer (Nat.le_of_not_lt below) belowCount]
      omega
    · rw [groupIndex_above (Nat.le_of_not_lt below), groupIndex_above (Nat.le_of_not_lt belowCount), openedLength,
        countLength]
      omega

theorem restrictionsOf_opened {count opened : Nat} {value : Nat → Pattern} {component : Pattern} {items : List Nat}
    (fewer : opened ≤ count)
    (low : ∀ item ∈ items, ∀ index < count, mentions index (value item) = true → mentions index component = false →
      index < opened) :
    restrictionsOf (allowedFor opened component) opened value items =
      restrictionsOf (allowedFor count component) count value items := by
  have characterize : ∀ (bound : Nat) (index : Nat),
      (index < bound ∧ (items.any fun item =>
          (throughKeys (allowedFor bound component) bound value item).contains index) = true) ↔
        (index < bound ∧ mentions index component = false ∧ ∃ item ∈ items, mentions index (value item) = true) := by
    intro bound index
    have := mem_restrictionsOf_iff (count := bound) (value := value) (component := component) (items := items)
      (index := index)
    unfold restrictionsOf at this
    simpa only [List.mem_filter, List.mem_range] using this
  unfold restrictionsOf
  apply filter_range_eq
  intro index
  rw [characterize, characterize]
  constructor
  · rintro ⟨below, notMentioned, witness⟩
    exact ⟨by omega, notMentioned, witness⟩
  · rintro ⟨below, notMentioned, item, inItems, mentioned⟩
    exact ⟨low item inItems index below mentioned notMentioned, notMentioned, item, inItems, mentioned⟩

/-- **A group whose own restrictions stay bound stays a group** once the block's outer restrictions are unbound. -/
theorem isGroup_opened {count opened : Nat} {components : List Pattern} (fewer : opened ≤ count) {live : Finset Nat}
    {p : Nat} {group : Finset Nat} (isGroup : (blockSystem block ⟨count, components⟩).IsGroup live p group)
    (low : ∀ member ∈ group, ∀ restriction ∈ (blockSystem block ⟨count, components⟩).mentions member,
      restriction ∉ (blockSystem block ⟨count, components⟩).mentions p → restriction < opened) :
    (blockSystem block ⟨opened, components⟩).IsGroup live p group := by
  have openedMentions : ∀ {place restriction}, restriction ∈ (blockSystem block ⟨opened, components⟩).mentions place ↔
      restriction < opened ∧ restriction ∈ (blockSystem block ⟨count, components⟩).mentions place := by
    intro place restriction
    rw [mem_mentions, mem_mentions]
    exact ⟨fun ⟨below, mentioned⟩ => ⟨below, by simp only at below ⊢; omega, mentioned⟩,
      fun ⟨below, _, mentioned⟩ => ⟨below, mentioned⟩⟩
  refine ⟨isGroup.subset, isGroup.nonempty, fun first inFirst second inSecond => ?_, ?_⟩
  · have linked := isGroup.linked first inFirst second inSecond
    clear inSecond
    induction linked with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step reached =>
        obtain ⟨inMiddle, inLast, restriction, inMiddleMentions, inLastMentions, notP⟩ := step
        have below := low _ inMiddle restriction inMiddleMentions notP
        refine reached.tail ⟨inMiddle, inLast, restriction, openedMentions.mpr ⟨below, inMiddleMentions⟩,
          openedMentions.mpr ⟨below, inLastMentions⟩, fun inP => notP (openedMentions.mp inP).2⟩
  · intro first inFirst second inSecond link
    obtain ⟨restriction, inFirstMentions, inSecondMentions, notP⟩ := link
    obtain ⟨below, inFirstClosed⟩ := openedMentions.mp inFirstMentions
    refine isGroup.closed first inFirst second inSecond ⟨restriction, inFirstClosed,
      (openedMentions.mp inSecondMentions).2, fun inP => notP (openedMentions.mpr ⟨below, inP⟩)⟩

/-- **A copy group whose own restrictions stay bound stays a copy group** once the block's outer restrictions are
unbound. -/
theorem isCopy_opened {count opened : Nat} {components : List Pattern} (fewer : opened ≤ count) {live : Finset Nat}
    {p : Nat} {group : Finset Nat} (isCopy : (blockSystem block ⟨count, components⟩).IsCopy live p group)
    (low : ∀ member ∈ group, ∀ restriction ∈ (blockSystem block ⟨count, components⟩).mentions member,
      restriction ∉ (blockSystem block ⟨count, components⟩).mentions p → restriction < opened) :
    (blockSystem block ⟨opened, components⟩).IsCopy live p group := by
  refine ⟨isCopy.isLive, isCopy.isReplicated, isGroup_opened fewer isCopy.isGroup low, ?_⟩
  have test := isCopy.isCopy
  simp only [blockSystem, absorptionSystem] at test ⊢
  set value := placeValue block components with valueIs
  set items := group.sort (· ≤ ·)
  have lowItems : ∀ item ∈ items, ∀ index < count, mentions index (value item) = true →
      mentions index (value p) = false → index < opened := by
    intro item inItems index below mentioned notMentioned
    refine low item ((Finset.mem_sort _).mp inItems) index (mem_mentions.mpr ⟨below, mentioned⟩) fun inP => ?_
    rw [(mem_mentions.mp inP).2] at notMentioned
    cases notMentioned
  have restrictionsSame := restrictionsOf_opened (component := value p) fewer lowItems
  unfold CopyTest asGroup at test ⊢
  rw [restrictionsSame]
  set restrictions := restrictionsOf (allowedFor count (value p)) count value items with restrictionsIs
  have nodup : restrictions.Nodup := restrictionsOf_nodup _ _ _ _
  have restrictionsLow : ∀ index ∈ restrictions, index < opened := by
    intro index member
    obtain ⟨below, notMentioned, item, inItems, mentioned⟩ := mem_restrictionsOf_iff.mp member
    exact lowItems item inItems index below mentioned notMentioned
  obtain ⟨same, notReplicated, smaller, mentionedAll⟩ := test
  obtain ⟨argument, componentIs⟩ := replicated_shape isCopy.isReplicated
  have targetSame : rename (Prenex.groupIndex opened (outsideOf opened restrictions)) (argumentOf? (value p)) =
      rename (Prenex.groupIndex count (outsideOf count restrictions)) (argumentOf? (value p)) := by
    apply rename_congr
    intro index free
    refine groupIndex_opened fewer nodup restrictionsLow fun _ member => ?_
    obtain ⟨-, notMentioned, -⟩ := mem_restrictionsOf_iff.mp member
    have mentioned : mentions index (value p) = true := by
      have componentIs' : value p = .apply block.replicate [argument] := componentIs
      rw [componentIs'] at free ⊢
      exact (mentions_iff _ _).mpr (freeIn_apply.mpr ⟨argument, List.mem_singleton_self _, free⟩)
    rw [mentioned] at notMentioned
    cases notMentioned
  rw [copyOf_opened fewer nodup restrictionsLow, targetSame]
  exact ⟨same, notReplicated, smaller, fun index below mentioned => mentionedAll index (by omega) mentioned⟩

/-! ## Free names of a block's pattern -/

theorem freeIn_body {components : List Pattern} {index : Nat} :
    FreeIn index (Prenex.body block.toBlock components) ↔ ∃ component ∈ components, FreeIn index component := by
  match components with
  | [] =>
      simp only [Prenex.body, freeIn_apply, List.not_mem_nil, false_and, exists_false]
  | [component] =>
      simp only [Prenex.body, List.mem_singleton, exists_eq_left]
  | first :: second :: rest =>
      rw [show Prenex.body block.toBlock (first :: second :: rest) =
        .collection .hashBag (first :: second :: rest) none from rfl, freeIn_collection]

theorem freeIn_restricts {process : Pattern} : ∀ (count : Nat) {index : Nat},
    FreeIn index (Prenex.restricts block.toBlock count process) ↔ FreeIn (index + count) process
  | 0, _ => Iff.rfl
  | count + 1, index => by
      rw [Prenex.restricts_succ, freeIn_apply]
      simp only [List.mem_singleton, exists_eq_left, freeIn_lambda]
      rw [freeIn_restricts count]
      rw [show index + 1 + count = index + (count + 1) by omega]

theorem freeIn_toPattern {form : Prenex} {index : Nat} :
    FreeIn index (Prenex.toPattern block.toBlock form) ↔
      ∃ component ∈ form.components, FreeIn (index + form.count) component := by
  unfold Prenex.toPattern
  rw [freeIn_restricts, freeIn_body]

/-- **A copy group of the live components is one of fewer live components** holding it and its replicated
component. -/
theorem isCopy_restrict {system : CopyGroups.System Nat} {live live' : Finset Nat} {p : Nat} {group : Finset Nat}
    (isCopy : system.IsCopy live p group) (fewer : live' ⊆ live) (groupIn : group ⊆ live') (pIn : p ∈ live') :
    system.IsCopy live' p group := by
  refine ⟨pIn, isCopy.isReplicated, ⟨fun member inGroup => ?_, isCopy.isGroup.nonempty, isCopy.isGroup.linked,
    fun first inFirst second inSecond link => ?_⟩, isCopy.isCopy⟩
  · exact Finset.mem_erase.mpr ⟨fun same => isCopy.isGroup.not_mem (same ▸ inGroup), groupIn inGroup⟩
  · obtain ⟨different, inLive'⟩ := Finset.mem_erase.mp inSecond
    exact isCopy.isGroup.closed first inFirst second (Finset.mem_erase.mpr ⟨different, fewer inLive'⟩) link

/-- The places of a list of distinct places, by place. -/
theorem image_idxOf {kept : List Nat} (nodup : kept.Nodup) :
    kept.toFinset.image kept.idxOf = (List.range kept.length).toFinset := by
  ext position
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_range]
  constructor
  · rintro ⟨place, member, rfl⟩
    exact List.idxOf_lt_length_of_mem member
  · intro below
    exact ⟨kept[position], List.getElem_mem below, nodup.idxOf_getElem _ below⟩

/-- The order splitting a group's restrictions off keeps a block's restrictions. -/
theorem preserving_split {count : Nat} {restrictions : List Nat} (nodup : restrictions.Nodup)
    (inside : ∀ index ∈ restrictions, index < count) :
    Preserving count count (Prenex.permute count (splitOrder count (outsideOf count restrictions) restrictions)) := by
  have parts := outside_parts nodup inside
  refine ⟨permute_injective parts.splitOrder_perm, fun index below => ?_, fun index above => ?_⟩
  · rw [Prenex.permute, if_pos below, splitOrder_getD below]
    exact parts.splitPlace_lt below
  · rw [Prenex.permute, if_neg (by omega)]
    exact above

/-- **A copy group inside a group of another replicated component is a copy group of that group's copy.** -/
theorem isCopy_in_copyBlock {count : Nat} {components : List Pattern}
    (atomic : ∀ component ∈ components, decompose block.toBlock component = Prenex.atom component) {bound : Nat}
    (below : Below block bound) (heavy : (Prenex.mk count components).mass ≤ bound)
    (blind : BlindOn block (canonicalOf block) count components) {live : Finset Nat}
    (inside : live ⊆ (places ⟨count, components⟩).toFinset) {p q : Nat} {group outer : Finset Nat}
    (isCopy : (blockSystem block ⟨count, components⟩).IsCopy live p group) (qLive : q ∈ live)
    (outerGroup : (blockSystem block ⟨count, components⟩).IsGroup live q outer)
    (groupInside : group ⊆ outer) (pIn : p ∈ outer) :
    (blockSystem block (copyBlock count (restrictionsOf (allowedFor count (placeValue block components q)) count
        (placeValue block components) (outer.sort (· ≤ ·))) ((outer.sort (· ≤ ·)).map (placeValue block components)))).IsCopy
      (List.range (outer.sort (· ≤ ·)).length).toFinset ((outer.sort (· ≤ ·)).idxOf p)
      (group.image (outer.sort (· ≤ ·)).idxOf) := by
  have orderSet : (outer.sort (· ≤ ·)).toFinset = outer := Finset.sort_toFinset _ _
  have orderNodup : (outer.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  generalize orderIs : outer.sort (· ≤ ·) = order at orderSet orderNodup ⊢
  have outerLive : outer ⊆ live := fun member inOuter => (Finset.mem_erase.mp (outerGroup.subset inOuter)).2
  have orderLive : order.toFinset ⊆ live := orderSet ▸ outerLive
  have groupSub : group ⊆ order.toFinset := orderSet ▸ groupInside
  have pOrder : p ∈ order.toFinset := orderSet ▸ pIn
  have orderRange : ∀ place ∈ order, place < components.length := fun place member => by
    have := inside (orderLive (List.mem_toFinset.mpr member))
    simpa [places] using this
  -- the copy group among the group's places
  have isCopyOuter := isCopy_restrict isCopy orderLive groupSub pOrder
  have iso := restrictTo_iso (form := ⟨count, components⟩) blind orderRange
  have restricted := (iso.isCopy_iff pOrder groupSub).mpr isCopyOuter
  rw [image_idxOf orderNodup] at restricted
  -- reordered so that the group's restrictions come first
  have nodup : (restrictionsOf (allowedFor count (placeValue block components q)) count (placeValue block components)
      order).Nodup := restrictionsOf_nodup _ _ _ _
  have restrictionsInside : ∀ index ∈ restrictionsOf (allowedFor count (placeValue block components q)) count
      (placeValue block components) order, index < count := fun _ member => restrictionsOf_lt member
  have preserving := preserving_split nodup restrictionsInside
  have orderSmall : (restrictTo block ⟨count, components⟩ order).mass ≤ bound := by
    have weights := sizeList_places_le (block := block) orderNodup orderRange
    simp only [restrictTo, Prenex.mass] at heavy ⊢
    omega
  have orderAtomic : ∀ component ∈ (restrictTo block ⟨count, components⟩ order).components,
      decompose block.toBlock component = Prenex.atom component := by
    intro component member
    obtain ⟨place, inOrder, rfl⟩ := List.mem_map.mp member
    exact atomic _ (placeValue_mem (orderRange place inOrder))
  have iso' := rename_iso (block := block) preserving (below.mono orderSmall) orderAtomic
  have placesIs : (places (restrictTo block ⟨count, components⟩ order)).toFinset =
      (List.range order.length).toFinset := by
    simp [places, restrictTo]
  have pPlace : order.idxOf p ∈ (List.range order.length).toFinset :=
    List.mem_toFinset.mpr (List.mem_range.mpr (List.idxOf_lt_length_of_mem (List.mem_toFinset.mp pOrder)))
  have groupPlaces : group.image order.idxOf ⊆ (List.range order.length).toFinset := by
    intro position member
    obtain ⟨place, inGroup, rfl⟩ := Finset.mem_image.mp member
    exact List.mem_toFinset.mpr (List.mem_range.mpr (List.idxOf_lt_length_of_mem
      (List.mem_toFinset.mp (groupSub inGroup))))
  rw [← placesIs] at pPlace groupPlaces restricted
  have restricted' := (iso'.isCopy_iff pPlace groupPlaces).mpr restricted
  simp only [Finset.image_id, id] at restricted'
  have placesIs' : (places (⟨count, order.map (placeValue block components)⟩ : Prenex)).toFinset =
      (List.range order.length).toFinset := by
    simp [places]
  rw [placesIs'] at restricted'
  -- the restrictions outside the group's unbound
  refine isCopy_opened (count := count) (length_le_of_inside nodup restrictionsInside) restricted' ?_
  intro member inGroup restriction mentioned notMentioned
  obtain ⟨place, placeInGroup, rfl⟩ := Finset.mem_image.mp inGroup
  have placeOrder : place ∈ order.toFinset := groupSub placeInGroup
  have placePlace : order.idxOf place ∈ (places (restrictTo block ⟨count, components⟩ order)).toFinset := by
    rw [placesIs]
    exact List.mem_toFinset.mpr (List.mem_range.mpr (List.idxOf_lt_length_of_mem (List.mem_toFinset.mp placeOrder)))
  have mentionsIs := iso'.mentions (order.idxOf place) placePlace
  have mentionsP := iso'.mentions (order.idxOf p) pPlace
  simp only [id] at mentionsIs mentionsP
  rw [mentionsIs] at mentioned
  rw [mentionsP] at notMentioned
  obtain ⟨original, inRestricted, rfl⟩ := Finset.mem_image.mp mentioned
  have notP : original ∉ (blockSystem block (restrictTo block ⟨count, components⟩ order)).mentions (order.idxOf p) :=
    fun inP => notMentioned (Finset.mem_image_of_mem _ inP)
  have equationPlace := iso.mentions place placeOrder
  have equationP := iso.mentions p pOrder
  rw [Finset.image_id] at equationPlace equationP
  replace inRestricted : original ∈ (blockSystem block ⟨count, components⟩).mentions place := by
    rw [← equationPlace]
    exact inRestricted
  replace notP : original ∉ (blockSystem block ⟨count, components⟩).mentions p := by
    rw [← equationP]
    exact notP
  obtain ⟨originalBelow, mentionedHere⟩ := mem_mentions.mp inRestricted
  have notMentionedQ : mentions original (placeValue block components q) = false := by
    cases holds : mentions original (placeValue block components q) with
    | false => rfl
    | true =>
        have qp : q ≠ p := fun same => outerGroup.not_mem (same ▸ pIn)
        have qInGroup := isCopy.isGroup.closed place placeInGroup q (Finset.mem_erase.mpr ⟨qp, qLive⟩)
          ⟨original, inRestricted, mem_mentions.mpr ⟨originalBelow, holds⟩, notP⟩
        exact absurd (groupInside qInGroup) outerGroup.not_mem
  have inRestrictions : original ∈ restrictionsOf (allowedFor count (placeValue block components q)) count
      (placeValue block components) order :=
    mem_restrictionsOf_iff.mpr ⟨originalBelow, notMentionedQ, place, List.mem_toFinset.mp placeOrder, mentionedHere⟩
  rw [permute_split_inside inRestrictions originalBelow]
  exact List.idxOf_lt_length_of_mem inRestrictions

/-! ## A group's copy without a copy inside it -/

/-- **The free names of a group's copy without a copy inside it**, read as the whole group's copy reads them: an
outside restriction by its place among those outside the whole group, a name outside the block shifted. -/
def innerRelabel (count : Nat) (first second : List Nat) (index : Nat) : Nat :=
  if index < count - second.length then (outsideOf count first).idxOf ((outsideOf count second).getD index 0)
  else index + second.length - first.length

/-- **The restrictions of a group's copy without a copy inside it**, among those of the whole group's copy, and
its other names shifted past them. -/
def innerShift (first second : List Nat) (index : Nat) : Nat :=
  if index < second.length then first.idxOf (second.getD index 0) else index + first.length - second.length

section Inner

variable {count : Nat} {first second : List Nat}

/-- The restrictions of a group without a copy inside it, among those of the whole group. -/
structure InnerParts (count : Nat) (first second : List Nat) : Prop where
  firstNodup : first.Nodup
  secondNodup : second.Nodup
  firstInside : ∀ index ∈ first, index < count
  secondInside : ∀ index ∈ second, index < count
  sub : ∀ index ∈ second, index ∈ first

theorem InnerParts.length_le (parts : InnerParts count first second) : second.length ≤ first.length := by
  have subperm : second.Subperm first := parts.secondNodup.subperm parts.sub
  exact subperm.length_le

theorem InnerParts.innerShift_preserving (parts : InnerParts count first second) :
    Preserving second.length first.length (innerShift first second) := by
  have lengths := parts.length_le
  have firstAt : ∀ index < second.length, first.idxOf (second.getD index 0) < first.length := fun index below => by
    rw [List.getD_eq_getElem _ _ below]
    exact List.idxOf_lt_length_of_mem (parts.sub _ (List.getElem_mem below))
  refine ⟨fun a b same => ?_, fun index below => ?_, fun index above => ?_⟩
  · unfold innerShift at same
    by_cases aBelow : a < second.length <;> by_cases bBelow : b < second.length
    · rw [if_pos aBelow, if_pos bBelow] at same
      rw [List.getD_eq_getElem _ _ aBelow, List.getD_eq_getElem _ _ bBelow] at same
      have equal := SplitParts.eq_of_idxOf_eq (parts.sub _ (List.getElem_mem aBelow))
        (parts.sub _ (List.getElem_mem bBelow)) same
      exact (List.Nodup.getElem_inj_iff parts.secondNodup).mp equal
    · rw [if_pos aBelow, if_neg bBelow] at same
      have := firstAt a aBelow
      omega
    · rw [if_neg aBelow, if_pos bBelow] at same
      have := firstAt b bBelow
      omega
    · rw [if_neg aBelow, if_neg bBelow] at same
      omega
  · unfold innerShift
    rw [if_pos below]
    exact firstAt index below
  · unfold innerShift
    rw [if_neg (by omega)]
    omega

theorem InnerParts.pruneRelabel_id (parts : InnerParts count first second) (index : Nat) :
    pruneRelabel second.length first.length (innerShift first second) index = index := by
  have lengths := parts.length_le
  unfold pruneRelabel innerShift
  rw [if_neg (by omega)]
  omega

/-- **Every name of a component without the copy**: read in the smaller group's copy, renamed outside and shifted,
it is read as in the whole group's copy. -/
theorem InnerParts.split_comp (parts : InnerParts count first second) {index : Nat}
    (outside : index < count → index ∉ second → index ∉ first) :
    innerShift first second (liftIndex second.length (innerRelabel count first second)
        (Prenex.permute count (splitOrder count (outsideOf count second) second) index)) =
      Prenex.permute count (splitOrder count (outsideOf count first) first) index := by
  have lengths := parts.length_le
  have firstSmall := length_le_of_inside parts.firstNodup parts.firstInside
  have secondOutside := outsideOf_length parts.secondNodup parts.secondInside
  have firstOutside := outsideOf_length parts.firstNodup parts.firstInside
  by_cases inside : index < count
  · by_cases member : index ∈ second
    · have placed := List.idxOf_lt_length_of_mem member
      rw [permute_split_inside member inside, permute_split_inside (parts.sub _ member) inside, liftIndex,
        if_pos placed, innerShift, if_pos placed, List.getD_eq_getElem _ _ placed, List.getElem_idxOf]
    · have notFirst := outside inside member
      have outsideMember : index ∈ outsideOf count second := mem_outsideOf.mpr ⟨inside, member⟩
      have placed := List.idxOf_lt_length_of_mem outsideMember
      rw [permute_split_outside member inside, permute_split_outside notFirst inside, liftIndex,
        if_neg (by omega), Nat.add_sub_cancel_left, innerRelabel, if_pos (by omega),
        List.getD_eq_getElem _ _ placed, List.getElem_idxOf, innerShift, if_neg (by omega)]
      omega
  · have above : count ≤ index := Nat.le_of_not_lt inside
    rw [permute_split_above above, permute_split_above above, liftIndex, if_neg (by omega), innerRelabel,
      if_neg (by omega), innerShift, if_neg (by omega)]
    omega

/-- **The names a replicated argument reads**, renumbered for the smaller group's copy and read as the whole
group's copy reads them. -/
theorem InnerParts.groupIndex_comp (parts : InnerParts count first second) {index : Nat}
    (outside : index < count → index ∉ first ∧ index ∉ second) :
    innerRelabel count first second (Prenex.groupIndex count (outsideOf count second) index) =
      Prenex.groupIndex count (outsideOf count first) index := by
  have lengths := parts.length_le
  have firstSmall := length_le_of_inside parts.firstNodup parts.firstInside
  have secondOutside := outsideOf_length parts.secondNodup parts.secondInside
  have firstOutside := outsideOf_length parts.firstNodup parts.firstInside
  by_cases inside : index < count
  · obtain ⟨notFirst, notSecond⟩ := outside inside
    have outsideMember : index ∈ outsideOf count second := mem_outsideOf.mpr ⟨inside, notSecond⟩
    have placed := List.idxOf_lt_length_of_mem outsideMember
    rw [groupIndex_below inside, groupIndex_below inside, innerRelabel, if_pos (by omega),
      List.getD_eq_getElem _ _ placed, List.getElem_idxOf]
  · have above : count ≤ index := Nat.le_of_not_lt inside
    rw [groupIndex_above above, groupIndex_above above, secondOutside, firstOutside, innerRelabel, if_neg (by omega)]
    omega

/-- The renaming of free names is injective on the names that are not the whole group's own restrictions. -/
theorem InnerParts.innerRelabel_injOn (parts : InnerParts count first second) {a b : Nat}
    (aOutside : a < count - second.length → (outsideOf count second).getD a 0 ∉ first)
    (bOutside : b < count - second.length → (outsideOf count second).getD b 0 ∉ first)
    (same : innerRelabel count first second a = innerRelabel count first second b) : a = b := by
  have lengths := parts.length_le
  have firstSmall := length_le_of_inside parts.firstNodup parts.firstInside
  have secondOutside := outsideOf_length parts.secondNodup parts.secondInside
  have firstOutside := outsideOf_length parts.firstNodup parts.firstInside
  have memberOf : ∀ position < count - second.length,
      (outsideOf count second).getD position 0 ∉ first →
        (outsideOf count second).getD position 0 ∈ outsideOf count first := by
    intro position below notFirst
    have inRange : position < (outsideOf count second).length := by omega
    rw [List.getD_eq_getElem _ _ inRange]
    rw [List.getD_eq_getElem _ _ inRange] at notFirst
    exact mem_outsideOf.mpr ⟨(mem_outsideOf.mp (List.getElem_mem inRange)).1, notFirst⟩
  unfold innerRelabel at same
  by_cases aBelow : a < count - second.length <;> by_cases bBelow : b < count - second.length
  · rw [if_pos aBelow, if_pos bBelow] at same
    have equal := SplitParts.eq_of_idxOf_eq (memberOf a aBelow (aOutside aBelow)) (memberOf b bBelow (bOutside bBelow))
      same
    have aIn : a < (outsideOf count second).length := by omega
    have bIn : b < (outsideOf count second).length := by omega
    rw [List.getD_eq_getElem _ _ aIn, List.getD_eq_getElem _ _ bIn] at equal
    exact (List.Nodup.getElem_inj_iff ((List.nodup_range).filter _)).mp equal
  · rw [if_pos aBelow, if_neg bBelow] at same
    have := List.idxOf_lt_length_of_mem (memberOf a aBelow (aOutside aBelow))
    omega
  · rw [if_neg aBelow, if_pos bBelow] at same
    have := List.idxOf_lt_length_of_mem (memberOf b bBelow (bOutside bBelow))
    omega
  · rw [if_neg aBelow, if_neg bBelow] at same
    omega

end Inner

/-! ## The inner law -/

theorem placeValue_map_idxOf {order : List Nat} {value : Nat → Pattern} {relabel : Nat → Nat} {place : Nat}
    (member : place ∈ order) :
    placeValue block ((order.map value).map (rename relabel)) (order.idxOf place) = rename relabel (value place) := by
  have below := List.idxOf_lt_length_of_mem member
  unfold placeValue
  rw [List.getD_eq_getElem _ _ (by simpa using below)]
  simp

theorem placeValue_map_idxOf' {order : List Nat} {value : Nat → Pattern} {place : Nat} (member : place ∈ order) :
    placeValue block (order.map value) (order.idxOf place) = value place := by
  have below := List.idxOf_lt_length_of_mem member
  unfold placeValue
  rw [List.getD_eq_getElem _ _ (by simpa using below)]
  simp

/-- **Absorbing a copy inside a group keeps the group a copy or not**, given the canonical form below the block's
size and the laws of every lighter block. -/
theorem inner_of_lawful {count : Nat} {components : List Pattern}
    (atomic : ∀ component ∈ components, decompose block.toBlock component = Prenex.atom component) {bound : Nat}
    (below : Below block bound) (heavy : (Prenex.mk count components).mass ≤ bound)
    (lawful : ∀ form : Prenex, form.mass < bound → form.Atomic block.toBlock →
      (blockSystem block form).Laws (places form).toFinset ∧ BlindOn block (canonicalOf block) form.count form.components)
    (blind : BlindOn block (canonicalOf block) count components) {live : Finset Nat}
    (inside : live ⊆ (places ⟨count, components⟩).toFinset) {p q : Nat} {group outer : Finset Nat}
    (isCopy : (blockSystem block ⟨count, components⟩).IsCopy live p group) (qLive : q ∈ live)
    (qReplicated : (blockSystem block ⟨count, components⟩).replicated q)
    (outerGroup : (blockSystem block ⟨count, components⟩).IsGroup live q outer)
    (groupInside : group ⊆ outer) (pIn : p ∈ outer) :
    (blockSystem block ⟨count, components⟩).copy outer q ↔
      (blockSystem block ⟨count, components⟩).copy (outer \ group) q := by
  have copyInside := isCopy_in_copyBlock atomic below heavy blind inside isCopy qLive outerGroup groupInside pIn
  have pReplicated : isReplicated block (placeValue block components p) = true := isCopy.isReplicated
  have pTest := isCopy.isCopy
  simp only [blockSystem, absorptionSystem] at pTest qReplicated ⊢
  have outerLive : outer ⊆ live := fun member inOuter => (Finset.mem_erase.mp (outerGroup.subset inOuter)).2
  have qOuter : q ∉ outer := outerGroup.not_mem
  have pGroup : p ∉ group := isCopy.isGroup.not_mem
  have orderSet : (outer.sort (· ≤ ·)).toFinset = outer := Finset.sort_toFinset _ _
  have orderNodup : (outer.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have restSet : ((outer \ group).sort (· ≤ ·)).toFinset = outer \ group := Finset.sort_toFinset _ _
  have restNodup : ((outer \ group).sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  generalize orderIs : outer.sort (· ≤ ·) = order at copyInside orderSet orderNodup ⊢
  generalize restIs : (outer \ group).sort (· ≤ ·) = rest at restSet restNodup ⊢
  have memOrder : ∀ {place}, place ∈ order ↔ place ∈ outer := fun {place} => by
    rw [← List.mem_toFinset, orderSet]
  have memRest : ∀ {place}, place ∈ rest ↔ place ∈ outer ∧ place ∉ group := fun {place} => by
    rw [← List.mem_toFinset, restSet, Finset.mem_sdiff]
  have orderRange : ∀ place ∈ order, place < components.length := fun place member => by
    have := inside (outerLive (memOrder.mp member))
    simpa [places] using this
  have qRange : q < components.length := by
    have := inside qLive
    simpa [places] using this
  have restOrder : ∀ place ∈ rest, place ∈ order := fun place member => memOrder.mpr (memRest.mp member).1
  have pRest : p ∈ rest := memRest.mpr ⟨pIn, pGroup⟩
  obtain ⟨argument, qIs⟩ := replicated_shape qReplicated
  set value := placeValue block components with valueIs
  -- weights
  have orderWeights : sizeList ((q :: order).map value) ≤ sizeList components :=
    sizeList_places_le (List.nodup_cons.mpr ⟨fun member => qOuter (memOrder.mp member), orderNodup⟩)
      fun place member => by
        rcases List.mem_cons.mp member with rfl | inOrder
        · exact qRange
        · exact orderRange place inOrder
  have restWeights : sizeList ((q :: rest).map value) ≤ sizeList components :=
    sizeList_places_le (List.nodup_cons.mpr ⟨fun member => qOuter (memRest.mp member).1, restNodup⟩)
      fun place member => by
        rcases List.mem_cons.mp member with rfl | inRest
        · exact qRange
        · exact orderRange place (restOrder place inRest)
  simp only [List.map_cons, sizeList] at orderWeights restWeights
  have qSize : size (value q) = size argument + 1 := by rw [qIs]; simp [size, sizeList]
  have argumentPositive := size_pos argument
  simp only [Prenex.mass] at heavy
  -- the restrictions of the two groups
  set first := restrictionsOf (allowedFor count (value q)) count value order with firstIs
  set second := restrictionsOf (allowedFor count (value q)) count value rest with secondIs
  have parts : InnerParts count first second := by
    refine ⟨restrictionsOf_nodup _ _ _ _, restrictionsOf_nodup _ _ _ _, fun _ member => restrictionsOf_lt member,
      fun _ member => restrictionsOf_lt member, fun index member => ?_⟩
    obtain ⟨below', notMentioned, place, inRest, mentioned⟩ := mem_restrictionsOf_iff.mp member
    exact mem_restrictionsOf_iff.mpr ⟨below', notMentioned, place, restOrder place inRest, mentioned⟩
  -- a name of a component without the copy, not a restriction of the smaller group, is none of the whole group's
  have restOutside : ∀ place ∈ rest, ∀ index, FreeIn index (value place) → index < count → index ∉ second →
      index ∉ first := by
    intro place inRest index free below' notSecond inFirst
    obtain ⟨-, notMentioned, -⟩ := mem_restrictionsOf_iff.mp inFirst
    exact notSecond (mem_restrictionsOf_iff.mpr ⟨below', notMentioned, place, inRest, (mentions_iff _ _).mpr free⟩)
  have argumentOutside : ∀ index, FreeIn index argument → index < count → index ∉ first ∧ index ∉ second := by
    intro index free _
    have mentioned : mentions index (value q) = true := by
      rw [qIs]
      exact (mentions_iff _ _).mpr (freeIn_apply.mpr ⟨argument, List.mem_singleton_self _, free⟩)
    constructor
    · intro inFirst
      obtain ⟨-, notMentioned, -⟩ := mem_restrictionsOf_iff.mp inFirst
      rw [mentioned] at notMentioned
      cases notMentioned
    · intro inSecond
      obtain ⟨-, notMentioned, -⟩ := mem_restrictionsOf_iff.mp inSecond
      rw [mentioned] at notMentioned
      cases notMentioned
  -- the copies, as blocks
  set whole := copyBlock count first (order.map value) with wholeIs
  set smaller := copyBlock count second (rest.map value) with smallerIs
  have orderAtoms : ∀ member ∈ order.map value, decompose block.toBlock member = Prenex.atom member := by
    intro member inMembers
    obtain ⟨place, inOrder, rfl⟩ := List.mem_map.mp inMembers
    exact atomic _ (placeValue_mem (orderRange place inOrder))
  have restAtoms : ∀ member ∈ rest.map value, decompose block.toBlock member = Prenex.atom member :=
    fun member inMembers => by
      obtain ⟨place, inRest, rfl⟩ := List.mem_map.mp inMembers
      exact orderAtoms _ (List.mem_map_of_mem (restOrder place inRest))
  have wholeAtomic : whole.Atomic block.toBlock := atomic_map_rename orderAtoms _
  have smallerAtomic : smaller.Atomic block.toBlock := atomic_map_rename restAtoms _
  have wholeUsed : whole.Used := copyBlock_used
  have smallerUsed : smaller.Used := copyBlock_used
  have wholeMass : whole.mass < bound := by
    have := copyBlock_mass (allowed := allowedFor count (value q)) (count := count) (value := value) (items := order)
    rw [← firstIs, ← wholeIs] at this
    omega
  have smallerMass : smaller.mass < bound := by
    have := copyBlock_mass (allowed := allowedFor count (value q)) (count := count) (value := value) (items := rest)
    rw [← secondIs, ← smallerIs] at this
    omega
  -- the whole group's copy holds the copy group, and without it
  have placesWhole : (places whole).toFinset = (List.range order.length).toFinset := by
    simp [places, wholeIs, copyBlock]
  obtain ⟨wholeLaws, wholeBlind⟩ := lawful whole wholeMass wholeAtomic
  set kept := rest.map order.idxOf with keptIs
  have keptNodup : kept.Nodup := restNodup.map_on fun a aIn b bIn same =>
    SplitParts.eq_of_idxOf_eq (restOrder a aIn) (restOrder b bIn) same
  have keptInside : ∀ position ∈ kept, position < whole.components.length := by
    intro position member
    obtain ⟨place, inRest, rfl⟩ := List.mem_map.mp member
    simp only [wholeIs, copyBlock, List.length_map]
    exact List.idxOf_lt_length_of_mem (restOrder place inRest)
  have keptSet : kept.toFinset = (places whole).toFinset \ group.image order.idxOf := by
    rw [placesWhole]
    ext position
    simp only [List.mem_toFinset, Finset.mem_sdiff, Finset.mem_image, List.mem_range, keptIs, List.mem_map]
    constructor
    · rintro ⟨place, inRest, rfl⟩
      refine ⟨List.idxOf_lt_length_of_mem (restOrder place inRest), ?_⟩
      rintro ⟨other, inGroup, same⟩
      have otherOrder : other ∈ order := memOrder.mpr (groupInside inGroup)
      have equal := SplitParts.eq_of_idxOf_eq otherOrder (restOrder place inRest) same
      exact (memRest.mp inRest).2 (equal ▸ inGroup)
    · rintro ⟨below', notGroup⟩
      refine ⟨order[position], memRest.mpr ⟨memOrder.mp (List.getElem_mem below'), fun inGroup =>
        notGroup ⟨order[position], inGroup, orderNodup.idxOf_getElem _ below'⟩⟩, orderNodup.idxOf_getElem _ below'⟩
  have removes : (blockSystem block whole).Removes (places whole).toFinset kept.toFinset := by
    rw [keptSet]
    refine .step (p := order.idxOf p) ?_ .refl
    rw [placesWhole]
    exact copyInside
  have restricted := normal_restrict wholeLaws wholeBlind keptNodup keptInside removes
  set split := Prenex.permute count (splitOrder count (outsideOf count first) first) with splitIs
  have restrictedIs : restrictTo block whole kept = ⟨first.length, (rest.map value).map (rename split)⟩ := by
    show (⟨first.length, (rest.map order.idxOf).map (placeValue block ((order.map value).map (rename split)))⟩ :
      Prenex) = _
    congr 1
    simp only [List.map_map]
    exact List.map_congr_left fun place inRest => by
      simp only [Function.comp_apply]
      exact placeValue_map_idxOf' (restOrder place inRest)
  -- the smaller group's copy, renamed outside and shifted, is the whole group's copy without the copy group
  set relabel := innerRelabel count first second with relabelIs
  set split' := Prenex.permute count (splitOrder count (outsideOf count second) second) with split'Is
  have pointwise : ∀ place ∈ rest, rename split (value place) =
      rename (innerShift first second) (rename (liftIndex second.length relabel) (rename split' (value place))) := by
    intro place inRest
    rw [rename_comp, rename_comp]
    apply rename_congr
    intro index free
    simp only [Function.comp_apply]
    exact (parts.split_comp fun below' notSecond => restOutside place inRest index free below' notSecond).symm
  have outerAtomic : (smaller.renameOuter relabel).Atomic block.toBlock := atomic_map_rename smallerAtomic _
  have outerMass : (smaller.renameOuter relabel).mass < bound := by
    have same : (smaller.renameOuter relabel).mass = smaller.mass := by
      simp only [Prenex.renameOuter, Prenex.mass, sizeList_map_rename]
    omega
  obtain ⟨outerLaws, outerBlind⟩ := lawful _ outerMass outerAtomic
  have outerCount : (smaller.renameOuter relabel).count = second.length := rfl
  have outerSmall : (Prenex.mk second.length (smaller.renameOuter relabel).components).mass ≤ bound := by
    have := outerMass
    simp only [Prenex.mass] at this ⊢
    rw [outerCount] at this
    omega
  obtain ⟨_, _, _, normalOuter, normalShifted⟩ := normal_rename (count := second.length) (count' := first.length)
    parts.innerShift_preserving (components := (smaller.renameOuter relabel).components)
    (below.mono outerSmall) outerAtomic outerLaws outerBlind
  have shifted : (⟨first.length, (rest.map value).map (rename split)⟩ : Prenex) =
      ⟨first.length, (smaller.renameOuter relabel).components.map (rename (innerShift first second))⟩ := by
    simp only [Prenex.renameOuter, smallerIs, copyBlock, List.map_map, Prenex.mk.injEq, true_and]
    exact List.map_congr_left fun place inRest => pointwise place inRest
  have normalSame : normal block whole = normal block (smaller.renameOuter relabel) := by
    rw [← restricted, restrictedIs, shifted, normalShifted, renameOuter_of_id parts.pruneRelabel_id, ← normalOuter]
    rfl
  have copySame : canonicalOf block (copyOf block.toBlock count ⟨first, order.map value⟩) =
      canonicalOf block (rename relabel (copyOf block.toBlock count ⟨second, rest.map value⟩)) := by
    unfold canonicalOf
    rw [copyOf_eq_copyBlock, copyOf_eq_copyBlock, decompose_renameOuter]
    simp only
    rw [← wholeIs, ← smallerIs, decompose_toPattern wholeAtomic wholeUsed, decompose_toPattern smallerAtomic smallerUsed,
      normalSame]
  -- an injective renaming agreeing on the names the smaller copy and the replicated argument read
  have secondSmall := length_le_of_inside parts.secondNodup parts.secondInside
  have secondOutsideLength := outsideOf_length parts.secondNodup parts.secondInside
  obtain ⟨relabel', injective, agree⟩ := exists_injective_on
    [copyOf block.toBlock count ⟨second, rest.map value⟩,
      rename (Prenex.groupIndex count (outsideOf count second)) argument]
    relabel (fun index => index < count - second.length → (outsideOf count second).getD index 0 ∉ first)
    (by
      intro pattern member index free below'
      rcases List.mem_cons.mp member with rfl | inRest
      · rw [copyOf_eq_copyBlock, freeIn_toPattern] at free
        obtain ⟨component, inComponents, free'⟩ := free
        simp only [copyBlock, List.map_map, List.mem_map, Function.comp_apply] at inComponents
        obtain ⟨place, inRestPlaces, rfl⟩ := inComponents
        rw [freeIn_rename] at free'
        obtain ⟨original, freeOriginal, sent⟩ := free'
        simp only [copyBlock] at sent
        by_cases originalBelow : original < count
        · by_cases inSecond : original ∈ second
          · rw [permute_split_inside inSecond originalBelow] at sent
            have := List.idxOf_lt_length_of_mem inSecond
            omega
          · rw [permute_split_outside inSecond originalBelow] at sent
            have placed : (outsideOf count second).idxOf original = index := by omega
            have outsideMember : original ∈ outsideOf count second := mem_outsideOf.mpr ⟨originalBelow, inSecond⟩
            have atIndex : (outsideOf count second).getD index 0 = original := by
              rw [← placed, List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem outsideMember), List.getElem_idxOf]
            rw [atIndex]
            exact restOutside place inRestPlaces original freeOriginal originalBelow inSecond
        · rw [permute_split_above (Nat.le_of_not_lt originalBelow)] at sent
          omega
      · rw [List.mem_singleton] at inRest
        subst inRest
        rw [freeIn_rename] at free
        obtain ⟨original, freeOriginal, sent⟩ := free
        by_cases originalBelow : original < count
        · obtain ⟨notFirst, notSecond⟩ := argumentOutside original freeOriginal originalBelow
          rw [groupIndex_below originalBelow] at sent
          have outsideMember : original ∈ outsideOf count second := mem_outsideOf.mpr ⟨originalBelow, notSecond⟩
          have atIndex : (outsideOf count second).getD index 0 = original := by
            rw [← sent, List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem outsideMember), List.getElem_idxOf]
          rw [atIndex]
          exact notFirst
        · rw [groupIndex_above (Nat.le_of_not_lt originalBelow), secondOutsideLength] at sent
          omega)
    fun a b aIn bIn same => parts.innerRelabel_injOn aIn bIn same
  have copySame' : canonicalOf block (copyOf block.toBlock count ⟨first, order.map value⟩) =
      canonicalOf block (rename relabel' (copyOf block.toBlock count ⟨second, rest.map value⟩)) := by
    rw [copySame, agree _ List.mem_cons_self]
  have targetSame : rename (Prenex.groupIndex count (outsideOf count first)) argument =
      rename relabel' (rename (Prenex.groupIndex count (outsideOf count second)) argument) := by
    rw [agree _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), rename_comp]
    apply rename_congr
    intro index free
    simp only [Function.comp_apply]
    exact (parts.groupIndex_comp fun below' => argumentOutside index free below').symm
  have copySmall : size (copyOf block.toBlock count ⟨second, rest.map value⟩) < bound := by
    rw [copyOf_eq_copyBlock]
    show size (Prenex.toPattern block.toBlock smaller) < bound
    have toPatternSize := size_toPattern_le (block := block.toBlock) smaller
    have massBound := copyBlock_mass (allowed := allowedFor count (value q)) (count := count) (value := value)
      (items := rest)
    rw [← secondIs, ← smallerIs] at massBound
    omega
  have targetSmall : size (rename (Prenex.groupIndex count (outsideOf count second)) argument) < bound := by
    rw [size_rename]
    omega
  have argumentIs : argumentOf? (value q) = argument := by rw [qIs]; rfl
  unfold CopyTest asGroup
  simp only
  rw [argumentIs]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · rw [copySame', targetSame]
    exact below.renamed _ _ copySmall targetSmall _ injective
  · rw [copySame', below.shape _ copySmall _ injective]
  · constructor
    · intro holds member inMembers replicated
      obtain ⟨place, inRest, rfl⟩ := List.mem_map.mp inMembers
      exact holds _ (List.mem_map_of_mem (restOrder place inRest)) replicated
    · intro holds member inMembers replicated
      obtain ⟨place, inOrder, rfl⟩ := List.mem_map.mp inMembers
      by_cases inGroup : place ∈ group
      · simp only [asGroup] at pTest
        have smaller' := pTest.2.2.1 (value place) (List.mem_map_of_mem ((Finset.mem_sort _).mpr inGroup)) replicated
        have pSmaller := holds (value p) (List.mem_map_of_mem pRest) pReplicated
        omega
      · exact holds _ (List.mem_map_of_mem (memRest.mpr ⟨memOrder.mp inOrder, inGroup⟩)) replicated
  · constructor
    · intro holds index below' mentioned
      obtain ⟨member, inMembers, mentionedMember⟩ := holds index below' mentioned
      obtain ⟨place, inOrder, rfl⟩ := List.mem_map.mp inMembers
      by_cases inGroup : place ∈ group
      · cases pMentions : mentions index (value p) with
        | true => exact ⟨value p, List.mem_map_of_mem pRest, pMentions⟩
        | false =>
            have qp : q ≠ p := fun same => qOuter (same ▸ pIn)
            have link : (blockSystem block ⟨count, components⟩).LinkFor p place q :=
              ⟨index, mem_mentions.mpr ⟨below', mentionedMember⟩, mem_mentions.mpr ⟨below', mentioned⟩,
                fun inP => by rw [(mem_mentions.mp inP).2] at pMentions; cases pMentions⟩
            have qInGroup := isCopy.isGroup.closed place inGroup q (Finset.mem_erase.mpr ⟨qp, qLive⟩) link
            exact absurd (groupInside qInGroup) qOuter
      · exact ⟨value place, List.mem_map_of_mem (memRest.mpr ⟨memOrder.mp inOrder, inGroup⟩), mentionedMember⟩
    · intro holds index below' mentioned
      obtain ⟨member, inMembers, mentionedMember⟩ := holds index below' mentioned
      obtain ⟨place, inRest, rfl⟩ := List.mem_map.mp inMembers
      exact ⟨value place, List.mem_map_of_mem (restOrder place inRest), mentionedMember⟩

/-! ## The laws -/

/-- **A block's absorption system has its laws and an order-blind copy test**, given the canonical form below its
size and the laws of every lighter block. -/
theorem lawful_step (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {bound : Nat} (below : Below block bound)
    (lawful : ∀ form : Prenex, form.mass < bound → form.Atomic block.toBlock →
      (blockSystem block form).Laws (places form).toFinset ∧ BlindOn block (canonicalOf block) form.count form.components)
    (form : Prenex) (heavy : form.mass ≤ bound) (atomic : form.Atomic block.toBlock) :
    (blockSystem block form).Laws (places form).toFinset ∧ BlindOn block (canonicalOf block) form.count form.components := by
  obtain ⟨count, components⟩ := form
  have blind := blindOn_of_lawful atomic below heavy lawful
  refine ⟨blockSystem_laws fresh restrictFresh ⟨count, components⟩ ?_, blind⟩
  intro live inside p group q outer isCopy qLive qReplicated outerGroup _ groupInside pIn
  exact inner_of_lawful atomic below heavy lawful blind inside isCopy qLive qReplicated outerGroup groupInside pIn

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks







