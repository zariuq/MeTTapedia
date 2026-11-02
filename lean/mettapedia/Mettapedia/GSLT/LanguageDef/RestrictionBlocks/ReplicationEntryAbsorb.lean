import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationEntryMoves

/-!
# Entries through absorption

Removing a copy group keeps the entries of the live places (`isEntry_remove_copy`): paths through the copy group go
through its replicated component instead (`reroute_copy`); a class holding the copy group holds its replicated
component and reads canonically without the copy group (`normal_class_without_copy`); a class that is a copy group
whole is the copy of a replicated component using no restriction, with that component's entry
(`entryOf_copy_class`). Hence absorbing keeps the entries (`isEntry_absorbs`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex freeIn_apply)

variable {block : ReplicationBlock}

theorem mem_keysAt_iff {form : Prenex} {place restriction : Nat} :
    restriction ∈ keysAt block form place ↔ restriction ∈ (blockSystem block form).mentions place := by
  show _ ↔ restriction ∈ (usedRestrictions form.count (placeValue block form.components place)).toFinset
  rw [List.mem_toFinset]
  rfl

/-- **A copy group is linked through shared restrictions.** -/
theorem isCopy_linkedIn {form : Prenex} {live : Finset Nat} {items : List Nat} (inItems : ∀ place ∈ live, place ∈ items)
    {p : Nat} {group : Finset Nat} (isCopy : (blockSystem block form).IsCopy live p group) {first second : Nat}
    (inFirst : first ∈ group) (inSecond : second ∈ group) :
    Linked.LinkedIn (keysAt block form) items first second := by
  have linked := isCopy.isGroup.linked first inFirst second inSecond
  have groupItems : ∀ place ∈ group, place ∈ items := fun place inGroup =>
    inItems place (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup)).2
  clear inSecond
  induction linked with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step reached =>
      obtain ⟨inMiddle, inLast, ⟨restriction, inMiddleMentions, inLastMentions, _⟩⟩ := step
      exact reached.tail ⟨groupItems _ inMiddle, groupItems _ inLast,
        ⟨restriction, mem_keysAt_iff.mpr inMiddleMentions, mem_keysAt_iff.mpr inLastMentions⟩⟩

/-- A component outside a copy group sharing a restriction with it shares a restriction its replicated component
mentions, unless it is the replicated component. -/
theorem shares_through {form : Prenex} {live : Finset Nat} {p : Nat} {group : Finset Nat}
    (isCopy : (blockSystem block form).IsCopy live p group) {member other : Nat} (inGroup : member ∈ group)
    (otherLive : other ∈ live) (otherOut : other ∉ group) (different : other ≠ p) {restriction : Nat}
    (inMember : restriction ∈ keysAt block form member) (inOther : restriction ∈ keysAt block form other) :
    restriction ∈ keysAt block form p := by
  by_contra notP
  exact otherOut (isCopy.isGroup.closed member inGroup other (Finset.mem_erase.mpr ⟨different, otherLive⟩)
    ⟨restriction, mem_keysAt_iff.mp inMember, mem_keysAt_iff.mp inOther, fun inP => notP (mem_keysAt_iff.mpr inP)⟩)

/-- **Paths around a copy group**: a path from a component outside a copy group reaches every component outside it
without the copy group, and reaches the replicated component when it reaches the copy group. -/
theorem reroute_copy {form : Prenex} {live : Finset Nat} {items : List Nat}
    (sameItems : ∀ place, place ∈ items ↔ place ∈ live) {p : Nat} {group : Finset Nat}
    (isCopy : (blockSystem block form).IsCopy live p group) {first : Nat} (firstOut : first ∉ group) :
    ∀ target, Linked.LinkedIn (keysAt block form) items first target →
      (target ∉ group → Linked.LinkedIn (keysAt block form) (items.filter fun place => !decide (place ∈ group))
        first target) ∧
      (target ∈ group → Linked.LinkedIn (keysAt block form) (items.filter fun place => !decide (place ∈ group))
        first p) := by
  have inRest : ∀ place, place ∈ items.filter (fun place => !decide (place ∈ group)) ↔ place ∈ live ∧ place ∉ group := by
    intro place
    simp [sameItems]
  have pRest : p ∈ items.filter (fun place => !decide (place ∈ group)) :=
    (inRest p).mpr ⟨isCopy.isLive, isCopy.isGroup.not_mem⟩
  intro target path
  induction path with
  | refl => exact ⟨fun _ => Relation.ReflTransGen.refl, fun inGroup => absurd inGroup firstOut⟩
  | @tail middle last _ step reached =>
      obtain ⟨inMiddle, inLast, ⟨key, inMiddleKeys, inLastKeys⟩⟩ := step
      obtain ⟨throughMiddle, throughGroup⟩ := reached
      have middleLive := (sameItems middle).mp inMiddle
      have lastLive := (sameItems last).mp inLast
      by_cases middleIn : middle ∈ group
      · have toP := throughGroup middleIn
        refine ⟨fun lastOut => ?_, fun _ => toP⟩
        by_cases lastIsP : last = p
        · rw [lastIsP]
          exact toP
        · have keyP := shares_through isCopy middleIn lastLive lastOut lastIsP inMiddleKeys inLastKeys
          exact toP.tail ⟨pRest, (inRest last).mpr ⟨lastLive, lastOut⟩, ⟨key, keyP, inLastKeys⟩⟩
      · have toMiddle := throughMiddle middleIn
        have middleRest := (inRest middle).mpr ⟨middleLive, middleIn⟩
        refine ⟨fun lastOut => toMiddle.tail ⟨middleRest, (inRest last).mpr ⟨lastLive, lastOut⟩,
          ⟨key, inMiddleKeys, inLastKeys⟩⟩, fun lastIn => ?_⟩
        by_cases middleIsP : middle = p
        · rw [← middleIsP]
          exact toMiddle
        · have keyP := shares_through isCopy lastIn middleLive middleIn middleIsP inLastKeys inMiddleKeys
          exact toMiddle.tail ⟨middleRest, pRest, ⟨key, inMiddleKeys, keyP⟩⟩

section Absorb

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **A class holding a copy group and its replicated component reads canonically without the copy group.** -/
theorem normal_class_without_copy {form : Prenex} (atomic : form.Atomic block.toBlock) {live : Finset Nat}
    (inside : live ⊆ (places form).toFinset) {p : Nat} {group : Finset Nat}
    (isCopy : (blockSystem block form).IsCopy live p group) {members : List Nat} (nodup : members.Nodup)
    (membersLive : ∀ place ∈ members, place ∈ live) (groupIn : ∀ place ∈ group, place ∈ members) (pIn : p ∈ members) :
    normal block (restrictTo block form (members.filter fun place => !decide (place ∈ group))) =
      normal block (restrictTo block form members) := by
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh atomic
  have membersInside : ∀ place ∈ members, place < form.components.length := fun place member => by
    have := inside (membersLive place member)
    simpa [places] using this
  have membersSet : members.toFinset ⊆ live := fun place member => membersLive place (List.mem_toFinset.mp member)
  have groupSet : group ⊆ members.toFinset := fun place member => List.mem_toFinset.mpr (groupIn place member)
  have pSet : p ∈ members.toFinset := List.mem_toFinset.mpr pIn
  have isCopyMembers := isCopy_restrict isCopy membersSet groupSet pSet
  have iso := restrictTo_iso (form := form) blind membersInside
  have isCopyRestricted := (iso.isCopy_iff pSet groupSet).mpr isCopyMembers
  rw [image_idxOf nodup] at isCopyRestricted
  set restricted := restrictTo block form members with restrictedIs
  have restrictedAtomic : restricted.Atomic block.toBlock := by
    intro component member
    obtain ⟨place, inMembers, rfl⟩ := List.mem_map.mp member
    exact atomic _ (placeValue_mem (membersInside place inMembers))
  obtain ⟨restrictedLaws, restrictedBlind⟩ := lawful_all fresh restrictFresh restrictedAtomic
  set kept := (members.filter fun place => !decide (place ∈ group)).map members.idxOf with keptIs
  have keptNodup : kept.Nodup := by
    rw [keptIs]
    refine (nodup.filter _).map_on fun first firstIn second secondIn same => ?_
    exact (List.idxOf_inj (List.mem_filter.mp firstIn).1).mp same
  have keptInside : ∀ place ∈ kept, place < restricted.components.length := by
    intro place member
    obtain ⟨original, inFilter, rfl⟩ := List.mem_map.mp member
    have := List.idxOf_lt_length_of_mem (List.mem_filter.mp inFilter).1
    simpa [restrictedIs, restrictTo] using this
  have placesIs : (places restricted).toFinset = (List.range members.length).toFinset := by
    simp [places, restrictedIs, restrictTo]
  have keptSet : kept.toFinset = (places restricted).toFinset \ group.image members.idxOf := by
    rw [placesIs]
    ext position
    simp only [keptIs, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range, Finset.mem_sdiff,
      Finset.mem_image, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro ⟨place, ⟨inMembers, notGroup⟩, rfl⟩
      refine ⟨List.idxOf_lt_length_of_mem inMembers, fun ⟨other, inGroup, same⟩ => notGroup ?_⟩
      rw [(List.idxOf_inj (groupIn other inGroup)).mp same] at inGroup
      exact inGroup
    · rintro ⟨below, notGroup⟩
      refine ⟨members[position], ⟨List.getElem_mem below, fun inGroup => notGroup ⟨_, inGroup, ?_⟩⟩, ?_⟩
      · exact nodup.idxOf_getElem _ below
      · exact nodup.idxOf_getElem _ below
  have removes : (blockSystem block restricted).Removes (places restricted).toFinset kept.toFinset := by
    rw [keptSet]
    refine .step (p := members.idxOf p) (copied := group.image members.idxOf) ?_ .refl
    rw [placesIs]
    exact isCopyRestricted
  have reduced := normal_restrict restrictedLaws restrictedBlind keptNodup keptInside removes
  rw [← reduced]
  congr 1
  simp only [restrictTo, restrictedIs, keptIs, List.map_map]
  congr 1
  refine List.map_congr_left fun place inFilter => ?_
  simp only [Function.comp_apply]
  exact (placeValue_idxOf (List.mem_filter.mp inFilter).1).symm

omit fresh restrictFresh in
theorem restrictionsOf_range (count : Nat) (value : Nat → Pattern) (items : List Nat) :
    restrictionsOf (List.range count) count value items = usedOf ⟨count, items.map value⟩ := by
  have := molecule_asGroup count value items
  simp only [Prenex.molecule, asGroup, prune_eq, Prenex.mk.injEq] at this
  unfold restrictionsOf usedOf
  apply List.filter_congr
  intro index member
  have below := List.mem_range.mp member
  apply Bool.eq_iff_iff.mpr
  rw [throughKeys_range]
  simp only [List.any_eq_true, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨item, inItems, listed⟩
    simp only [usedRestrictions, List.mem_filter, List.mem_range] at listed
    exact ⟨value item, ⟨item, inItems, rfl⟩, listed.2⟩
  · rintro ⟨_, ⟨item, inItems, rfl⟩, mentioned⟩
    exact ⟨item, inItems, by simp only [usedRestrictions, List.mem_filter, List.mem_range]; exact ⟨below, mentioned⟩⟩

omit fresh restrictFresh in
/-- **A group's copy is its block without unused restrictions, with the outside past the others.** -/
theorem copyOf_eq_rename_prune (count : Nat) (components : List Pattern) :
    copyOf block.toBlock count ⟨usedOf ⟨count, components⟩, components⟩ =
      rename (fun index => index + (count - (usedOf ⟨count, components⟩).length))
        (Prenex.toPattern block.toBlock (Prenex.mk count components).prune) := by
  set used := usedOf ⟨count, components⟩ with usedIs
  have usedNodup : used.Nodup := List.nodup_range.filter _
  have usedBelow : ∀ index ∈ used, index < count := fun index member => by
    rw [usedIs] at member
    unfold usedOf at member
    exact List.mem_range.mp (List.mem_filter.mp member).1
  have fewer := length_le_of_inside usedNodup usedBelow
  rw [rename_toPattern, prune_eq, ← usedIs]
  unfold copyOf Prenex.renameOuter
  simp only [List.map_map]
  congr 2
  refine List.map_congr_left fun component member => ?_
  simp only [Function.comp_apply, rename_comp]
  apply rename_congr
  intro index free
  simp only [Function.comp_apply]
  by_cases below : index < count
  · have inUsed : index ∈ used := by
      rw [usedIs]
      simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
      exact ⟨below, component, member, (mentions_iff _ _).mpr free⟩
    rw [permute_split_inside inUsed below, groupIndex_below below]
    simp [liftIndex, List.idxOf_lt_length_of_mem inUsed]
  · rw [permute_split_above (by omega), groupIndex_above (by omega)]
    simp only [liftIndex]
    rw [if_neg (by omega)]
    omega

/-- **A class that is a copy group whole is the copy of a replicated component using no restriction**, with that
component's entry. -/
theorem entryOf_copy_class (multisetFresh : block.replicate ∉ block.multisets) {form : Prenex}
    (atomic : form.Atomic block.toBlock) {live : Finset Nat} (inside : live ⊆ (places form).toFinset) {p : Nat}
    {group : Finset Nat} (isCopy : (blockSystem block form).IsCopy live p group) (alone : keysAt block form p = []) :
    entryOf block form (group.sort (· ≤ ·)) = entryOf block form [p] := by
  set value := placeValue block form.components with valueIs
  set items := group.sort (· ≤ ·) with itemsIs
  have test : CopyTest block (canonicalOf block) form.count (value p)
      (asGroup (allowedFor form.count (value p)) form.count value items) := isCopy.isCopy
  have noMention : ∀ index < form.count, mentions index (value p) = false := by
    intro index below
    by_contra mentioned
    have inKeys : index ∈ keysAt block form p := by
      simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range]
      exact ⟨below, by simpa using mentioned⟩
    rw [alone] at inKeys
    cases inKeys
  have allowedAll : allowedFor form.count (value p) = List.range form.count := by
    unfold allowedFor
    apply List.filter_eq_self.mpr
    intro index member
    simp [noMention index (List.mem_range.mp member)]
  rw [allowedAll] at test
  obtain ⟨same, notReplicated, -, -⟩ := test
  have groupIs : asGroup (List.range form.count) form.count value items =
      ⟨usedOf ⟨form.count, items.map value⟩, items.map value⟩ := by
    unfold asGroup
    rw [restrictionsOf_range]
  rw [groupIs, copyOf_eq_rename_prune] at same notReplicated
  simp only at same
  -- the replicated component and its argument
  obtain ⟨argument, componentIs⟩ := replicated_shape (block := block) (component := value p)
    (isCopy.isReplicated : isReplicated block (placeValue block form.components p) = true)
  rw [componentIs] at same
  simp only [argumentOf?] at same
  set used := usedOf ⟨form.count, items.map value⟩ with usedIs
  have usedNodup : used.Nodup := List.nodup_range.filter _
  have usedBelow : ∀ index ∈ used, index < form.count := fun index member => by
    rw [usedIs] at member
    unfold usedOf at member
    exact List.mem_range.mp (List.mem_filter.mp member).1
  have fewer := length_le_of_inside usedNodup usedBelow
  set shift := fun index => index + (form.count - used.length) with shiftIs
  have shiftInjective : Function.Injective shift := fun first second equal => by
    simp only [shiftIs] at equal
    omega
  have argumentFar : ∀ index, FreeIn index argument → form.count ≤ index := by
    intro index free
    by_contra near
    have mentioned : mentions index (value p) = true := by
      rw [componentIs, mentions_iff, freeIn_apply]
      exact ⟨argument, List.mem_singleton_self _, free⟩
    rw [noMention index (by omega)] at mentioned
    cases mentioned
  have argumentIs : rename (Prenex.groupIndex form.count (outsideOf form.count used)) argument =
      rename shift (rename (Prenex.groupIndex form.count []) argument) := by
    rw [rename_comp]
    apply rename_congr
    intro index free
    have far := argumentFar index free
    have outsideLength := outsideOf_length usedNodup usedBelow
    simp only [Function.comp_apply, shiftIs]
    rw [groupIndex_above far, groupIndex_above far, outsideLength]
    simp
  rw [argumentIs] at same
  -- canonical forms below every size
  have below := below_all fresh restrictFresh (max (size (Prenex.toPattern block.toBlock
    (Prenex.mk form.count (items.map value)).prune)) (size (rename (Prenex.groupIndex form.count []) argument)) + 1)
  have canonicalSame := (below.renamed _ _ (Nat.lt_succ_of_le (le_max_left _ _))
    (Nat.lt_succ_of_le (le_max_right _ _)) shift shiftInjective).mp same
  have itemsAtomic : (Prenex.mk form.count (items.map value)).Atomic block.toBlock := by
    intro component member
    obtain ⟨place, inItems, rfl⟩ := List.mem_map.mp member
    have inGroup : place ∈ group := (Finset.mem_sort _).mp inItems
    have := inside (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup)).2
    exact atomic _ (placeValue_mem (by simpa [places] using this))
  have prunedAtomic := prune_atomic itemsAtomic
  have prunedUsed := used_prune (Prenex.mk form.count (items.map value))
  rw [canonicalOf_toPattern prunedAtomic prunedUsed, normal_prune fresh restrictFresh _ itemsAtomic] at canonicalSame
  have shapeSame := below.shape _ (Nat.lt_succ_of_le (le_max_left _ _)) shift shiftInjective
  rw [notReplicated, canonicalOf_toPattern prunedAtomic prunedUsed,
    normal_prune fresh restrictFresh _ itemsAtomic] at shapeSame
  -- the entry of the group
  have groupEntry : entryOf block form items = .apply block.replicate
      [canonicalOf block (rename (Prenex.groupIndex form.count []) argument)] := by
    unfold entryOf restrictTo
    rw [canonicalSame]
    exact bang_of_not_replicated (by rw [← canonicalSame]; exact shapeSame.symm)
  -- the entry of the replicated component alone
  have usedSingle : usedOf (Prenex.mk form.count [value p]) = [] := by
    unfold usedOf
    apply List.filter_eq_nil_iff.mpr
    intro index member
    simp [noMention index (List.mem_range.mp member)]
  have singleAtomic : (Prenex.mk form.count [value p]).Atomic block.toBlock := by
    intro component member
    rw [List.mem_singleton] at member
    subst member
    exact atomic _ (placeValue_mem (by
      have := inside isCopy.isLive
      simpa [places] using this))
  have renamedAtomic : decompose block.toBlock (rename (Prenex.groupIndex form.count []) (value p)) =
      Prenex.atom (rename (Prenex.groupIndex form.count []) (value p)) :=
    atomic_rename (singleAtomic _ List.mem_cons_self) _
  have singleEntry : entryOf block form [p] = .apply block.replicate
      [canonicalOf block (rename (Prenex.groupIndex form.count []) argument)] := by
    have prunedIs : (Prenex.mk form.count [value p]).prune =
        ⟨0, [rename (Prenex.groupIndex form.count []) (value p)]⟩ := by
      rw [prune_eq, usedSingle]
      rfl
    unfold entryOf restrictTo
    simp only [List.map_cons, List.map_nil]
    rw [← valueIs, ← normal_prune fresh restrictFresh _ singleAtomic, prunedIs]
    have canonicalIs : Prenex.toPattern block.toBlock (normal block ⟨0, [rename (Prenex.groupIndex form.count []) (value p)]⟩) =
        recanon block (rename (Prenex.groupIndex form.count []) (value p)) := by
      have := canonicalOf_atom (block := block) renamedAtomic
      unfold canonicalOf at this
      rwa [renamedAtomic] at this
    rw [canonicalIs, componentIs, rename_apply]
    simp only [List.map_cons, List.map_nil]
    rw [recanon_apply]
    simp only [List.map_cons, List.map_nil]
    have partIs : partOf block block.replicate (rename (Prenex.groupIndex form.count []) argument) =
        canonicalOf block (rename (Prenex.groupIndex form.count []) argument) := by
      unfold partOf
      rw [if_neg restrictFresh, if_neg multisetFresh]
    rw [partIs]
    exact bang_of_replicated (by simp [isReplicated])
  rw [groupEntry, singleEntry]

/-- **Removing a copy group keeps the entries of the live places.** -/
theorem isEntry_remove_copy (multisetFresh : block.replicate ∉ block.multisets) {form : Prenex}
    (atomic : form.Atomic block.toBlock) {live : Finset Nat} (inside : live ⊆ (places form).toFinset) {p : Nat}
    {group : Finset Nat} (isCopy : (blockSystem block form).IsCopy live p group) (pattern : Pattern) :
    IsEntry block form ((live \ group).sort (· ≤ ·)) pattern ↔ IsEntry block form (live.sort (· ≤ ·)) pattern := by
  set items := live.sort (· ≤ ·) with itemsIs
  set rest := items.filter fun place => !decide (place ∈ group) with restIs
  have itemsNodup : items.Nodup := Finset.sort_nodup _ _
  have restNodup : rest.Nodup := itemsNodup.filter _
  have sameItems : ∀ place, place ∈ items ↔ place ∈ live := fun place => Finset.mem_sort _
  have inRest : ∀ place, place ∈ rest ↔ place ∈ live ∧ place ∉ group := by
    intro place
    simp [restIs, sameItems]
  have liveInside : ∀ place ∈ live, place < form.components.length := fun place member => by
    have := inside member
    simpa [places] using this
  have itemsInside : ∀ place ∈ items, place < form.components.length :=
    fun place member => liveInside place ((sameItems place).mp member)
  have groupLive : ∀ place ∈ group, place ∈ live := fun place member =>
    (Finset.mem_erase.mp (isCopy.isGroup.subset member)).2
  have pRest : p ∈ rest := (inRest p).mpr ⟨isCopy.isLive, isCopy.isGroup.not_mem⟩
  -- the live places outside the copy group, in order
  rw [isEntry_of_mem_iff fresh restrictFresh atomic (Finset.sort_nodup _ _) restNodup
    (fun place member => liveInside place (Finset.mem_sdiff.mp ((Finset.mem_sort _).mp member)).1)
    (fun place => by rw [Finset.mem_sort, Finset.mem_sdiff, inRest]) pattern]
  have reroute : ∀ first ∈ items, (decide (first ∈ group)) = false → ∀ second ∈ items,
      (decide (second ∈ group)) = false → Linked.LinkedIn (keysAt block form) items first second →
      Linked.LinkedIn (keysAt block form) (items.filter fun place => !decide (place ∈ group)) first second := by
    intro first _ firstOut second _ secondOut linked
    exact (reroute_copy sameItems isCopy (by simpa using firstOut) second linked).1 (by simpa using secondOut)
  have classInside : ∀ place, ∀ other ∈ classIn block form items place, other < form.components.length :=
    fun _ other member => itemsInside other (mem_classIn.mp member).1
  -- the entry of a class outside the copy group, without the copy group
  have entryWithout : ∀ place ∈ items, place ∉ group →
      entryOf block form (classIn block form rest place) = entryOf block form (classIn block form items place) := by
    intro place inItems outside
    have filtered : (classIn block form rest place).Perm
        ((classIn block form items place).filter fun place => !decide (place ∈ group)) := by
      rw [List.perm_ext_iff_of_nodup (classIn_nodup restNodup place) ((classIn_nodup itemsNodup place).filter _)]
      exact classIn_filter (fun place => decide (place ∈ group)) reroute inItems (by simpa using outside)
    have filteredInside : ∀ other ∈ classIn block form rest place, other < form.components.length :=
      fun other member => liveInside other ((inRest other).mp (mem_classIn.mp member).1).1
    rw [entryOf_perm fresh restrictFresh atomic filteredInside filtered]
    by_cases hit : ∃ member ∈ group, member ∈ classIn block form items place
    · obtain ⟨member, inGroup, inClass⟩ := hit
      have groupIn : ∀ other ∈ group, other ∈ classIn block form items place := by
        intro other otherIn
        obtain ⟨_, toMember⟩ := mem_classIn.mp inClass
        exact mem_classIn.mpr ⟨(sameItems other).mpr (groupLive other otherIn),
          toMember.trans (isCopy_linkedIn (fun place member => (sameItems place).mpr member) isCopy inGroup otherIn)⟩
      have pIn : p ∈ classIn block form items place := by
        obtain ⟨_, toMember⟩ := mem_classIn.mp inClass
        have toP := (reroute_copy sameItems isCopy outside member toMember).2 inGroup
        exact mem_classIn.mpr ⟨(sameItems p).mpr isCopy.isLive,
          toP.mono fun other member => (List.mem_filter.mp member).1⟩
      unfold entryOf
      rw [normal_class_without_copy fresh restrictFresh atomic inside isCopy (classIn_nodup itemsNodup place)
        (fun other member => (sameItems other).mp (mem_classIn.mp member).1) groupIn pIn]
    · push Not at hit
      congr 1
      apply List.filter_eq_self.mpr
      intro other member
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      exact fun inGroup => hit other inGroup member
  constructor
  · rintro ⟨place, inPlace, rfl⟩
    obtain ⟨inLive, outside⟩ := (inRest place).mp inPlace
    exact ⟨place, (sameItems place).mpr inLive, (entryWithout place ((sameItems place).mpr inLive) outside).symm⟩
  · rintro ⟨place, inItems, rfl⟩
    by_cases outside : place ∉ group
    · exact ⟨place, (inRest place).mpr ⟨(sameItems place).mp inItems, outside⟩,
        entryWithout place inItems outside⟩
    · push Not at outside
      by_cases escape : ∃ other ∈ classIn block form items place, other ∉ group
      · obtain ⟨other, inClass, otherOut⟩ := escape
        have otherItems := (mem_classIn.mp inClass).1
        refine ⟨other, (inRest other).mpr ⟨(sameItems other).mp otherItems, otherOut⟩, ?_⟩
        rw [entryWithout other otherItems otherOut]
        exact entryOf_perm fresh restrictFresh atomic (classInside other) (classIn_perm_of_mem itemsNodup inClass)
      · push Not at escape
        -- the class is the copy group whole
        have classPerm : (classIn block form items place).Perm (group.sort (· ≤ ·)) := by
          rw [List.perm_ext_iff_of_nodup (classIn_nodup itemsNodup place) (Finset.sort_nodup _ _)]
          intro other
          rw [Finset.mem_sort]
          constructor
          · exact escape other
          · intro inGroup
            exact mem_classIn.mpr ⟨(sameItems other).mpr (groupLive other inGroup),
              isCopy_linkedIn (fun place member => (sameItems place).mpr member) isCopy outside inGroup⟩
        -- its replicated component uses no restriction
        have alone : keysAt block form p = [] := by
          by_contra used
          obtain ⟨restriction, inKeys⟩ := List.exists_mem_of_ne_nil _ used
          have test : CopyTest block (canonicalOf block) form.count (placeValue block form.components p)
              (asGroup (allowedFor form.count (placeValue block form.components p)) form.count
                (placeValue block form.components) (group.sort (· ≤ ·))) := isCopy.isCopy
          have keyBelow : restriction < form.count := by
            simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range] at inKeys
            exact inKeys.1
          have keyMentioned : mentions restriction (placeValue block form.components p) = true := by
            simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range] at inKeys
            simpa using inKeys.2
          obtain ⟨_, componentIn, mentioned⟩ := test.2.2.2 restriction keyBelow keyMentioned
          obtain ⟨member, inSorted, rfl⟩ := List.mem_map.mp componentIn
          have inGroup : member ∈ group := (Finset.mem_sort _).mp inSorted
          have memberKeys : restriction ∈ keysAt block form member := by
            simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range]
            exact ⟨keyBelow, by simpa using mentioned⟩
          have linkedP : Linked.LinkedIn (keysAt block form) items place p :=
            (isCopy_linkedIn (fun place member => (sameItems place).mpr member) isCopy outside inGroup).tail
              ⟨(sameItems member).mpr (groupLive member inGroup), (sameItems p).mpr isCopy.isLive,
                ⟨restriction, memberKeys, inKeys⟩⟩
          exact isCopy.isGroup.not_mem (escape p (mem_classIn.mpr ⟨(sameItems p).mpr isCopy.isLive, linkedP⟩))
        refine ⟨p, pRest, ?_⟩
        rw [classIn_of_keys_nil restNodup pRest alone,
          entryOf_perm fresh restrictFresh atomic (classInside place) classPerm,
          entryOf_copy_class fresh restrictFresh multisetFresh atomic inside isCopy alone]

omit fresh restrictFresh in
/-- **Absorbing keeps the entries of the live places.** -/
theorem isEntry_absorbs (multisetFresh : block.replicate ∉ block.multisets) (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) {form : Prenex} (atomic : form.Atomic block.toBlock)
    {live final : Finset Nat} (absorbs : (blockSystem block form).Absorbs live final) :
    live ⊆ (places form).toFinset → ∀ pattern,
      IsEntry block form (final.sort (· ≤ ·)) pattern ↔ IsEntry block form (live.sort (· ≤ ·)) pattern := by
  induction absorbs with
  | done => exact fun _ _ => Iff.rfl
  | step isCopy _ recurse =>
      intro inside pattern
      rw [recurse (Finset.sdiff_subset.trans inside) pattern]
      exact isEntry_remove_copy fresh restrictFresh multisetFresh atomic inside isCopy pattern

end Absorb

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
