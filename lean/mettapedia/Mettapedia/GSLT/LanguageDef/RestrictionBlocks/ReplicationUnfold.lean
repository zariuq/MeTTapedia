import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationMolecules

/-!
# Unfolding a replication

A replicated component's canonical argument is smaller than the pattern of its block's canonical form
(`size_argument_lt`): absorption keeps a replicated component at least as high (`exists_survivor`). So each class of
a block that is no replication is a copy of its replicated molecule beside the block (`isCopy_molecule`), and a block
beside its replicated molecules reads canonically as the replicated molecules alone (`normal_par_replicatedOf`):
`P | !P = !P` on canonical blocks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex freeIn_apply)

variable {block : ReplicationBlock}

/-- **Absorption keeps a replicated component at least as high as each one it removes.** -/
theorem exists_survivor {system : CopyGroups.System Nat} {whole : Finset Nat} (laws : system.Laws whole)
    {live final : Finset Nat} (absorbs : system.Absorbs live final) :
    live ⊆ whole → ∀ place ∈ live, system.replicated place →
      ∃ kept ∈ final, system.replicated kept ∧ system.height place ≤ system.height kept := by
  induction absorbs with
  | done => exact fun _ place inLive replicated => ⟨place, inLive, replicated, le_refl _⟩
  | @step live final q copied isCopy _ recurse =>
      intro inside place inLive replicated
      have restInside : live \ copied ⊆ whole := Finset.sdiff_subset.trans inside
      by_cases inCopied : place ∈ copied
      · have lower := laws.lower copied (fun member inGroup => inside (Finset.mem_erase.mp
          (isCopy.isGroup.subset inGroup)).2) q (inside isCopy.isLive) isCopy.isGroup.not_mem place
          isCopy.isReplicated isCopy.isCopy inCopied replicated
        obtain ⟨kept, inFinal, keptReplicated, higher⟩ := recurse restInside q isCopy.live_rest isCopy.isReplicated
        exact ⟨kept, inFinal, keptReplicated, by omega⟩
      · exact recurse restInside place (Finset.mem_sdiff.mpr ⟨inLive, inCopied⟩) replicated

section Unfold

variable (multisetFresh : block.replicate ∉ block.multisets) (fresh : block.replicate ∉ block.emptyUnits)
  (restrictFresh : block.replicate ≠ block.restrict)

include multisetFresh fresh restrictFresh

/-- **A replicated component's canonical argument is smaller than its block's canonical pattern.** -/
theorem size_argument_lt {form : Prenex} (atomic : form.Atomic block.toBlock) {component : Pattern}
    (member : component ∈ form.components) (replicated : isReplicated block component = true) :
    size (canonicalOf block (argumentOf? component)) < size (Prenex.toPattern block.toBlock (normal block form)) := by
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh atomic
  obtain ⟨final, finalNodup, absorbs, absorbed⟩ := absorb_places blind
  obtain ⟨place, below, rfl⟩ := List.getElem_of_mem member
  have valueIs : placeValue block form.components place = form.components[place] := List.getD_eq_getElem _ _ below
  have placeLive : place ∈ (places form).toFinset := by simp [places, below]
  obtain ⟨kept, keptFinal, keptReplicated, higher⟩ := exists_survivor laws absorbs (Finset.Subset.refl _) place
    placeLive (show isReplicated block (placeValue block form.components place) = true by rw [valueIs]; exact replicated)
  have keptReplicated' : isReplicated block (placeValue block form.components kept) = true := keptReplicated
  have higher' : size (canonicalOf block (argumentOf? (placeValue block form.components place))) ≤
      size (canonicalOf block (argumentOf? (placeValue block form.components kept))) := higher
  rw [valueIs] at higher'
  have keptIn : kept ∈ final := List.mem_toFinset.mp keptFinal
  obtain ⟨argument, keptIs⟩ := replicated_shape keptReplicated'
  have keptArgument : argumentOf? (placeValue block form.components kept) = argument := by
    rw [keptIs]
    rfl
  rw [keptArgument] at higher'
  -- the kept replicated component in the canonical block
  set absorbedForm := (Prenex.mk form.count (final.map (placeValue block form.components))).prune with absorbedIs
  obtain ⟨order, inOrders, leastIs⟩ := least_reading_mem (block := block) absorbedForm
  have isOrder : IsOrder absorbedForm.count order := readingOrders_isOrder inOrders
  set used := usedOf (Prenex.mk form.count (final.map (placeValue block form.components))) with usedIs
  set relabel := Prenex.permute absorbedForm.count order ∘ Prenex.groupIndex form.count used with relabelIs
  have keptRead : recanon block (rename relabel (placeValue block form.components kept)) ∈
      (normal block form).components := by
    rw [normal_eq_reading form, absorbed]
    show _ ∈ least (readingsR block absorbedForm)
    rw [leastIs, mem_reading_iff]
    refine ⟨rename (Prenex.groupIndex form.count used) (placeValue block form.components kept), ?_, ?_⟩
    · rw [absorbedIs, prune_eq]
      exact List.mem_map_of_mem (List.mem_map_of_mem keptIn)
    · simp only [relabelIs, rename_comp]
  have partIs : ∀ pattern, partOf block block.replicate pattern = canonicalOf block pattern := by
    intro pattern
    unfold partOf
    rw [if_neg restrictFresh, if_neg multisetFresh]
  have readIs : recanon block (rename relabel (placeValue block form.components kept)) =
      .apply block.replicate [canonicalOf block (rename relabel argument)] := by
    rw [keptIs, rename_apply, List.map_cons, List.map_nil, recanon_apply, List.map_cons, List.map_nil, partIs]
  rw [readIs] at keptRead
  -- the renaming tells the argument's names apart
  have usedNodup : used.Nodup := List.nodup_range.filter _
  obtain ⟨injectiveRelabel, injective, agrees⟩ := exists_injective_on [argument] relabel
    (fun index => index < form.count → index ∈ used)
    (fun pattern inList index free => by
      rw [List.mem_singleton] at inList
      subst inList
      intro low
      have mentioned : mentions index (placeValue block form.components kept) = true := by
        rw [keptIs, mentions_iff, freeIn_apply]
        exact ⟨_, List.mem_singleton_self _, free⟩
      simp only [usedIs, usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
      exact ⟨low, _, List.mem_map_of_mem keptIn, mentioned⟩)
    (fun first second firstIn secondIn same => by
      simp only [relabelIs, Function.comp_apply] at same
      have inner := permute_injective isOrder same
      by_cases firstLow : first < form.count <;> by_cases secondLow : second < form.count
      · rw [groupIndex_below firstLow, groupIndex_below secondLow] at inner
        exact (List.idxOf_inj (firstIn firstLow)).mp inner
      · rw [groupIndex_below firstLow, groupIndex_above (by omega)] at inner
        have := List.idxOf_lt_length_of_mem (firstIn firstLow)
        omega
      · rw [groupIndex_above (by omega), groupIndex_below secondLow] at inner
        have := List.idxOf_lt_length_of_mem (secondIn secondLow)
        omega
      · rw [groupIndex_above (by omega), groupIndex_above (by omega)] at inner
        omega)
  have renamedSame := agrees argument (List.mem_singleton_self _)
  have sized := (below_all fresh restrictFresh (size argument + 1)).sized argument (Nat.lt_succ_self _)
    injectiveRelabel injective
  rw [renamedSame] at sized
  -- the canonical pattern is at least as large as its components
  have componentSmall := size_lt_of_mem keptRead
  have patternSize := size_toPattern_eq block.toBlock (normal block form)
  simp only [size, sizeList] at componentSmall
  omega

omit multisetFresh fresh restrictFresh in
/-- A pattern lifted past a block's restrictions mentions none of them. -/
theorem mentions_lift_false {count index : Nat} (below : index < count) (pattern : Pattern) :
    mentions index (rename (shiftAbove 0 count) pattern) = false := by
  apply Bool.eq_false_iff.mpr
  intro mentioned
  rw [mentions_iff, freeIn_rename] at mentioned
  obtain ⟨original, _, maps⟩ := mentioned
  simp only [shiftAbove, Nat.not_lt_zero, if_false] at maps
  omega

omit multisetFresh fresh restrictFresh in
theorem rename_lower_lift (count : Nat) (pattern : Pattern) :
    rename (Prenex.groupIndex count []) (rename (shiftAbove 0 count) pattern) = pattern := by
  rw [rename_comp]
  conv_rhs => rw [← rename_id pattern]
  apply rename_congr
  intro index _
  simp only [Function.comp_apply, shiftAbove, Nat.not_lt_zero, if_false, id]
  rw [groupIndex_above (by omega)]
  simp

omit multisetFresh in
/-- **A block whose components each use a restriction keeps one in its canonical form.** -/
theorem normal_count_pos {count : Nat} {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock) (nonempty : components ≠ [])
    (uses : ∀ component ∈ components, ∃ index < count, mentions index component = true) :
    0 < (normal block ⟨count, components⟩).count := by
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh atomic
  obtain ⟨final, _, absorbs, absorbed⟩ := absorb_places blind
  have finalIs := absorbs.eq laws (Finset.Subset.refl _)
  have placesNonempty : (places (Prenex.mk count components)).toFinset.Nonempty :=
    ⟨0, by simp [places, List.length_pos_of_ne_nil nonempty]⟩
  obtain ⟨kept, keptLive, keptNotCopy⟩ := CopyGroups.System.exists_not_copy laws (Finset.Subset.refl _) placesNonempty
  have keptFinal : kept ∈ final := by
    rw [← List.mem_toFinset, finalIs]
    exact Finset.mem_sdiff.mpr ⟨keptLive, keptNotCopy⟩
  have keptBelow : kept < components.length := by simpa [places] using keptLive
  obtain ⟨index, below, mentioned⟩ := uses _ (placeValue_mem (block := block) keptBelow)
  rw [normal_eq_reading, absorbed]
  simp only [prune_eq]
  apply List.length_pos_of_mem (a := index)
  simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
  exact ⟨below, _, List.mem_map_of_mem keptFinal, mentioned⟩

omit multisetFresh in
/-- **A class's canonical pattern is a replication only for a lone replication using no restriction.** -/
theorem lone_of_replicated {form : Prenex} (atomic : form.Atomic block.toBlock) {group : List Nat}
    (member : group ∈ Linked.build (keysAt block form) (places form))
    (replicated : isReplicated block (Prenex.toPattern block.toBlock (normal block (restrictTo block form group))) = true) :
    ∃ place, group = [place] ∧ keysAt block form place = [] ∧
      isReplicated block (placeValue block form.components place) = true := by
  have grouping := Linked.build_grouping (keys := keysAt block form) (places form)
  have groupNodup := grouping.group_nodup (places_nodup form) member
  have groupInside : ∀ place ∈ group, place < form.components.length := fun place inGroup => by
    have := grouping.mem_items member inGroup
    simpa [places] using this
  have restrictedAtomic : (restrictTo block form group).Atomic block.toBlock := by
    intro component inComponents
    obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp inComponents
    exact atomic _ (placeValue_mem (groupInside place inGroup))
  have nonempty : group ≠ [] := grouping.nonempty group member
  -- a class with a restriction keeps it, and is no replication
  have notUses : ¬ ∀ place ∈ group, keysAt block form place ≠ [] := by
    intro uses
    have positive := normal_count_pos fresh restrictFresh restrictedAtomic (by simpa using nonempty)
      (fun component inComponents => by
        obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp inComponents
        obtain ⟨key, inKeys⟩ := List.exists_mem_of_ne_nil _ (uses place inGroup)
        simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range] at inKeys
        exact ⟨key, inKeys.1, inKeys.2⟩)
    rw [isReplicated_toPattern restrictFresh] at replicated
    simp only [Bool.and_eq_true, decide_eq_true_eq] at replicated
    have zero : (normal block (restrictTo block form group)).count = 0 := replicated.1.1
    unfold restrictTo at zero
    omega
  push Not at notUses
  obtain ⟨place, inGroup, alone⟩ := notUses
  have single : group = [place] := by
    have classIs := classIn_of_keys_nil (block := block) (form := form) (places_nodup form)
      (grouping.mem_items member inGroup) alone
    have groupPerm : group.Perm [place] := by
      rw [List.perm_ext_iff_of_nodup groupNodup (List.nodup_singleton place)]
      intro other
      rw [grouping.mem_iff member inGroup other, List.mem_singleton]
      constructor
      · intro linked
        have := mem_classIn.mpr ⟨grouping.mem_items member ((grouping.mem_iff member inGroup other).mpr linked),
          linked⟩
        rw [classIs, List.mem_singleton] at this
        exact this
      · rintro rfl
        exact Relation.ReflTransGen.refl
    exact List.perm_singleton.mp groupPerm
  subst single
  refine ⟨place, rfl, alone, ?_⟩
  -- the lone component's canonical pattern is its own reading, renamed
  have noMention : ∀ index < form.count, mentions index (placeValue block form.components place) = false := by
    intro index below
    by_contra mentioned
    have inKeys : index ∈ keysAt block form place := by
      simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range]
      exact ⟨below, by simpa using mentioned⟩
    rw [alone] at inKeys
    cases inKeys
  have usedNil : usedOf (Prenex.mk form.count [placeValue block form.components place]) = [] := by
    unfold usedOf
    apply List.filter_eq_nil_iff.mpr
    intro index member
    simp [noMention index (List.mem_range.mp member)]
  have singleAtomic : (Prenex.mk form.count [placeValue block form.components place]).Atomic block.toBlock :=
    fun component member => by
      rw [List.mem_singleton] at member
      subst member
      exact atomic _ (placeValue_mem (groupInside place (List.mem_singleton_self _)))
  unfold restrictTo at replicated
  simp only [List.map_cons, List.map_nil] at replicated
  rw [← normal_prune fresh restrictFresh _ singleAtomic, prune_eq, usedNil] at replicated
  have renamedAtomic : decompose block.toBlock (rename (Prenex.groupIndex form.count []) (placeValue block form.components place)) =
      Prenex.atom (rename (Prenex.groupIndex form.count []) (placeValue block form.components place)) :=
    atomic_rename (singleAtomic _ List.mem_cons_self) _
  have canonicalIs := canonicalOf_atom (block := block) renamedAtomic
  unfold canonicalOf at canonicalIs
  rw [renamedAtomic] at canonicalIs
  simp only [List.length_nil, List.map_cons, List.map_nil] at replicated
  rw [show (Prenex.mk 0 [rename (Prenex.groupIndex form.count []) (placeValue block form.components place)]) =
    Prenex.atom (rename (Prenex.groupIndex form.count []) (placeValue block form.components place)) from rfl,
    canonicalIs, isReplicated_recanon, isReplicated_rename] at replicated
  exact replicated

/-- **A class of a block that is no replication is a copy group of its replicated molecule beside the block.** -/
theorem isCopy_molecule {count : Nat} {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock) {group : List Nat}
    (member : group ∈ Linked.build (keysAt block ⟨count, components⟩) (places (Prenex.mk count components)))
    (notLone : isReplicated block (Prenex.toPattern block.toBlock
      (normal block (restrictTo block ⟨count, components⟩ group))) = false)
    {entries : List Pattern} {index : Nat} (indexBelow : index < entries.length)
    (entryAt : entries[index] = entryOf block ⟨count, components⟩ group) {live : Finset Nat}
    (groupLive : ∀ place ∈ group, place ∈ live) (pLive : components.length + index ∈ live) :
    (blockSystem block ⟨count, components ++ entries.map (rename (shiftAbove 0 count))⟩).IsCopy live
      (components.length + index) group.toFinset := by
  have grouping := Linked.build_grouping (keys := keysAt block ⟨count, components⟩) (places (Prenex.mk count components))
  have groupNodup := grouping.group_nodup (places_nodup _) member
  have groupInside : ∀ place ∈ group, place < components.length := fun place inGroup => by
    have := grouping.mem_items member inGroup
    simpa [places] using this
  set canonical := Prenex.toPattern block.toBlock (normal block (restrictTo block ⟨count, components⟩ group))
    with canonicalIs
  have liftedLength : (entries.map (rename (shiftAbove 0 count))).length = entries.length := List.length_map _
  -- the values of the wide block
  have leftValue : ∀ place, place < components.length →
      placeValue block (components ++ entries.map (rename (shiftAbove 0 count))) place =
        placeValue block components place :=
    fun place below => placeValue_append_left below
  have rightValue : ∀ offset (below : offset < entries.length),
      placeValue block (components ++ entries.map (rename (shiftAbove 0 count))) (components.length + offset) =
        rename (shiftAbove 0 count) entries[offset] := by
    intro offset below
    rw [placeValue_append_right (by rw [liftedLength]; exact below)]
    unfold placeValue
    rw [List.getD_eq_getElem _ _ (by rw [liftedLength]; exact below), List.getElem_map]
  have pValue : placeValue block (components ++ entries.map (rename (shiftAbove 0 count))) (components.length + index) =
      rename (shiftAbove 0 count) (.apply block.replicate [canonical]) := by
    rw [rightValue index indexBelow, entryAt]
    unfold entryOf
    rw [← canonicalIs, bang_of_not_replicated notLone]
  have leftKeys : ∀ place, place < components.length →
      keysAt block ⟨count, components ++ entries.map (rename (shiftAbove 0 count))⟩ place =
        keysAt block ⟨count, components⟩ place := by
    intro place below
    show usedRestrictions count (placeValue block (components ++ entries.map (rename (shiftAbove 0 count))) place) =
      usedRestrictions count (placeValue block components place)
    rw [leftValue place below]
  have liftedNoMention : ∀ pattern, ∀ restriction < count,
      restriction ∉ (usedRestrictions count (rename (shiftAbove 0 count) pattern)).toFinset := by
    intro pattern restriction below inUsed
    simp only [List.mem_toFinset, mem_usedRestrictions] at inUsed
    rw [mentions_lift_false below] at inUsed
    exact Bool.false_ne_true inUsed.2
  have pMentions : ∀ restriction, restriction ∉ (blockSystem block
      ⟨count, components ++ entries.map (rename (shiftAbove 0 count))⟩).mentions (components.length + index) := by
    intro restriction inMentions
    have inUsed : restriction ∈ (usedRestrictions count (placeValue block
        (components ++ entries.map (rename (shiftAbove 0 count))) (components.length + index))).toFinset := inMentions
    rw [pValue] at inUsed
    have below : restriction < count := by
      simp only [List.mem_toFinset, mem_usedRestrictions] at inUsed
      exact inUsed.1
    exact liftedNoMention _ restriction below inUsed
  have rightMentions : ∀ place, components.length ≤ place → ∀ restriction, restriction ∉ (blockSystem block
      ⟨count, components ++ entries.map (rename (shiftAbove 0 count))⟩).mentions place := by
    intro place above restriction inMentions
    have inUsed : restriction ∈ (usedRestrictions count (placeValue block
        (components ++ entries.map (rename (shiftAbove 0 count))) place)).toFinset := inMentions
    have below : restriction < count := by
      simp only [List.mem_toFinset, mem_usedRestrictions] at inUsed
      exact inUsed.1
    by_cases inside : place - components.length < entries.length
    · have shifted : place = components.length + (place - components.length) := by omega
      rw [shifted, rightValue _ inside] at inUsed
      exact liftedNoMention _ restriction below inUsed
    · have far : (components ++ entries.map (rename (shiftAbove 0 count))).length ≤ place := by
        simp only [List.length_append, liftedLength]
        omega
      have unitIs : placeValue block (components ++ entries.map (rename (shiftAbove 0 count))) place =
          .apply block.unit [] := List.getD_eq_default _ _ far
      rw [unitIs] at inUsed
      simp only [List.mem_toFinset, mem_usedRestrictions, mentions_iff, freeIn_apply] at inUsed
      simp at inUsed
  -- the group is a group of the replicated molecule
  have isGroup : (blockSystem block ⟨count, components ++ entries.map (rename (shiftAbove 0 count))⟩).IsGroup live
      (components.length + index) group.toFinset := by
    refine ⟨fun place inGroup => ?_, ?_, fun first inFirst second inSecond => ?_,
      fun first inFirst second inSecond link => ?_⟩
    · have inList := List.mem_toFinset.mp inGroup
      exact Finset.mem_erase.mpr ⟨by have := groupInside place inList; omega, groupLive place inList⟩
    · obtain ⟨first, inFirst⟩ := List.exists_mem_of_ne_nil _ (grouping.nonempty group member)
      exact ⟨first, List.mem_toFinset.mpr inFirst⟩
    · have linked := grouping.linked group member first (List.mem_toFinset.mp inFirst) second
        (List.mem_toFinset.mp inSecond)
      clear inSecond
      induction linked with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ step reached =>
          obtain ⟨inMiddle, inLast, ⟨key, inMiddleKeys, inLastKeys⟩⟩ := step
          refine reached.tail ⟨List.mem_toFinset.mpr inMiddle, List.mem_toFinset.mpr inLast, ⟨key, ?_, ?_, pMentions key⟩⟩
          · show key ∈ (keysAt block _ _).toFinset
            rw [leftKeys _ (groupInside _ inMiddle), List.mem_toFinset]
            exact inMiddleKeys
          · show key ∈ (keysAt block _ _).toFinset
            rw [leftKeys _ (groupInside _ inLast), List.mem_toFinset]
            exact inLastKeys
    · obtain ⟨key, inFirstKeys, inSecondKeys, _⟩ := link
      have firstList := List.mem_toFinset.mp inFirst
      by_cases secondLeft : second < components.length
      · have firstKeys : key ∈ keysAt block ⟨count, components⟩ first := by
          have : key ∈ (keysAt block _ first).toFinset := inFirstKeys
          rwa [leftKeys first (groupInside first firstList), List.mem_toFinset] at this
        have secondKeys : key ∈ keysAt block ⟨count, components⟩ second := by
          have : key ∈ (keysAt block _ second).toFinset := inSecondKeys
          rwa [leftKeys second secondLeft, List.mem_toFinset] at this
        have secondPlaces : second ∈ places (Prenex.mk count components) := by simp [places, secondLeft]
        exact List.mem_toFinset.mpr (grouping.closed member firstList
          (Linked.LinkedIn.single (grouping.mem_items member firstList) secondPlaces ⟨key, firstKeys, secondKeys⟩))
      · exact absurd inSecondKeys (rightMentions second (by omega) key)
  refine ⟨pLive, ?_, isGroup, ?_⟩
  · show isReplicated block (placeValue block _ (components.length + index)) = true
    rw [pValue, isReplicated_rename]
    simp [isReplicated]
  -- the copy test: the group's copy is the molecule, read past the others
  show CopyTest block (canonicalOf block) count
    (placeValue block (components ++ entries.map (rename (shiftAbove 0 count))) (components.length + index))
    (asGroup (allowedFor count (placeValue block (components ++ entries.map (rename (shiftAbove 0 count)))
      (components.length + index))) count (placeValue block (components ++ entries.map (rename (shiftAbove 0 count))))
      (group.toFinset.sort (· ≤ ·)))
  have allowedAll : allowedFor count (placeValue block (components ++ entries.map (rename (shiftAbove 0 count)))
      (components.length + index)) = List.range count := by
    unfold allowedFor
    apply List.filter_eq_self.mpr
    intro restriction inRange
    rw [pValue, mentions_lift_false (List.mem_range.mp inRange)]
    rfl
  set items := group.toFinset.sort (· ≤ ·) with itemsIs
  have itemsNodup : items.Nodup := Finset.sort_nodup _ _
  have itemsPerm : items.Perm group := by
    rw [List.perm_ext_iff_of_nodup itemsNodup groupNodup]
    intro place
    rw [itemsIs, Finset.mem_sort, List.mem_toFinset]
  have itemsValues : items.map (placeValue block (components ++ entries.map (rename (shiftAbove 0 count)))) =
      items.map (placeValue block components) :=
    List.map_congr_left fun place inItems => leftValue place (groupInside place (itemsPerm.subset inItems))
  have groupIs : asGroup (List.range count) count
      (placeValue block (components ++ entries.map (rename (shiftAbove 0 count)))) items =
        ⟨usedOf ⟨count, items.map (placeValue block components)⟩, items.map (placeValue block components)⟩ := by
    unfold asGroup
    rw [restrictionsOf_range, itemsValues]
  rw [allowedAll, groupIs]
  unfold CopyTest
  rw [copyOf_eq_rename_prune, pValue]
  set used := usedOf ⟨count, items.map (placeValue block components)⟩ with usedIs
  set shift := fun position => position + (count - used.length) with shiftIs
  have shiftInjective : Function.Injective shift := fun first second same => by
    simp only [shiftIs] at same
    omega
  have usedNodup : used.Nodup := List.nodup_range.filter _
  have usedBelow : ∀ restriction ∈ used, restriction < count := fun restriction inUsed => by
    rw [usedIs] at inUsed
    unfold usedOf at inUsed
    exact List.mem_range.mp (List.mem_filter.mp inUsed).1
  have argumentIs : argumentOf? (rename (shiftAbove 0 count) (Pattern.apply block.replicate [canonical])) =
      rename (shiftAbove 0 count) canonical := by
    rw [rename_apply]
    rfl
  have renamedArgument : rename (Prenex.groupIndex count (outsideOf count used)) (rename (shiftAbove 0 count) canonical) =
      rename shift canonical := by
    rw [rename_comp]
    apply rename_congr
    intro position _
    simp only [Function.comp_apply, shiftAbove, Nat.not_lt_zero, if_false, shiftIs]
    rw [groupIndex_above (by omega), outsideOf_length usedNodup usedBelow]
    omega
  rw [argumentIs, renamedArgument]
  -- canonical forms of the group's block
  have restrictedAtomic : (restrictTo block ⟨count, components⟩ group).Atomic block.toBlock := by
    intro component inComponents
    obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp inComponents
    exact atomic _ (placeValue_mem (groupInside place inGroup))
  have itemsAtomic : (Prenex.mk count (items.map (placeValue block components))).Atomic block.toBlock := by
    intro component inComponents
    obtain ⟨place, inItems, rfl⟩ := List.mem_map.mp inComponents
    exact atomic _ (placeValue_mem (groupInside place (itemsPerm.subset inItems)))
  have canonicalFixed : canonicalOf block canonical = canonical := by
    rw [canonicalIs, canonicalOf_toPattern (normal_atomic fresh restrictFresh restrictedAtomic)
      (used_normal fresh restrictFresh _ restrictedAtomic), normal_normal fresh restrictFresh restrictedAtomic]
  have prunedIs : canonicalOf block (Prenex.toPattern block.toBlock
      (Prenex.mk count (items.map (placeValue block components))).prune) = canonical := by
    rw [canonicalOf_toPattern (prune_atomic itemsAtomic) (used_prune _), normal_prune fresh restrictFresh _ itemsAtomic,
      normal_perm fresh restrictFresh (itemsPerm.map _) itemsAtomic]
    rfl
  have below := below_all fresh restrictFresh (max (size (Prenex.toPattern block.toBlock
    (Prenex.mk count (items.map (placeValue block components))).prune)) (size canonical) + 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (below.renamed _ _ (Nat.lt_succ_of_le (le_max_left _ _)) (Nat.lt_succ_of_le (le_max_right _ _)) shift
      shiftInjective).mpr (prunedIs.trans canonicalFixed.symm)
  · rw [below.shape _ (Nat.lt_succ_of_le (le_max_left _ _)) shift shiftInjective, prunedIs]
    exact notLone
  · intro component inComponents replicated
    rw [(below_all fresh restrictFresh (size canonical + 1)).sized canonical (Nat.lt_succ_self _)
      (shiftAbove 0 count) (fun first second same => by
        simp only [shiftAbove, Nat.not_lt_zero, if_false] at same
        omega), canonicalFixed]
    have inRestricted : component ∈ (restrictTo block ⟨count, components⟩ group).components := by
      obtain ⟨place, inItems, rfl⟩ := List.mem_map.mp inComponents
      exact List.mem_map_of_mem (itemsPerm.subset inItems)
    exact size_argument_lt multisetFresh fresh restrictFresh restrictedAtomic inRestricted replicated
  · intro restriction below mentioned
    rw [mentions_lift_false below] at mentioned
    cases mentioned

omit multisetFresh fresh restrictFresh in
theorem build_pairwise_disjoint {keys : Nat → List Nat} {items : List Nat} (nodup : items.Nodup) :
    (Linked.build keys items).Pairwise List.Disjoint := by
  have grouping := Linked.build_grouping (keys := keys) items
  have flatNodup : (Linked.build keys items).flatten.Nodup := grouping.perm.nodup_iff.mpr nodup
  exact (List.nodup_flatten.mp flatNodup).2

/-- **Removing the classes that are no replications, each a copy of its replicated molecule beside the block.** -/
theorem removes_molecules {count : Nat} {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock) :
    ∀ (pending : List (List Nat)), pending.Pairwise List.Disjoint →
      (∀ group ∈ pending, group ∈ Linked.build (keysAt block ⟨count, components⟩) (places (Prenex.mk count components))) →
      ∀ live : Finset Nat,
        (∀ group ∈ pending, ∀ place ∈ group, place ∈ live) →
        (∀ offset < ((Linked.build (keysAt block ⟨count, components⟩) (places (Prenex.mk count components))).map
          (entryOf block ⟨count, components⟩)).length, components.length + offset ∈ live) →
        (blockSystem block ⟨count, components ++
          ((Linked.build (keysAt block ⟨count, components⟩) (places (Prenex.mk count components))).map
            (entryOf block ⟨count, components⟩)).map (rename (shiftAbove 0 count))⟩).Removes live
          (live \ ((pending.filter fun group => !isReplicated block (Prenex.toPattern block.toBlock
            (normal block (restrictTo block ⟨count, components⟩ group)))).flatten).toFinset)
  | [], _, _, live, _, _ => by
      simp only [List.filter_nil, List.flatten_nil, List.toFinset_nil, Finset.sdiff_empty]
      exact .refl
  | group :: rest, disjoint, members, live, groupsLive, entriesLive => by
      set groups := Linked.build (keysAt block ⟨count, components⟩) (places (Prenex.mk count components))
      obtain ⟨separate, restDisjoint⟩ := List.pairwise_cons.mp disjoint
      have groupMember := members group List.mem_cons_self
      have grouping := Linked.build_grouping (keys := keysAt block ⟨count, components⟩) (places (Prenex.mk count components))
      have groupInside : ∀ place ∈ group, place < components.length := fun place inGroup => by
        have := grouping.mem_items groupMember inGroup
        simpa [places] using this
      by_cases notLone : isReplicated block (Prenex.toPattern block.toBlock
          (normal block (restrictTo block ⟨count, components⟩ group))) = false
      · have filterIs : ((group :: rest).filter fun group => !isReplicated block (Prenex.toPattern block.toBlock
            (normal block (restrictTo block ⟨count, components⟩ group)))) =
            group :: rest.filter fun group => !isReplicated block (Prenex.toPattern block.toBlock
              (normal block (restrictTo block ⟨count, components⟩ group))) := by
          rw [List.filter_cons_of_pos (by simp [notLone])]
        rw [filterIs, List.flatten_cons, List.toFinset_append]
        have sdiffIs : ∀ first second : Finset Nat, live \ (first ∪ second) = (live \ first) \ second := by
          intro first second
          ext place
          simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
          tauto
        rw [sdiffIs]
        -- the group is a copy of its entry
        have indexBelow : groups.idxOf group < (groups.map (entryOf block ⟨count, components⟩)).length := by
          rw [List.length_map]
          exact List.idxOf_lt_length_of_mem groupMember
        have entryAt : (groups.map (entryOf block ⟨count, components⟩))[groups.idxOf group] =
            entryOf block ⟨count, components⟩ group := by
          rw [List.getElem_map, List.getElem_idxOf]
        have isCopy := isCopy_molecule multisetFresh fresh restrictFresh atomic groupMember notLone indexBelow entryAt
          (fun place inGroup => groupsLive group List.mem_cons_self place inGroup) (entriesLive _ indexBelow)
        refine .step (copied := group.toFinset) isCopy ?_
        refine removes_molecules atomic rest restDisjoint (fun other inRest => members other (List.mem_cons_of_mem _ inRest))
          (live \ group.toFinset) (fun other inRest place inOther => ?_) (fun offset below => ?_)
        · refine Finset.mem_sdiff.mpr ⟨groupsLive other (List.mem_cons_of_mem _ inRest) place inOther, fun inGroup => ?_⟩
          exact separate other inRest (List.mem_toFinset.mp inGroup) inOther
        · refine Finset.mem_sdiff.mpr ⟨entriesLive offset below, fun inGroup => ?_⟩
          have := groupInside _ (List.mem_toFinset.mp inGroup)
          omega
      · have filterIs : ((group :: rest).filter fun group => !isReplicated block (Prenex.toPattern block.toBlock
            (normal block (restrictTo block ⟨count, components⟩ group)))) =
            rest.filter fun group => !isReplicated block (Prenex.toPattern block.toBlock
              (normal block (restrictTo block ⟨count, components⟩ group))) := by
          rw [List.filter_cons_of_neg (by simpa using notLone)]
        rw [filterIs]
        exact removes_molecules atomic rest restDisjoint (fun other inRest => members other (List.mem_cons_of_mem _ inRest))
          live (fun other inRest => groupsLive other (List.mem_cons_of_mem _ inRest)) entriesLive

omit multisetFresh in
/-- Replicated duplicates of components of a block add nothing to its canonical form. -/
theorem normal_append_duplicates {count : Nat} {components : List Pattern} :
    ∀ (duplicates : List Pattern), (∀ duplicate ∈ duplicates, duplicate ∈ components) →
      (∀ duplicate ∈ duplicates, isReplicated block duplicate = true) →
      (Prenex.mk count (duplicates ++ components)).Atomic block.toBlock →
      normal block ⟨count, duplicates ++ components⟩ = normal block ⟨count, components⟩
  | [], _, _, _ => rfl
  | duplicate :: rest, inComponents, replicated, atomic => by
      have consAtomic : (Prenex.mk count (duplicate :: (rest ++ components))).Atomic block.toBlock := atomic
      rw [List.cons_append, normal_duplicate fresh restrictFresh _ count duplicate (rest ++ components)
        (Nat.lt_succ_self _) consAtomic
        (List.mem_append_right _ (inComponents duplicate List.mem_cons_self)) (replicated duplicate List.mem_cons_self)]
      exact normal_append_duplicates rest (fun other member => inComponents other (List.mem_cons_of_mem _ member))
        (fun other member => replicated other (List.mem_cons_of_mem _ member))
        (fun other member => atomic other (List.mem_cons_of_mem _ member))

omit multisetFresh in
/-- **A lone replication using no restriction enters as itself, read again past the block's restrictions.** -/
theorem entryOf_lone {form : Prenex} (atomic : form.Atomic block.toBlock) {place : Nat}
    (inside : place < form.components.length) (alone : keysAt block form place = []) :
    entryOf block form [place] =
      bang block (recanon block (rename (Prenex.groupIndex form.count []) (placeValue block form.components place))) := by
  have noMention : ∀ index < form.count, mentions index (placeValue block form.components place) = false := by
    intro index below
    by_contra mentioned
    have inKeys : index ∈ keysAt block form place := by
      simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range]
      exact ⟨below, by simpa using mentioned⟩
    rw [alone] at inKeys
    cases inKeys
  have usedNil : usedOf (Prenex.mk form.count [placeValue block form.components place]) = [] := by
    unfold usedOf
    apply List.filter_eq_nil_iff.mpr
    intro index member
    simp [noMention index (List.mem_range.mp member)]
  have singleAtomic : (Prenex.mk form.count [placeValue block form.components place]).Atomic block.toBlock :=
    fun component member => by
      rw [List.mem_singleton] at member
      subst member
      exact atomic _ (placeValue_mem inside)
  have renamedAtomic : decompose block.toBlock (rename (Prenex.groupIndex form.count []) (placeValue block form.components place)) =
      Prenex.atom (rename (Prenex.groupIndex form.count []) (placeValue block form.components place)) :=
    atomic_rename (singleAtomic _ List.mem_cons_self) _
  have canonicalIs := canonicalOf_atom (block := block) renamedAtomic
  unfold canonicalOf at canonicalIs
  rw [renamedAtomic] at canonicalIs
  unfold entryOf restrictTo
  simp only [List.map_cons, List.map_nil]
  rw [← normal_prune fresh restrictFresh _ singleAtomic, prune_eq, usedNil]
  simp only [List.length_nil, List.map_cons, List.map_nil]
  rw [show (Prenex.mk 0 [rename (Prenex.groupIndex form.count []) (placeValue block form.components place)]) =
    Prenex.atom (rename (Prenex.groupIndex form.count []) (placeValue block form.components place)) from rfl,
    canonicalIs]

/-- **A block beside its replicated molecules reads canonically as the replicated molecules alone**:
`P | !P = !P` on blocks. -/
theorem normal_par_replicatedOf {form : Prenex} (atomic : form.Atomic block.toBlock) :
    normal block (form.par ⟨0, replicatedOf block (canonicalOf block) form⟩) =
      normal block ⟨0, replicatedOf block (canonicalOf block) form⟩ := by
  obtain ⟨count, components⟩ := form
  rw [replicatedOf_eq_entries multisetFresh fresh restrictFresh atomic]
  set groups := Linked.build (keysAt block ⟨count, components⟩) (places (Prenex.mk count components)) with groupsIs
  set entries := groups.map (entryOf block ⟨count, components⟩) with entriesIs
  have grouping := Linked.build_grouping (keys := keysAt block ⟨count, components⟩) (places (Prenex.mk count components))
  have entriesReplicated : ∀ entry ∈ entries, isReplicated block entry = true := by
    intro entry member
    obtain ⟨group, _, rfl⟩ := List.mem_map.mp member
    exact isReplicated_bang _
  set lift := rename (shiftAbove 0 count) with liftIs
  have liftInjective : Function.Injective (shiftAbove 0 count) := fun first second same => by
    simp only [shiftAbove, Nat.not_lt_zero, if_false] at same
    omega
  have parIs : (Prenex.mk count components).par ⟨0, entries⟩ = ⟨count, components ++ entries.map lift⟩ := by
    simp only [Prenex.par, Nat.add_zero, Prenex.mk.injEq, true_and]
    congr 1
    · conv_rhs => rw [← List.map_id components]
      exact List.map_congr_left fun component _ => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero component 0
    · exact List.map_congr_left fun entry _ => liftBVars_eq_rename 0 count entry
  rw [parIs]
  -- the wide block
  have wideAtomic : (Prenex.mk count (components ++ entries.map lift)).Atomic block.toBlock := by
    intro component member
    rcases List.mem_append.mp member with inComponents | inEntries
    · exact atomic component inComponents
    · obtain ⟨entry, inEntry, rfl⟩ := List.mem_map.mp inEntries
      exact replicated_atomic fresh restrictFresh (by rw [liftIs, isReplicated_rename]; exact entriesReplicated entry inEntry)
  obtain ⟨wideLaws, wideBlind⟩ := lawful_all fresh restrictFresh wideAtomic
  have groupsDisjoint := build_pairwise_disjoint (keys := keysAt block ⟨count, components⟩) (places_nodup (Prenex.mk count components))
  have groupInside : ∀ group ∈ groups, ∀ place ∈ group, place < components.length := fun group member place inGroup => by
    have := grouping.mem_items member inGroup
    simpa [places] using this
  set removed := ((groups.filter fun group => !isReplicated block (Prenex.toPattern block.toBlock
    (normal block (restrictTo block ⟨count, components⟩ group)))).flatten).toFinset with removedIs
  have removedLeft : ∀ place ∈ removed, place < components.length := by
    intro place member
    simp only [removedIs, List.mem_toFinset, List.mem_flatten, List.mem_filter] at member
    obtain ⟨group, ⟨inGroups, _⟩, inGroup⟩ := member
    exact groupInside group inGroups place inGroup
  have removes := removes_molecules multisetFresh fresh restrictFresh atomic groups groupsDisjoint (fun _ member => member)
    (places (Prenex.mk count (components ++ entries.map lift))).toFinset
    (fun group member place inGroup => by
      have := groupInside group member place inGroup
      simp [places]
      omega)
    (fun offset below => by
      simp only [List.length_map] at below
      simp [places, entriesIs]
      omega)
  -- the kept places: the lone ones, then the entries
  set lone := (List.range components.length).filter fun place => !decide (place ∈ removed) with loneIs
  set kept := lone ++ (List.range entries.length).map (components.length + ·) with keptIs
  have keptNodup : kept.Nodup := by
    refine List.nodup_append.mpr ⟨List.nodup_range.filter _, List.nodup_range.map fun a b same => by omega, ?_⟩
    intro first inLone second inEntries same
    obtain ⟨offset, _, rfl⟩ := List.mem_map.mp inEntries
    have := List.mem_range.mp (List.mem_filter.mp inLone).1
    omega
  have keptInside : ∀ place ∈ kept, place < (components ++ entries.map lift).length := by
    intro place member
    simp only [List.length_append, List.length_map]
    rcases List.mem_append.mp member with inLone | inEntries
    · have := List.mem_range.mp (List.mem_filter.mp inLone).1
      omega
    · obtain ⟨offset, below, rfl⟩ := List.mem_map.mp inEntries
      have := List.mem_range.mp below
      omega
  have keptSet : kept.toFinset = (places (Prenex.mk count (components ++ entries.map lift))).toFinset \ removed := by
    ext place
    simp only [keptIs, loneIs, List.toFinset_append, Finset.mem_union, List.mem_toFinset, List.mem_filter,
      List.mem_range, List.mem_map, Finset.mem_sdiff, places, List.length_append, List.length_map,
      Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro (⟨below, notRemoved⟩ | ⟨offset, below, rfl⟩)
      · exact ⟨by omega, notRemoved⟩
      · exact ⟨by omega, fun inRemoved => by have := removedLeft _ inRemoved; omega⟩
    · rintro ⟨below, notRemoved⟩
      by_cases left : place < components.length
      · exact .inl ⟨left, notRemoved⟩
      · exact .inr ⟨place - components.length, by omega, by omega⟩
  have restricted := normal_restrict wideLaws wideBlind keptNodup keptInside (by rw [keptSet]; exact removes)
  rw [← restricted]
  -- the kept components: the lone replications, then the entries renamed past the block's restrictions
  have keptValues : kept.map (placeValue block (components ++ entries.map lift)) =
      lone.map (placeValue block components) ++ entries.map lift := by
    rw [keptIs, List.map_append]
    congr 1
    · refine List.map_congr_left fun place member => ?_
      exact placeValue_append_left (List.mem_range.mp (List.mem_filter.mp member).1)
    · rw [List.map_map]
      have liftedLength : (entries.map lift).length = entries.length := List.length_map _
      conv_rhs => rw [← map_range_placeValue (block := block) (entries.map lift), liftedLength]
      refine List.map_congr_left fun offset member => ?_
      simp only [Function.comp_apply]
      exact placeValue_append_right (by rw [liftedLength]; exact List.mem_range.mp member)
  show normal block ⟨count, kept.map (placeValue block (components ++ entries.map lift))⟩ = _
  rw [keptValues]
  -- each lone component is alike to its entry renamed past the restrictions
  have loneFacts : ∀ place ∈ lone, keysAt block ⟨count, components⟩ place = [] ∧
      isReplicated block (placeValue block components place) = true ∧ [place] ∈ groups := by
    intro place member
    obtain ⟨inRange, notRemoved⟩ := List.mem_filter.mp member
    have below := List.mem_range.mp inRange
    have inPlaces : place ∈ places (Prenex.mk count components) := by simp [places, below]
    obtain ⟨group, inGroups, inGroup⟩ := grouping.exists_group inPlaces
    have replicatedGroup : isReplicated block (Prenex.toPattern block.toBlock
        (normal block (restrictTo block ⟨count, components⟩ group))) = true := by
      by_contra notReplicated
      have inRemoved : place ∈ removed := by
        simp only [removedIs, List.mem_toFinset, List.mem_flatten, List.mem_filter]
        exact ⟨group, ⟨inGroups, by simpa using notReplicated⟩, inGroup⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at notRemoved
      exact notRemoved inRemoved
    obtain ⟨single, rfl, alone, replicated⟩ := lone_of_replicated fresh restrictFresh atomic inGroups replicatedGroup
    rw [List.mem_singleton] at inGroup
    subst inGroup
    exact ⟨alone, replicated, inGroups⟩
  have loneAlike : List.Forall₂ (AlikeR block) (lone.map (placeValue block components))
      (lone.map fun place => lift (entryOf block ⟨count, components⟩ [place])) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun place member => ?_
    obtain ⟨alone, replicated, _⟩ := loneFacts place member
    have below := List.mem_range.mp (List.mem_filter.mp member).1
    rw [entryOf_lone fresh restrictFresh atomic below alone,
      bang_of_replicated (by rw [isReplicated_recanon, isReplicated_rename]; exact replicated)]
    have back : placeValue block components place =
        lift (rename (Prenex.groupIndex count []) (placeValue block components place)) := by
      rw [liftIs, rename_comp]
      conv_lhs => rw [← rename_id (placeValue block components place)]
      apply rename_congr
      intro index free
      have far : count ≤ index := by
        by_contra near
        have inKeys : index ∈ keysAt block ⟨count, components⟩ place := by
          simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range]
          exact ⟨by omega, (mentions_iff _ _).mpr free⟩
        rw [alone] at inKeys
        cases inKeys
      simp only [Function.comp_apply, id, shiftAbove, Nat.not_lt_zero, if_false]
      rw [groupIndex_above far, List.length_nil]
      omega
    conv_lhs => rw [back]
    exact (alike_recanon_all fresh restrictFresh _).rename liftInjective
  have duplicatesAtomic : (Prenex.mk count ((lone.map fun place => lift (entryOf block ⟨count, components⟩ [place])) ++
      entries.map lift)).Atomic block.toBlock := by
    intro component member
    rcases List.mem_append.mp member with inLone | inEntries
    · obtain ⟨place, _, rfl⟩ := List.mem_map.mp inLone
      exact replicated_atomic fresh restrictFresh (by rw [liftIs, isReplicated_rename]; exact isReplicated_bang _)
    · exact wideAtomic component (List.mem_append_right _ inEntries)
  have loneAtomic : (Prenex.mk count (lone.map (placeValue block components) ++ entries.map lift)).Atomic block.toBlock := by
    intro component member
    rcases List.mem_append.mp member with inLone | inEntries
    · obtain ⟨place, inLone', rfl⟩ := List.mem_map.mp inLone
      exact atomic _ (placeValue_mem (List.mem_range.mp (List.mem_filter.mp inLone').1))
    · exact wideAtomic component (List.mem_append_right _ inEntries)
  rw [normal_similar_all fresh restrictFresh (first := ⟨count, lone.map (placeValue block components) ++ entries.map lift⟩)
    (second := ⟨count, (lone.map fun place => lift (entryOf block ⟨count, components⟩ [place])) ++ entries.map lift⟩)
    ⟨rfl, List.range count, _, List.Perm.refl _, ?similar, List.Perm.refl _⟩ loneAtomic duplicatesAtomic]
  case similar =>
    show List.Forall₂ (AlikeR block) ((lone.map (placeValue block components) ++ entries.map lift).map
      (rename (Prenex.permute count (List.range count)))) _
    rw [permute_range, show rename id = (id : Pattern → Pattern) from funext rename_id, List.map_id]
    exact List.rel_append loneAlike (List.forall₂_same.mpr fun component _ => AlikeR.refl component)
  rw [normal_append_duplicates fresh restrictFresh _
    (fun duplicate member => by
      obtain ⟨place, inLone, rfl⟩ := List.mem_map.mp member
      exact List.mem_map_of_mem (List.mem_map_of_mem (loneFacts place inLone).2.2))
    (fun duplicate member => by
      obtain ⟨place, _, rfl⟩ := List.mem_map.mp member
      rw [liftIs, isReplicated_rename]
      exact isReplicated_bang _) duplicatesAtomic]
  -- the entries renamed past unused restrictions are the entries
  have entriesAtomic : (Prenex.mk count (entries.map lift)).Atomic block.toBlock :=
    fun component member => wideAtomic component (List.mem_append_right _ member)
  rw [← normal_prune fresh restrictFresh _ entriesAtomic]
  have usedNil : usedOf (Prenex.mk count (entries.map lift)) = [] := by
    unfold usedOf
    apply List.filter_eq_nil_iff.mpr
    intro index member
    simp only [List.any_map, Function.comp_def, Bool.not_eq_true, List.any_eq_false]
    intro entry _
    rw [liftIs]
    exact mentions_lift_false (List.mem_range.mp member) entry
  rw [prune_eq, usedNil]
  simp only [List.length_nil, List.map_map]
  congr 2
  conv_rhs => rw [← List.map_id entries]
  exact List.map_congr_left fun entry _ => rename_lower_lift count entry

end Unfold

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
