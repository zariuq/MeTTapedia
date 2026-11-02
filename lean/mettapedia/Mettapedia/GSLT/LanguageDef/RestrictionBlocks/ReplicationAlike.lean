import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRenamed

/-!
# Blocks of alike components

A pattern's free names lie below a bound (`exists_freeBound`), so a renaming injective on the free names of some
patterns renames them as an injective renaming does (`exists_injective_on`), and alike components stay alike under
it (`AlikeR.rename_on`).

Replacing a block's components by alike ones keeps its copy tests (`copyTest_alike`), so its absorption system
(`alike_iso`) and its canonical form (`normal_alike`), given the canonical form below the blocks' size.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_bvar freeIn_apply freeIn_lambda freeIn_multiLambda
  freeIn_subst freeIn_collection liftIndex)

/-! ## Renamings agreeing with an injective one on finitely many names -/

theorem exists_bound_of_list {α : Type} (property : α → Nat → Prop)
    (mono : ∀ item first second, first ≤ second → property item first → property item second) :
    ∀ (items : List α), (∀ item ∈ items, ∃ bound, property item bound) → ∃ bound, ∀ item ∈ items, property item bound
  | [], _ => ⟨0, fun _ member => nomatch member⟩
  | item :: rest, each => by
      obtain ⟨first, holds⟩ := each item List.mem_cons_self
      obtain ⟨second, holdsRest⟩ := exists_bound_of_list property mono rest fun other member =>
        each other (List.mem_cons_of_mem _ member)
      refine ⟨max first second, fun other member => ?_⟩
      rcases List.mem_cons.mp member with rfl | inRest
      · exact mono _ _ _ (le_max_left _ _) holds
      · exact mono _ _ _ (le_max_right _ _) (holdsRest other inRest)

/-- **Every pattern has its free names below some bound.** -/
theorem exists_freeBound (pattern : Pattern) : ∃ bound, ∀ index, FreeIn index pattern → index < bound := by
  induction pattern using Pattern.inductionOn with
  | hbvar other => exact ⟨other + 1, fun index free => by rw [freeIn_bvar] at free; omega⟩
  | hfvar _ => exact ⟨0, fun index free => by cases free⟩
  | happly _ arguments recurse =>
      obtain ⟨bound, holds⟩ := exists_bound_of_list (fun pattern bound => ∀ index, FreeIn index pattern → index < bound)
        (fun _ _ _ le holds index free => lt_of_lt_of_le (holds index free) le) arguments recurse
      exact ⟨bound, fun index free => by
        obtain ⟨argument, member, free'⟩ := freeIn_apply.mp free
        exact holds argument member index free'⟩
  | hlambda _ body recurse =>
      obtain ⟨bound, holds⟩ := recurse
      exact ⟨bound, fun index free => by have := holds _ (freeIn_lambda.mp free); omega⟩
  | hmultiLambda arity _ body recurse =>
      obtain ⟨bound, holds⟩ := recurse
      exact ⟨bound, fun index free => by have := holds _ (freeIn_multiLambda.mp free); omega⟩
  | hsubst body replacement recurseBody recurseReplacement =>
      obtain ⟨first, holdsBody⟩ := recurseBody
      obtain ⟨second, holdsReplacement⟩ := recurseReplacement
      refine ⟨first + second, fun index free => ?_⟩
      rcases freeIn_subst.mp free with free' | free'
      · have := holdsBody _ free'
        omega
      · have := holdsReplacement _ free'
        omega
  | hcollection _ elements _ recurse =>
      obtain ⟨bound, holds⟩ := exists_bound_of_list (fun pattern bound => ∀ index, FreeIn index pattern → index < bound)
        (fun _ _ _ le holds index free => lt_of_lt_of_le (holds index free) le) elements recurse
      exact ⟨bound, fun index free => by
        obtain ⟨element, member, free'⟩ := freeIn_collection.mp free
        exact holds element member index free'⟩

/-- **A renaming injective on some names below a bound agrees there with an injective renaming.** -/
theorem exists_injective_agree (relabel : Nat → Nat) (bound : Nat) (inside : Nat → Prop) [DecidablePred inside]
    (injOn : ∀ first second, first < bound → inside first → second < bound → inside second →
      relabel first = relabel second → first = second) :
    ∃ relabel', Function.Injective relabel' ∧ ∀ index < bound, inside index → relabel' index = relabel index := by
  set top := ((List.range bound).map relabel).sum + 1 with topIs
  have bigger : ∀ index < bound, relabel index < top := fun index below => by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := relabel) (List.mem_range.mpr below))
    omega
  refine ⟨fun index => if index < bound ∧ inside index then relabel index else top + index, ?_,
    fun index below holds => if_pos ⟨below, holds⟩⟩
  intro first second same
  simp only at same
  by_cases firstIn : first < bound ∧ inside first <;> by_cases secondIn : second < bound ∧ inside second
  · rw [if_pos firstIn, if_pos secondIn] at same
    exact injOn first second firstIn.1 firstIn.2 secondIn.1 secondIn.2 same
  · rw [if_pos firstIn, if_neg secondIn] at same
    have := bigger first firstIn.1
    omega
  · rw [if_neg firstIn, if_pos secondIn] at same
    have := bigger second secondIn.1
    omega
  · rw [if_neg firstIn, if_neg secondIn] at same
    omega

/-- **A renaming injective on the free names of some patterns renames them as an injective renaming does.** -/
theorem exists_injective_on (patterns : List Pattern) (relabel : Nat → Nat) (inside : Nat → Prop)
    [DecidablePred inside] (holds : ∀ pattern ∈ patterns, ∀ index, FreeIn index pattern → inside index)
    (injOn : ∀ first second, inside first → inside second → relabel first = relabel second → first = second) :
    ∃ relabel', Function.Injective relabel' ∧ ∀ pattern ∈ patterns, rename relabel' pattern = rename relabel pattern := by
  obtain ⟨bound, bounded⟩ := exists_bound_of_list (fun pattern bound => ∀ index, FreeIn index pattern → index < bound)
    (fun _ _ _ le holds index free => lt_of_lt_of_le (holds index free) le) patterns
    fun pattern _ => exists_freeBound pattern
  obtain ⟨relabel', injective, agree⟩ := exists_injective_agree relabel bound inside
    fun first second _ firstIn _ secondIn same => injOn first second firstIn secondIn same
  exact ⟨relabel', injective, fun pattern member => rename_congr pattern fun index free =>
    agree index (bounded pattern member index free) (holds pattern member index free)⟩

/-- **Alike components stay alike under a renaming injective on their free names.** -/
theorem AlikeR.rename_on {block : ReplicationBlock} {first second : Pattern} (alike : AlikeR block first second)
    (relabel : Nat → Nat)
    (injOn : ∀ a b, FreeIn a first → FreeIn b first → relabel a = relabel b → a = b) :
    AlikeR block (RestrictionBlocks.rename relabel first) (RestrictionBlocks.rename relabel second) := by
  obtain ⟨relabel', injective, agree⟩ := exists_injective_on [first, second] relabel
    (fun index => mentions index first = true)
    (fun pattern member index free => by
      rcases List.mem_cons.mp member with rfl | inRest
      · exact (mentions_iff _ _).mpr free
      · rw [List.mem_singleton] at inRest
        subst inRest
        exact (mentions_iff _ _).mpr ((alike.1 index).mpr free))
    fun a b aIn bIn same => injOn a b ((mentions_iff _ _).mp aIn) ((mentions_iff _ _).mp bIn) same
  rw [← agree first List.mem_cons_self, ← agree second (List.mem_cons_of_mem _ (List.mem_singleton_self _))]
  exact alike.rename injective

/-! ## Replacing components by alike ones -/

variable {block : ReplicationBlock}

theorem placeValue_alike {first second : List Pattern} (alike : List.Forall₂ (AlikeR block) first second)
    {place : Nat} (inside : place < first.length) :
    AlikeR block (placeValue block first place) (placeValue block second place) := by
  have inside' : place < second.length := alike.length_eq ▸ inside
  unfold placeValue
  rw [List.getD_eq_getElem _ _ inside, List.getD_eq_getElem _ _ inside']
  exact alike.get inside inside'

theorem mentions_alike {first second : Pattern} (alike : AlikeR block first second) (index : Nat) :
    mentions index second = mentions index first :=
  Bool.eq_iff_iff.mpr (by rw [mentions_iff, mentions_iff]; exact (alike.1 index).symm)

theorem allowedFor_alike {count : Nat} {first second : Pattern} (alike : AlikeR block first second) :
    allowedFor count second = allowedFor count first := by
  unfold allowedFor
  exact List.filter_congr fun index _ => by rw [mentions_alike alike]

theorem restrictionsOf_alike {allowed : List Nat} {count : Nat} {first second : Nat → Pattern} {items : List Nat}
    (alike : ∀ item ∈ items, AlikeR block (first item) (second item)) :
    restrictionsOf allowed count second items = restrictionsOf allowed count first items := by
  unfold restrictionsOf
  refine List.filter_congr fun index _ => Bool.eq_iff_iff.mpr ?_
  simp only [List.any_eq_true]
  refine exists_congr fun item => and_congr_right fun member => ?_
  have keysSame : throughKeys allowed count second item = throughKeys allowed count first item := by
    unfold throughKeys usedRestrictions
    congr 1
    exact List.filter_congr fun index' _ => mentions_alike (alike item member) index'
  rw [keysSame]

/-- A renumbering keeping some restrictions is injective on them and the names outside the block. -/
theorem groupIndex_injOn {count : Nat} {kept : List Nat} {first second : Nat}
    (firstIn : first < count → first ∈ kept) (secondIn : second < count → second ∈ kept)
    (same : Prenex.groupIndex count kept first = Prenex.groupIndex count kept second) : first = second := by
  by_cases firstBelow : first < count <;> by_cases secondBelow : second < count
  · rw [groupIndex_below firstBelow, groupIndex_below secondBelow] at same
    exact SplitParts.eq_of_idxOf_eq (firstIn firstBelow) (secondIn secondBelow) same
  · rw [groupIndex_below firstBelow, groupIndex_above (Nat.le_of_not_lt secondBelow)] at same
    have := List.idxOf_lt_length_of_mem (firstIn firstBelow)
    omega
  · rw [groupIndex_above (Nat.le_of_not_lt firstBelow), groupIndex_below secondBelow] at same
    have := List.idxOf_lt_length_of_mem (secondIn secondBelow)
    omega
  · rw [groupIndex_above (Nat.le_of_not_lt firstBelow), groupIndex_above (Nat.le_of_not_lt secondBelow)] at same
    omega

theorem forall₂_map_alike {items : List Nat} {first second : Nat → Pattern} {relabel : Nat → Nat}
    (injective : Function.Injective relabel) (alike : ∀ item ∈ items, AlikeR block (first item) (second item)) :
    List.Forall₂ (AlikeR block) ((items.map first).map (rename relabel)) ((items.map second).map (rename relabel)) := by
  simp only [List.map_map]
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun item member => (alike item member).rename injective

/-- **Alike components give alike copy tests.** -/
theorem copyTest_alike {count : Nat} {first second : List Pattern} (alike : List.Forall₂ (AlikeR block) first second)
    {bound : Nat} (below : Below block bound) (firstSmall : (Prenex.mk count first).mass ≤ bound)
    (secondSmall : (Prenex.mk count second).mass ≤ bound)
    (firstAtomic : ∀ component ∈ first, decompose block.toBlock component = Prenex.atom component)
    (secondAtomic : ∀ component ∈ second, decompose block.toBlock component = Prenex.atom component)
    {place : Nat} {items : List Nat} (nodup : (place :: items).Nodup)
    (inRange : ∀ member ∈ place :: items, member < first.length)
    (replicated : isReplicated block (placeValue block first place) = true) :
    CopyTest block (canonicalOf block) count (placeValue block second place)
        (asGroup (allowedFor count (placeValue block second place)) count (placeValue block second) items) ↔
      CopyTest block (canonicalOf block) count (placeValue block first place)
        (asGroup (allowedFor count (placeValue block first place)) count (placeValue block first) items) := by
  have lengthEq := alike.length_eq
  have inRange' : ∀ member ∈ place :: items, member < second.length := fun member inList =>
    lengthEq ▸ inRange member inList
  have placeAlike := placeValue_alike alike (inRange place List.mem_cons_self)
  have itemsAlike : ∀ item ∈ items, AlikeR block (placeValue block first item) (placeValue block second item) :=
    fun item inItems => placeValue_alike alike (inRange item (List.mem_cons_of_mem _ inItems))
  have replicated' : isReplicated block (placeValue block second place) = true := placeAlike.2.1 ▸ replicated
  set value := placeValue block first with valueIs
  set value' := placeValue block second with value'Is
  rw [allowedFor_alike placeAlike]
  unfold CopyTest asGroup
  rw [restrictionsOf_alike itemsAlike]
  set restrictions := restrictionsOf (allowedFor count (value place)) count value items with restrictionsIs
  -- the weights of the two groups
  have weights : sizeList ((place :: items).map value) ≤ sizeList first := sizeList_places_le nodup inRange
  have weights' : sizeList ((place :: items).map value') ≤ sizeList second := sizeList_places_le nodup inRange'
  simp only [List.map_cons, sizeList] at weights weights'
  obtain ⟨argument, componentIs⟩ := replicated_shape replicated
  obtain ⟨argument', componentIs'⟩ := replicated_shape replicated'
  have componentSize : size (value place) = size argument + 1 := by rw [componentIs]; simp [size, sizeList]
  have componentSize' : size (value' place) = size argument' + 1 := by rw [componentIs']; simp [size, sizeList]
  have positive := size_pos argument
  have positive' := size_pos argument'
  simp only [Prenex.mass] at firstSmall secondSmall
  -- the copies read canonically alike
  have splitInjective : Function.Injective (Prenex.permute count (splitOrder count (outsideOf count restrictions)
      restrictions)) := permute_injective (outside_parts (restrictionsOf_nodup _ _ _ _)
        fun _ member => restrictionsOf_lt member).splitOrder_perm
  have copySame : canonicalOf block (copyOf block.toBlock count ⟨restrictions, items.map value'⟩) =
      canonicalOf block (copyOf block.toBlock count ⟨restrictions, items.map value⟩) := by
    set copied := copyBlock count restrictions (items.map value) with copiedIs
    set copied' := copyBlock count restrictions (items.map value') with copied'Is
    have atomicCopy : copied.Atomic block.toBlock := atomic_map_rename (fun member inMembers => by
      obtain ⟨item, inItems, rfl⟩ := List.mem_map.mp inMembers
      exact firstAtomic _ (placeValue_mem (inRange item (List.mem_cons_of_mem _ inItems)))) _
    have atomicCopy' : copied'.Atomic block.toBlock := atomic_map_rename (fun member inMembers => by
      obtain ⟨item, inItems, rfl⟩ := List.mem_map.mp inMembers
      exact secondAtomic _ (placeValue_mem (inRange' item (List.mem_cons_of_mem _ inItems)))) _
    have usedCopy : copied.Used := copyBlock_used
    have usedCopy' : copied'.Used := by
      have := copyBlock_used (allowed := allowedFor count (value place)) (count := count) (value := value')
        (items := items)
      rwa [restrictionsOf_alike itemsAlike] at this
    have massCopy : copied.mass < bound := by
      have := copyBlock_mass (allowed := allowedFor count (value place)) (count := count) (value := value)
        (items := items)
      rw [← restrictionsIs, ← copiedIs] at this
      omega
    have massCopy' : copied'.mass < bound := by
      have := copyBlock_mass (allowed := allowedFor count (value place)) (count := count) (value := value')
        (items := items)
      rw [restrictionsOf_alike itemsAlike, ← restrictionsIs, ← copied'Is] at this
      omega
    have similar : SimilarR block copied copied' := by
      refine ⟨rfl, List.range copied.count, copied'.components, List.Perm.refl _, ?_, List.Perm.refl _⟩
      have renameId : rename (Prenex.permute copied.count (List.range copied.count)) = (id : Pattern → Pattern) := by
        rw [permute_range]
        exact funext rename_id
      rw [renameId, List.map_id]
      exact forall₂_map_alike splitInjective itemsAlike
    unfold canonicalOf
    rw [copyOf_eq_copyBlock, copyOf_eq_copyBlock]
    simp only
    rw [decompose_toPattern atomicCopy' usedCopy', decompose_toPattern atomicCopy usedCopy,
      below.similar copied copied' massCopy massCopy' atomicCopy atomicCopy' similar]
  -- the replicated arguments read canonically alike
  have targetSame : canonicalOf block (rename (Prenex.groupIndex count (outsideOf count restrictions))
      (argumentOf? (value' place))) = canonicalOf block (rename (Prenex.groupIndex count (outsideOf count restrictions))
        (argumentOf? (value place))) := by
    have outside : ∀ pattern ∈ [argumentOf? (value place), argumentOf? (value' place)], ∀ index,
        FreeIn index pattern → index < count → index ∉ restrictions := by
      intro pattern member index free _ inRestrictions
      have mentioned : mentions index (value place) = true := by
        rcases List.mem_cons.mp member with rfl | inRest
        · rw [componentIs] at free ⊢
          exact (mentions_iff _ _).mpr (freeIn_apply.mpr ⟨argument, List.mem_singleton_self _, free⟩)
        · rw [List.mem_singleton] at inRest
          subst inRest
          rw [← mentions_alike placeAlike, componentIs']
          rw [componentIs'] at free
          exact (mentions_iff _ _).mpr (freeIn_apply.mpr ⟨argument', List.mem_singleton_self _, free⟩)
      have allowed := restrictionsOf_allowed inRestrictions
      simp only [allowedFor, List.mem_filter, List.mem_range, Bool.not_eq_true'] at allowed
      rw [mentioned] at allowed
      cases allowed.2
    obtain ⟨relabel', injective, agree⟩ := exists_injective_on [argumentOf? (value place), argumentOf? (value' place)]
      (Prenex.groupIndex count (outsideOf count restrictions)) (fun index => index < count → index ∉ restrictions)
      outside fun first second firstIn secondIn same => groupIndex_injOn
        (fun below => mem_outsideOf.mpr ⟨below, firstIn below⟩) (fun below => mem_outsideOf.mpr ⟨below, secondIn below⟩)
        same
    rw [← agree _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), ← agree _ List.mem_cons_self]
    exact (placeAlike.2.2.2 replicated relabel' injective).symm
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · rw [copySame, targetSame]
  · rw [copySame]
  · rw [List.forall_mem_map, List.forall_mem_map]
    have placeSize : size (canonicalOf block (argumentOf? (value' place))) =
        size (canonicalOf block (argumentOf? (value place))) := by
      have := placeAlike.2.2.2 replicated id Function.injective_id
      rw [rename_id, rename_id] at this
      rw [this]
    refine forall_congr' fun item => forall_congr' fun inItems => ?_
    have itemAlike := itemsAlike item inItems
    rw [← itemAlike.2.1, placeSize]
    constructor
    · intro smaller itemReplicated
      have := itemAlike.2.2.2 itemReplicated id Function.injective_id
      rw [rename_id, rename_id] at this
      rw [this]
      exact smaller itemReplicated
    · intro smaller itemReplicated
      have := itemAlike.2.2.2 itemReplicated id Function.injective_id
      rw [rename_id, rename_id] at this
      rw [← this]
      exact smaller itemReplicated
  · simp only [mentions_alike placeAlike, List.mem_map]
    constructor
    · rintro holds index below mentioned
      obtain ⟨_, ⟨item, inItems, rfl⟩, mentionedMember⟩ := holds index below mentioned
      exact ⟨value item, ⟨item, inItems, rfl⟩, by rw [← mentions_alike (itemsAlike item inItems)]; exact mentionedMember⟩
    · rintro holds index below mentioned
      obtain ⟨_, ⟨item, inItems, rfl⟩, mentionedMember⟩ := holds index below mentioned
      exact ⟨value' item, ⟨item, inItems, rfl⟩, by rw [mentions_alike (itemsAlike item inItems)]; exact mentionedMember⟩

/-- **The system of a block of alike components is the original's.** -/
theorem alike_iso {count : Nat} {first second : List Pattern} (alike : List.Forall₂ (AlikeR block) first second)
    {bound : Nat} (below : Below block bound) (firstSmall : (Prenex.mk count first).mass ≤ bound)
    (secondSmall : (Prenex.mk count second).mass ≤ bound)
    (firstAtomic : ∀ component ∈ first, decompose block.toBlock component = Prenex.atom component)
    (secondAtomic : ∀ component ∈ second, decompose block.toBlock component = Prenex.atom component) :
    (blockSystem block ⟨count, first⟩).Iso (blockSystem block ⟨count, second⟩) (places ⟨count, first⟩).toFinset id id
      where
  injective := fun _ _ _ _ same => same
  relabelInjective := Function.injective_id
  mentions := fun place placeLive => by
    have inside := List.mem_range.mp (List.mem_toFinset.mp placeLive)
    simp only [blockSystem, absorptionSystem, id, Finset.image_id]
    unfold usedRestrictions
    congr 1
    exact List.filter_congr fun index _ => mentions_alike (placeValue_alike alike inside) index
  replicated := fun place placeLive => by
    have inside := List.mem_range.mp (List.mem_toFinset.mp placeLive)
    simp only [blockSystem, absorptionSystem, id]
    rw [(placeValue_alike alike inside).2.1]
  copy := fun group groupInside place placeLive replicated notIn => by
    simp only [blockSystem, absorptionSystem, Finset.image_id, id]
    have placeRange := List.mem_range.mp (List.mem_toFinset.mp placeLive)
    exact copyTest_alike alike below firstSmall secondSmall firstAtomic secondAtomic
      (List.nodup_cons.mpr ⟨fun inSorted => notIn ((Finset.mem_sort _).mp inSorted), Finset.sort_nodup _ _⟩)
      (fun member inList => by
        rcases List.mem_cons.mp inList with rfl | inSorted
        · exact placeRange
        · exact List.mem_range.mp (List.mem_toFinset.mp (groupInside ((Finset.mem_sort _).mp inSorted))))
      replicated
  height := fun place placeLive replicated => by
    have inside := List.mem_range.mp (List.mem_toFinset.mp placeLive)
    simp only [blockSystem, absorptionSystem, id] at replicated ⊢
    have := (placeValue_alike alike inside).2.2.2 replicated id Function.injective_id
    rw [rename_id, rename_id] at this
    rw [this]

theorem forall₂_imp_mem {α β : Type} {relation relation' : α → β → Prop} {first : List α} {second : List β}
    (related : List.Forall₂ relation first second) (imp : ∀ a ∈ first, ∀ b, relation a b → relation' a b) :
    List.Forall₂ relation' first second := by
  induction related with
  | nil => exact .nil
  | cons here _ recurse =>
      exact .cons (imp _ List.mem_cons_self _ here) (recurse fun a member b holds =>
        imp a (List.mem_cons_of_mem _ member) b holds)

theorem any_mentions_alike {first second : List Pattern} (alike : List.Forall₂ (AlikeR block) first second)
    (index : Nat) : second.any (mentions index) = first.any (mentions index) := by
  induction alike with
  | nil => rfl
  | cons here _ recurse => simp only [List.any_cons, mentions_alike here, recurse]

/-- **Pruning alike components gives similar blocks.** -/
theorem prune_alike {count : Nat} {first second : List Pattern} (alike : List.Forall₂ (AlikeR block) first second) :
    SimilarR block (Prenex.mk count first).prune (Prenex.mk count second).prune := by
  have usedSame : usedOf ⟨count, second⟩ = usedOf ⟨count, first⟩ := by
    unfold usedOf
    exact List.filter_congr fun index _ => any_mentions_alike alike index
  rw [prune_eq, prune_eq, usedSame]
  refine ⟨rfl, List.range _, _, List.Perm.refl _, ?_, List.Perm.refl _⟩
  have renameId : rename (Prenex.permute (usedOf ⟨count, first⟩).length (List.range (usedOf ⟨count, first⟩).length)) =
      (id : Pattern → Pattern) := by
    rw [permute_range]
    exact funext rename_id
  simp only
  rw [renameId, List.map_id, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  have member : ∀ {component index}, FreeIn index component → component ∈ first → index < count →
      index ∈ usedOf ⟨count, first⟩ := fun free inFirst below =>
    List.mem_filter.mpr ⟨List.mem_range.mpr below, List.any_eq_true.mpr ⟨_, inFirst, (mentions_iff _ _).mpr free⟩⟩
  exact forall₂_imp_mem alike fun component inFirst component' here => here.rename_on _ fun a b aFree bFree same =>
    groupIndex_injOn (fun below => member aFree inFirst below) (fun below => member bFree inFirst below) same

/-- **Blocks of alike components have one canonical form**, under the laws of the first and order-blind copy tests
of both. -/
theorem normal_alike {count : Nat} {first second : List Pattern} (alike : List.Forall₂ (AlikeR block) first second)
    {bound : Nat} (below : Below block bound) (firstSmall : (Prenex.mk count first).mass ≤ bound)
    (secondSmall : (Prenex.mk count second).mass ≤ bound)
    (firstAtomic : ∀ component ∈ first, decompose block.toBlock component = Prenex.atom component)
    (secondAtomic : ∀ component ∈ second, decompose block.toBlock component = Prenex.atom component)
    (laws : (blockSystem block ⟨count, first⟩).Laws (places ⟨count, first⟩).toFinset)
    (blind : BlindOn block (canonicalOf block) count first) (blind' : BlindOn block (canonicalOf block) count second) :
    normal block ⟨count, first⟩ = normal block ⟨count, second⟩ := by
  have iso := alike_iso alike below firstSmall secondSmall firstAtomic secondAtomic
  have placesSame : places (⟨count, second⟩ : Prenex) = places ⟨count, first⟩ := by
    simp [places, alike.length_eq]
  have laws' : (blockSystem block ⟨count, second⟩).Laws (places ⟨count, second⟩).toFinset := by
    have := iso.laws laws
    rwa [Finset.image_id, ← placesSame] at this
  obtain ⟨final, nodup, finalIs, normalIs⟩ := normal_copies laws blind
  obtain ⟨final', nodup', finalIs', normalIs'⟩ := normal_copies laws' blind'
  have copiesSame := iso.copies
  rw [Finset.image_id, Finset.image_id, ← placesSame] at copiesSame
  have permutation : final'.Perm final := by
    rw [List.perm_ext_iff_of_nodup nodup' nodup]
    intro place
    rw [← List.mem_toFinset, ← List.mem_toFinset (l := final), finalIs', finalIs, copiesSame, placesSame]
  rw [normalIs, normalIs', least_reading_perm (permutation.map _)]
  have finalRange : ∀ place ∈ final, place < first.length := fun place member => by
    have inFinal : place ∈ final.toFinset := List.mem_toFinset.mpr member
    rw [finalIs] at inFinal
    simpa [places] using (Finset.mem_sdiff.mp inFinal).1
  have finalAlike : List.Forall₂ (AlikeR block) (final.map (placeValue block first))
      (final.map (placeValue block second)) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun place member => placeValue_alike alike (finalRange place member)
  exact least_reading_eq (prune_alike finalAlike)

/-! ## Similar blocks -/

theorem placeValue_cons_zero (head : Pattern) (rest : List Pattern) : placeValue block (head :: rest) 0 = head := rfl

theorem placeValue_cons_succ (head : Pattern) (rest : List Pattern) (place : Nat) :
    placeValue block (head :: rest) (place + 1) = placeValue block rest place := rfl

theorem map_range_placeValue (components : List Pattern) :
    (List.range components.length).map (placeValue block components) = components := by
  have := places_map (block := block) ⟨0, components⟩
  simpa [places] using congrArg Prenex.components this

/-- **A permutation of a block's components reads it at a permutation of its places.** -/
theorem exists_places_perm {first second : List Pattern} (permutation : first.Perm second) :
    ∃ kept : List Nat, kept.Nodup ∧ (∀ place ∈ kept, place < second.length) ∧ kept.length = second.length ∧
      kept.map (placeValue block second) = first := by
  induction permutation with
  | nil => exact ⟨[], List.nodup_nil, (fun _ member => nomatch member), rfl, rfl⟩
  | @cons head first second _ recurse =>
      obtain ⟨kept, nodup, inside, lengthIs, mapped⟩ := recurse
      refine ⟨0 :: kept.map (· + 1), List.nodup_cons.mpr ⟨by simp, nodup.map fun a b same => by omega⟩, ?_, ?_, ?_⟩
      · intro place member
        simp only [List.mem_cons, List.mem_map] at member
        rcases member with rfl | ⟨original, inKept, rfl⟩
        · simp
        · have := inside original inKept
          simp only [List.length_cons]
          omega
      · simp [lengthIs]
      · show placeValue block (head :: second) 0 :: (kept.map (· + 1)).map (placeValue block (head :: second)) =
          head :: first
        rw [List.map_map, ← mapped]
        rfl
  | swap first second rest =>
      refine ⟨1 :: 0 :: (List.range rest.length).map (· + 2), ?_, ?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨by simp, List.nodup_cons.mpr ⟨by simp, ?_⟩⟩
        exact List.nodup_range.map fun a b same => by omega
      · intro place member
        simp only [List.mem_cons, List.mem_map, List.mem_range] at member
        rcases member with rfl | rfl | ⟨original, below, rfl⟩
        · simp
        · simp
        · simp only [List.length_cons]
          omega
      · simp
      · simp only [List.map_cons, List.map_map]
        rw [show placeValue block (first :: second :: rest) 1 = second from rfl,
          show placeValue block (first :: second :: rest) 0 = first from rfl]
        congr 2
        conv_rhs => rw [← map_range_placeValue (block := block) rest]
        exact List.map_congr_left fun place _ => rfl
  | @trans first middle last _ _ recurse recurse' =>
      obtain ⟨kept, nodup, inside, lengthIs, mapped⟩ := recurse
      obtain ⟨kept', nodup', inside', lengthIs', mapped'⟩ := recurse'
      have middleLength : middle.length = last.length := by rw [← mapped', List.length_map, lengthIs']
      refine ⟨kept.map fun place => kept'.getD place 0, ?_, ?_, ?_, ?_⟩
      · refine nodup.map_on fun a aIn b bIn same => ?_
        have aBelow : a < kept'.length := by have := inside a aIn; omega
        have bBelow : b < kept'.length := by have := inside b bIn; omega
        rw [List.getD_eq_getElem _ _ aBelow, List.getD_eq_getElem _ _ bBelow] at same
        exact (List.Nodup.getElem_inj_iff nodup').mp same
      · intro place member
        obtain ⟨original, inKept, rfl⟩ := List.mem_map.mp member
        have below : original < kept'.length := by have := inside original inKept; omega
        rw [List.getD_eq_getElem _ _ below]
        exact inside' _ (List.getElem_mem below)
      · rw [List.length_map, lengthIs, middleLength]
      · rw [← mapped, List.map_map]
        refine List.map_congr_left fun place member => ?_
        have below : place < kept'.length := by have := inside place member; omega
        have belowMiddle : place < middle.length := inside place member
        simp only [Function.comp_apply]
        rw [List.getD_eq_getElem _ _ below]
        unfold placeValue
        rw [List.getD_eq_getElem _ _ belowMiddle]
        simp only [← mapped', List.getElem_map]
        unfold placeValue
        rfl

/-- A block of a permutation of the places is the block itself, as far as removals go. -/
theorem removes_of_perm {form : Prenex} {kept : List Nat} (nodup : kept.Nodup)
    (inside : ∀ place ∈ kept, place < form.components.length) (lengthIs : kept.length = form.components.length) :
    (blockSystem block form).Removes (places form).toFinset kept.toFinset := by
  have same : kept.toFinset = (places form).toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro place member
      simpa [places] using inside place (List.mem_toFinset.mp member)
    · rw [List.toFinset_card_of_nodup nodup, List.toFinset_card_of_nodup (places_nodup form), lengthIs]
      simp [places]
  rw [same]
  exact .refl

theorem Below.mono {bound bound' : Nat} (below : Below block bound) (smaller : bound' ≤ bound) : Below block bound' where
  similar := fun first second firstSmall secondSmall => below.similar first second (by omega) (by omega)
  renamed := fun first second firstSmall secondSmall => below.renamed first second (by omega) (by omega)
  shape := fun pattern small => below.shape pattern (by omega)
  sized := fun pattern small => below.sized pattern (by omega)

theorem renameOuter_of_id {relabel : Nat → Nat} (identity : ∀ index, relabel index = index) (form : Prenex) :
    form.renameOuter relabel = form := by
  obtain ⟨count, components⟩ := form
  have liftId : liftIndex count relabel = id := by
    funext index
    unfold liftIndex
    split_ifs
    · rfl
    · rw [identity]
      simp only [id]
      omega
  simp only [Prenex.renameOuter, liftId]
  rw [show rename id = (id : Pattern → Pattern) from funext rename_id, List.map_id]

/-- **Similar blocks have one canonical form**, given the canonical form below their size and the laws and
order-blind copy tests of every block no heavier than they are. -/
theorem normal_similar {first second : Prenex} (similar : SimilarR block first second) {bound : Nat}
    (below : Below block bound) (firstSmall : first.mass ≤ bound) (secondSmall : second.mass ≤ bound)
    (firstAtomic : first.Atomic block.toBlock) (secondAtomic : second.Atomic block.toBlock)
    (lawful : ∀ form : Prenex, form.mass ≤ bound → form.Atomic block.toBlock →
      (blockSystem block form).Laws (places form).toFinset ∧ BlindOn block (canonicalOf block) form.count form.components) :
    normal block first = normal block second := by
  obtain ⟨countEq, order, middle, isOrder, related, permutation⟩ := similar
  obtain ⟨count, components⟩ := first
  obtain ⟨count', components'⟩ := second
  simp only at countEq isOrder related permutation
  subst countEq
  -- the restrictions reordered
  have preserving : Preserving count count (Prenex.permute count order) := by
    refine ⟨permute_injective isOrder, fun index below => ?_, fun index above => ?_⟩
    · rw [Prenex.permute, if_pos below]
      have lengthIs := isOrder.length_eq
      simp only [List.length_range] at lengthIs
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.mem_range.mp (isOrder.subset (List.getElem_mem _))
    · rw [Prenex.permute, if_neg (by omega)]
      exact above
  have reorderedMass : (Prenex.mk count (components.map (rename (Prenex.permute count order)))).mass =
      (Prenex.mk count components).mass := by
    simp only [Prenex.mass, sizeList_map_rename]
  have reorderedAtomic : (Prenex.mk count (components.map (rename (Prenex.permute count order)))).Atomic
      block.toBlock := atomic_map_rename firstAtomic _
  obtain ⟨laws, blind⟩ := lawful ⟨count, components⟩ firstSmall firstAtomic
  obtain ⟨laws₁, blind₁⟩ := lawful _ (by rw [reorderedMass]; exact firstSmall) reorderedAtomic
  obtain ⟨_, _, _, normalIs, normalIs'⟩ := normal_rename preserving (below.mono firstSmall) firstAtomic laws blind
  have reordered : normal block ⟨count, components.map (rename (Prenex.permute count order))⟩ =
      normal block ⟨count, components⟩ := by
    rw [normalIs, normalIs', renameOuter_of_id fun index => by
      unfold pruneRelabel
      rw [Prenex.permute, if_neg (by omega)]
      omega]
  -- the components replaced by alike ones
  have middleMass : (Prenex.mk count middle).mass = (Prenex.mk count components').mass := by
    simp only [Prenex.mass, sizeList_perm permutation]
  have middleAtomic : (Prenex.mk count middle).Atomic block.toBlock := fun component member =>
    secondAtomic component (permutation.subset member)
  obtain ⟨laws₂, blind₂⟩ := lawful ⟨count, middle⟩ (by rw [middleMass]; exact secondSmall) middleAtomic
  have alikeStep := normal_alike related below (by rw [reorderedMass]; exact firstSmall)
    (by rw [middleMass]; exact secondSmall) reorderedAtomic middleAtomic laws₁ blind₁ blind₂
  -- the components permuted
  obtain ⟨kept, keptNodup, keptInside, keptLength, keptMap⟩ := exists_places_perm (block := block) permutation.symm
  have permuted := normal_restrict laws₂ blind₂ keptNodup keptInside (removes_of_perm keptNodup keptInside keptLength)
  have restricted : restrictTo block ⟨count, middle⟩ kept = ⟨count, components'⟩ := by
    unfold restrictTo
    rw [keptMap]
  rw [restricted] at permuted
  rw [← reordered, alikeStep, permuted]

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks




