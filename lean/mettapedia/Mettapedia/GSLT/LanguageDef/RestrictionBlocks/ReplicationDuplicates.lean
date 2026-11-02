import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationFree

/-!
# A replicated component twice is once

Two equal replicated components of a block are twins of its absorption system (`twins_of_eq`): they mention the
same restrictions and copy the same groups, and a copy group holding both is a copy or not without one of them,
since the group's copy reads canonically with or without the duplicate, a lighter block. Absorption without one twin
ends where absorption with both does, without it, and a reading does not see the duplicate, so a block reads
canonically as without it (`normal_duplicate`). Hence keeping one of each replicated component keeps the canonical
form (`normal_dedupReplicated`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {block : ReplicationBlock}

/-! ## Similar blocks at every size -/

/-- **Similar blocks of atoms have one canonical form.** -/
theorem normal_similar_all (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) {first second : Prenex} (similar : SimilarR block first second)
    (firstAtomic : first.Atomic block.toBlock) (secondAtomic : second.Atomic block.toBlock) :
    normal block first = normal block second :=
  normal_similar similar (below_all fresh restrictFresh (max first.mass second.mass)) (le_max_left _ _)
    (le_max_right _ _) firstAtomic secondAtomic fun _ _ atomic => lawful_all fresh restrictFresh atomic

/-- **A block's canonical form forgets the order of its components.** -/
theorem normal_perm (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {count : Nat} {first second : List Pattern} (permutation : first.Perm second)
    (atomic : (Prenex.mk count first).Atomic block.toBlock) :
    normal block ⟨count, first⟩ = normal block ⟨count, second⟩ := by
  refine normal_similar_all fresh restrictFresh ⟨rfl, List.range count, first, List.Perm.refl _, ?_, permutation⟩
    atomic fun component member => atomic component (permutation.symm.subset member)
  have renameId : rename id = (id : Pattern → Pattern) := funext rename_id
  simp only
  rw [permute_range, renameId, List.map_id]
  exact List.forall₂_same.mpr fun component _ => AlikeR.refl component

/-! ## A reading does not see a replicated duplicate -/

theorem readingsR_cons_duplicate {count : Nat} {duplicate : Pattern} {components : List Pattern}
    (member : duplicate ∈ components) (replicated : isReplicated block duplicate = true) :
    readingsR block ⟨count, duplicate :: components⟩ = readingsR block ⟨count, components⟩ := by
  unfold readingsR
  have sameMembers : ∀ component, component ∈ duplicate :: components ↔ component ∈ components := fun component =>
    ⟨fun inCons => (List.mem_cons.mp inCons).elim (fun same => same ▸ member) id, List.mem_cons_of_mem _⟩
  rw [readingOrders_congr (first := ⟨count, duplicate :: components⟩) (second := ⟨count, components⟩) rfl fun index _ =>
    signatureOf_congr (first := ⟨count, duplicate :: components⟩) (second := ⟨count, components⟩) rfl sameMembers index]
  apply List.map_congr_left
  intro order _
  apply content_eq
  intro target
  rw [count_content, count_content, List.map_cons]
  have readReplicated : isReplicated block (recanon block (rename (Prenex.permute count order) duplicate)) = true := by
    rw [isReplicated_recanon, isReplicated_rename, replicated]
  have readMember : recanon block (rename (Prenex.permute count order) duplicate) ∈
      components.map fun component => recanon block (rename (Prenex.permute count order) component) :=
    List.mem_map_of_mem (f := fun component => recanon block (rename (Prenex.permute count order) component)) member
  split_ifs with targetReplicated inBoth inRest inRest
  · rfl
  · exact absurd ((List.mem_cons.mp inBoth).resolve_left fun same => inRest (same ▸ readMember)) inRest
  · exact absurd (List.mem_cons_of_mem _ inRest) inBoth
  · rfl
  · rw [List.count_cons]
    have different : (recanon block (rename (Prenex.permute count order) duplicate) == target) = false := by
      rw [beq_eq_false_iff_ne]
      intro same
      rw [same] at readReplicated
      exact targetReplicated readReplicated
    rw [different]
    rfl

theorem usedOf_cons_duplicate {count : Nat} {duplicate : Pattern} {components : List Pattern}
    (member : duplicate ∈ components) :
    usedOf ⟨count, duplicate :: components⟩ = usedOf ⟨count, components⟩ := by
  unfold usedOf
  apply List.filter_congr
  intro index _
  simp only [List.any_cons]
  cases mentioned : mentions index duplicate
  · rfl
  · rw [Bool.true_or]
    exact (List.any_eq_true.mpr ⟨duplicate, member, mentioned⟩).symm

/-- **A replicated duplicate adds nothing to the least reading of a block's places.** -/
theorem least_reading_cons_duplicate {count : Nat} {duplicate : Pattern} {components : List Pattern}
    (member : duplicate ∈ components) (replicated : isReplicated block duplicate = true) :
    (⟨(Prenex.mk count (duplicate :: components)).prune.count,
        least (readingsR block (Prenex.mk count (duplicate :: components)).prune)⟩ : Prenex) =
      ⟨(Prenex.mk count components).prune.count, least (readingsR block (Prenex.mk count components).prune)⟩ := by
  rw [prune_eq, prune_eq, usedOf_cons_duplicate member]
  simp only [List.map_cons]
  rw [readingsR_cons_duplicate (List.mem_map_of_mem member) (by rw [isReplicated_rename]; exact replicated)]

/-! ## Equal replicated components are twins -/

/-- **Groups with the same components and the same canonical copy test alike.** -/
theorem copyTest_congr {count : Nat} {component : Pattern} {allowed : List Nat} {value : Nat → Pattern}
    {items items' : List Nat} (sameValues : ∀ pattern, pattern ∈ items.map value ↔ pattern ∈ items'.map value)
    (sameCopy : canonicalOf block (copyOf block.toBlock count (asGroup allowed count value items)) =
      canonicalOf block (copyOf block.toBlock count (asGroup allowed count value items'))) :
    CopyTest block (canonicalOf block) count component (asGroup allowed count value items) ↔
      CopyTest block (canonicalOf block) count component (asGroup allowed count value items') := by
  have restrictionsSame : restrictionsOf allowed count value items = restrictionsOf allowed count value items' := by
    unfold restrictionsOf
    apply List.filter_congr
    intro index _
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨item, inItems, keyed⟩
      obtain ⟨item', inItems', sameValue⟩ := List.mem_map.mp ((sameValues (value item)).mp (List.mem_map_of_mem inItems))
      refine ⟨item', inItems', ?_⟩
      unfold throughKeys at keyed ⊢
      rwa [sameValue]
    · rintro ⟨item', inItems', keyed⟩
      obtain ⟨item, inItems, sameValue⟩ := List.mem_map.mp ((sameValues (value item')).mpr (List.mem_map_of_mem inItems'))
      refine ⟨item, inItems, ?_⟩
      unfold throughKeys at keyed ⊢
      rwa [sameValue]
  have groupSame : (asGroup allowed count value items).restrictions = (asGroup allowed count value items').restrictions :=
    restrictionsSame
  unfold CopyTest
  rw [sameCopy, groupSame]
  constructor
  · rintro ⟨first, second, third, fourth⟩
    refine ⟨first, second, fun member inGroup isReplicated =>
      third member ((sameValues member).mpr inGroup) isReplicated, fun index below mentioned => ?_⟩
    obtain ⟨member, inGroup, mentionedBy⟩ := fourth index below mentioned
    exact ⟨member, (sameValues member).mp inGroup, mentionedBy⟩
  · rintro ⟨first, second, third, fourth⟩
    refine ⟨first, second, fun member inGroup isReplicated =>
      third member ((sameValues member).mp inGroup) isReplicated, fun index below mentioned => ?_⟩
    obtain ⟨member, inGroup, mentionedBy⟩ := fourth index below mentioned
    exact ⟨member, (sameValues member).mpr inGroup, mentionedBy⟩

/-- A group's copy reads canonically as its block does. -/
theorem canonicalOf_copyOf {allowed : List Nat} {count : Nat} {value : Nat → Pattern}
    {items : List Nat} (atomic : ∀ item ∈ items, decompose block.toBlock (value item) = Prenex.atom (value item)) :
    canonicalOf block (copyOf block.toBlock count (asGroup allowed count value items)) =
      Prenex.toPattern block.toBlock (normal block
        (copyBlock count (restrictionsOf allowed count value items) (items.map value))) := by
  rw [copyOf_eq_copyBlock]
  unfold canonicalOf
  congr 2
  apply decompose_toPattern _ copyBlock_used
  intro component member
  obtain ⟨original, inMap, rfl⟩ := List.mem_map.mp member
  obtain ⟨item, inItems, rfl⟩ := List.mem_map.mp inMap
  exact atomic_rename (atomic item inItems) _

/-- **A duplicate of a replicated component adds nothing to the canonical form.** -/
theorem normal_duplicate (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) :
    ∀ (bound count : Nat) (extra : Pattern) (components : List Pattern),
      (Prenex.mk count (extra :: components)).mass < bound →
      (Prenex.mk count (extra :: components)).Atomic block.toBlock → extra ∈ components →
      isReplicated block extra = true →
      normal block ⟨count, extra :: components⟩ = normal block ⟨count, components⟩
  | 0, _, _, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | bound + 1, count, extra, components, small, atomic, member, replicated => by
      classical
      set form : Prenex := ⟨count, extra :: components⟩ with formIs
      have formAtomic : form.Atomic block.toBlock := atomic
      obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh formAtomic
      -- the duplicate's place
      set e := components.idxOf extra + 1 with eIs
      have eBelow : components.idxOf extra < components.length := List.idxOf_lt_length_of_mem member
      have valueZero : placeValue block form.components 0 = extra := rfl
      have valueE : placeValue block form.components e = extra := by
        show placeValue block (extra :: components) (components.idxOf extra + 1) = extra
        rw [placeValue_cons_succ]
        unfold placeValue
        rw [List.getD_eq_getElem _ _ eBelow, List.getElem_idxOf]
      have same : placeValue block form.components 0 = placeValue block form.components e := by
        rw [valueZero, valueE]
      have placesIs : (places form).toFinset = (Finset.range (components.length + 1)) := by
        ext place
        simp [places, form]
      have zeroLive : 0 ∈ (places form).toFinset := by rw [placesIs]; simp
      have eLive : e ∈ (places form).toFinset := by rw [placesIs]; simp only [Finset.mem_range]; omega
      have inPlaces : ∀ place ∈ (places form).toFinset, place < form.components.length := fun place inSet => by
        rw [placesIs, Finset.mem_range] at inSet
        simpa [form] using inSet
      -- a copy group holding both twins reads canonically without one of them
      have dropOne : ∀ p ∈ (places form).toFinset, p ≠ 0 → p ≠ e → ∀ group ⊆ (places form).toFinset, p ∉ group →
          0 ∈ group → e ∈ group →
          ((blockSystem block form).copy group p ↔ (blockSystem block form).copy (group.erase 0) p) := by
        intro p pLive _ pE group groupLive pNot zeroIn eIn
        set value := placeValue block form.components with valueIs
        set allowed := allowedFor count (value p) with allowedIs
        set items := group.sort (· ≤ ·) with itemsIs
        set items' := (group.erase 0).sort (· ≤ ·) with itemsIs'
        have itemsNodup : items.Nodup := Finset.sort_nodup _ _
        have itemsNodup' : items'.Nodup := Finset.sort_nodup _ _
        have itemsPerm : items.Perm (0 :: items') := by
          rw [List.perm_ext_iff_of_nodup itemsNodup
            (List.nodup_cons.mpr ⟨fun inRest => by simp [items'] at inRest, itemsNodup'⟩)]
          intro place
          simp only [items, items', Finset.mem_sort, List.mem_cons, Finset.mem_erase]
          constructor
          · intro inGroup
            by_cases isZero : place = 0
            · exact .inl isZero
            · exact .inr ⟨isZero, inGroup⟩
          · rintro (rfl | ⟨_, inGroup⟩)
            · exact zeroIn
            · exact inGroup
        have eItems' : e ∈ items' := by
          simp only [items', Finset.mem_sort, Finset.mem_erase]
          exact ⟨by omega, eIn⟩
        have sameValues : ∀ pattern, pattern ∈ items.map value ↔ pattern ∈ items'.map value := by
          intro pattern
          rw [(itemsPerm.map value).mem_iff, List.map_cons, List.mem_cons]
          constructor
          · rintro (isZero | inRest)
            · rw [isZero, show value 0 = value e from same]
              exact List.mem_map_of_mem eItems'
            · exact inRest
          · exact Or.inr
        have restrictionsSame : restrictionsOf allowed count value items = restrictionsOf allowed count value items' := by
          unfold restrictionsOf
          apply List.filter_congr
          intro index _
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true]
          constructor
          · rintro ⟨item, inItems, keyed⟩
            obtain ⟨item', inItems', sameValue⟩ :=
              List.mem_map.mp ((sameValues (value item)).mp (List.mem_map_of_mem inItems))
            refine ⟨item', inItems', ?_⟩
            unfold throughKeys at keyed ⊢
            rwa [sameValue]
          · rintro ⟨item', inItems', keyed⟩
            obtain ⟨item, inItems, sameValue⟩ :=
              List.mem_map.mp ((sameValues (value item')).mpr (List.mem_map_of_mem inItems'))
            refine ⟨item, inItems, ?_⟩
            unfold throughKeys at keyed ⊢
            rwa [sameValue]
        have itemsInside : ∀ item ∈ items, item < form.components.length := fun item inItems => by
          have : item ∈ group := (Finset.mem_sort _).mp inItems
          exact inPlaces item (groupLive this)
        have itemsAtomic : ∀ item ∈ items, decompose block.toBlock (value item) = Prenex.atom (value item) :=
          fun item inItems => formAtomic _ (placeValue_mem (itemsInside item inItems))
        have itemsAtomic' : ∀ item ∈ items', decompose block.toBlock (value item) = Prenex.atom (value item) :=
          fun item inItems' => itemsAtomic item ((itemsPerm.symm.subset (List.mem_cons_of_mem _ inItems')))
        show CopyTest block (canonicalOf block) count (value p) (asGroup allowed count value items) ↔
          CopyTest block (canonicalOf block) count (value p) (asGroup allowed count value items')
        refine copyTest_congr sameValues ?_
        rw [canonicalOf_copyOf itemsAtomic, canonicalOf_copyOf itemsAtomic',
          ← restrictionsSame]
        congr 1
        -- the copy with both twins is the copy with one, and a duplicate
        set restrictions := restrictionsOf allowed count value items with restrictionsIs
        set split := Prenex.permute count (splitOrder count (outsideOf count restrictions) restrictions) with splitIs
        have copyPerm : ((items.map value).map (rename split)).Perm
            (rename split (value 0) :: (items'.map value).map (rename split)) := by
          have := (itemsPerm.map value).map (rename split)
          simpa using this
        have copyAtomic : (Prenex.mk restrictions.length ((items.map value).map (rename split))).Atomic block.toBlock := by
          intro component inComponents
          obtain ⟨original, inMap, rfl⟩ := List.mem_map.mp inComponents
          obtain ⟨item, inItems, rfl⟩ := List.mem_map.mp inMap
          exact atomic_rename (itemsAtomic item inItems) _
        show normal block ⟨restrictions.length, (items.map value).map (rename split)⟩ =
          normal block ⟨restrictions.length, (items'.map value).map (rename split)⟩
        rw [normal_perm fresh restrictFresh copyPerm copyAtomic]
        -- the duplicate is lighter than the block
        have pPlace : p < form.components.length := inPlaces p pLive
        have pNotItems : p ∉ items := fun inItems => pNot ((Finset.mem_sort _).mp inItems)
        have weights : size (value p) + sizeList (items.map value) ≤ sizeList (extra :: components) := by
          have := sizeList_places_le (block := block) (List.nodup_cons.mpr ⟨pNotItems, itemsNodup⟩)
            (fun item inList => by
              rcases List.mem_cons.mp inList with rfl | inItems
              · exact pPlace
              · exact itemsInside item inItems)
          simp only [List.map_cons, sizeList] at this
          exact this
        have pPositive : 0 < size (value p) := size_pos _
        have fewer : restrictions.length ≤ count := length_le_of_inside (restrictionsOf_nodup allowed count value items)
          fun _ restricted => restrictionsOf_lt restricted
        have permMass : sizeList (items.map value) =
            sizeList (rename split (value 0) :: (items'.map value).map (rename split)) := by
          rw [← sizeList_perm copyPerm, sizeList_map_rename]
        have smallIs : 2 * count + sizeList (extra :: components) < bound + 1 := small
        have copyMass : (Prenex.mk restrictions.length (rename split (value 0) :: (items'.map value).map (rename split))).mass
            < bound := by
          show 2 * restrictions.length + sizeList (rename split (value 0) :: (items'.map value).map (rename split)) < bound
          omega
        refine normal_duplicate fresh restrictFresh bound _ _ _ copyMass ?_ ?_ ?_
        · intro component inComponents
          exact copyAtomic component (copyPerm.symm.subset inComponents)
        · rw [show value 0 = value e from same]
          exact List.mem_map_of_mem (List.mem_map_of_mem eItems')
        · rw [isReplicated_rename]
          exact replicated
      have twins : (blockSystem block form).Twins (places form).toFinset 0 e :=
        { dLive := zeroLive
          eLive := eLive
          different := by omega
          dReplicated := by
            show isReplicated block (placeValue block form.components 0) = true
            rw [valueZero]
            exact replicated
          eReplicated := by
            show isReplicated block (placeValue block form.components e) = true
            rw [valueE]
            exact replicated
          sameMentions := by
            show (usedRestrictions count (placeValue block form.components 0)).toFinset =
              (usedRestrictions count (placeValue block form.components e)).toFinset
            rw [same]
          sameCopies := fun group _ _ _ => by
            show CopyTest block (canonicalOf block) count (placeValue block form.components 0)
                (asGroup (allowedFor count (placeValue block form.components 0)) count
                  (placeValue block form.components) (group.sort (· ≤ ·))) ↔
              CopyTest block (canonicalOf block) count (placeValue block form.components e)
                (asGroup (allowedFor count (placeValue block form.components e)) count
                  (placeValue block form.components) (group.sort (· ≤ ·)))
            rw [same]
          dropOne := dropOne }
      -- absorbing without the first twin
      set kept := (List.range components.length).map (· + 1) with keptIs
      have keptNodup : kept.Nodup := List.nodup_range.map fun _ _ same => Nat.succ_injective same
      have keptInside : ∀ place ∈ kept, place < form.components.length := fun place inKept => by
        obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp inKept
        simpa [form] using List.mem_range.mp inRange
      have keptValues : kept.map (placeValue block form.components) = components := by
        rw [keptIs, List.map_map]
        conv_rhs => rw [← map_range_placeValue (block := block) components]
        rfl
      have keptSet : kept.toFinset = (places form).toFinset.erase 0 := by
        ext place
        rw [placesIs]
        simp only [keptIs, List.mem_toFinset, List.mem_map, List.mem_range, Finset.mem_erase, Finset.mem_range]
        constructor
        · rintro ⟨index, below, rfl⟩
          omega
        · rintro ⟨notZero, below⟩
          exact ⟨place - 1, by omega, by omega⟩
      obtain ⟨final, finalNodup, absorbs, reached⟩ := absorbRounds_absorbs
        (height := fun place => size (canonicalOf block (argumentOf? (placeValue block form.components place))))
        blind kept.length keptNodup keptInside (le_refl _)
      rw [keptValues] at reached
      have restNormal : normal block ⟨count, components⟩ =
          ⟨(Prenex.mk count (final.map (placeValue block form.components))).prune.count,
            least (readingsR block (Prenex.mk count (final.map (placeValue block form.components))).prune)⟩ := by
        rw [normal_eq_reading]
        unfold absorb
        have lengthIs : components.length = kept.length := by simp [keptIs]
        simp only
        rw [lengthIs, reached]
      have finalIs : final.toFinset = ((places form).toFinset \ (blockSystem block form).copies (places form).toFinset).erase 0 :=
        twins.absorbs_erase laws (Finset.Subset.refl _) (keptSet ▸ absorbs)
      -- absorbing with both twins
      obtain ⟨final', finalNodup', finalIs', normalIs⟩ := normal_copies laws blind
      rw [restNormal]
      show normal block form = _
      rw [normalIs]
      by_cases zeroCopied : 0 ∈ (blockSystem block form).copies (places form).toFinset
      · have permutation : final'.Perm final := by
          rw [List.perm_ext_iff_of_nodup finalNodup' finalNodup]
          intro place
          rw [← List.mem_toFinset, ← List.mem_toFinset (l := final), finalIs', finalIs, Finset.mem_erase]
          constructor
          · intro inFinal
            refine ⟨fun isZero => ?_, inFinal⟩
            rw [isZero] at inFinal
            exact (Finset.mem_sdiff.mp inFinal).2 zeroCopied
          · exact fun ⟨_, inFinal⟩ => inFinal
        exact least_reading_perm (permutation.map _)
      · have eNotCopied : e ∉ (blockSystem block form).copies (places form).toFinset := fun eCopied =>
          zeroCopied ((twins.toTwinPair.mem_copies_iff laws (Finset.Subset.refl _)).mpr eCopied)
        have permutation : final'.Perm (0 :: final) := by
          rw [List.perm_ext_iff_of_nodup finalNodup' (List.nodup_cons.mpr ⟨fun inFinal => by
            have := List.mem_toFinset.mpr inFinal
            rw [finalIs] at this
            exact (Finset.mem_erase.mp this).1 rfl, finalNodup⟩)]
          intro place
          rw [← List.mem_toFinset, finalIs', List.mem_cons, ← List.mem_toFinset (l := final), finalIs,
            Finset.mem_erase]
          constructor
          · intro inFinal
            by_cases isZero : place = 0
            · exact .inl isZero
            · exact .inr ⟨isZero, inFinal⟩
          · rintro (rfl | ⟨_, inFinal⟩)
            · exact Finset.mem_sdiff.mpr ⟨zeroLive, zeroCopied⟩
            · exact inFinal
        have eFinal : e ∈ final := by
          rw [← List.mem_toFinset, finalIs, Finset.mem_erase]
          exact ⟨by omega, Finset.mem_sdiff.mpr ⟨eLive, eNotCopied⟩⟩
        rw [least_reading_perm (permutation.map _), List.map_cons, valueZero]
        refine least_reading_cons_duplicate ?_ replicated
        rw [← valueE]
        exact List.mem_map_of_mem eFinal

/-- **Keeping one of each replicated component keeps the canonical form.** -/
theorem normal_dedupReplicated (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) {count : Nat} :
    ∀ (components extra : List Pattern), (Prenex.mk count (extra ++ components)).Atomic block.toBlock →
      normal block ⟨count, extra ++ dedupReplicated block components⟩ = normal block ⟨count, extra ++ components⟩
  | [], _, _ => rfl
  | component :: rest, extra, atomic => by
      unfold dedupReplicated
      split_ifs with drop
      · simp only [Bool.and_eq_true, List.contains_iff_mem] at drop
        have restAtomic : (Prenex.mk count (extra ++ rest)).Atomic block.toBlock := fun other member =>
          atomic other (by
            rcases List.mem_append.mp member with inExtra | inRest
            · exact List.mem_append_left _ inExtra
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ inRest))
        rw [normal_dedupReplicated fresh restrictFresh rest extra restAtomic]
        have permutation : (component :: (extra ++ rest)).Perm (extra ++ component :: rest) :=
          List.perm_middle.symm
        have consAtomic : (Prenex.mk count (component :: (extra ++ rest))).Atomic block.toBlock :=
          fun other member => atomic other (permutation.subset member)
        rw [← normal_perm fresh restrictFresh permutation consAtomic,
          normal_duplicate fresh restrictFresh _ count component (extra ++ rest) (Nat.lt_succ_self _) consAtomic
            (List.mem_append_right _ drop.2) drop.1]
      · have moved : extra ++ component :: dedupReplicated block rest = (extra ++ [component]) ++ dedupReplicated block rest := by
          simp
        have moved' : extra ++ component :: rest = (extra ++ [component]) ++ rest := by simp
        rw [moved, moved', normal_dedupReplicated fresh restrictFresh rest (extra ++ [component]) (moved' ▸ atomic)]

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
