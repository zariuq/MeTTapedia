import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationEntries

/-!
# Entries along the moves of normalization

The entries of a block's places stay the same when its restrictions are renamed or unused ones dropped
(`isEntry_prune`), when its components are read again under an order of its restrictions (`isEntry_read`), when its
components are permuted (`isEntry_perm`), and when a replicated duplicate is dropped (`isEntry_cons_duplicate`,
`isEntry_dedupReplicated`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex freeIn_apply)

variable {block : ReplicationBlock}

/-! ## Keys and links -/

/-- **Keys renamed by a map telling them apart share alike.** -/
theorem shares_image {keys keys' : Nat → List Nat} {relabel : Nat → Nat}
    (image : ∀ place restriction, restriction ∈ keys' place ↔ ∃ original ∈ keys place, relabel original = restriction)
    (injective : ∀ first second place place', first ∈ keys place → second ∈ keys place' →
      relabel first = relabel second → first = second)
    (first second : Nat) : Linked.Shares keys' first second ↔ Linked.Shares keys first second := by
  constructor
  · rintro ⟨key, inFirst, inSecond⟩
    obtain ⟨original, inOriginal, rfl⟩ := (image first key).mp inFirst
    obtain ⟨original', inOriginal', same⟩ := (image second _).mp inSecond
    exact ⟨original, inOriginal, (injective original' original second first inOriginal' inOriginal same) ▸ inOriginal'⟩
  · rintro ⟨key, inFirst, inSecond⟩
    exact ⟨relabel key, (image first _).mpr ⟨key, inFirst, rfl⟩, (image second _).mpr ⟨key, inSecond, rfl⟩⟩

theorem linkedIn_congr {keys keys' : Nat → List Nat} {items : List Nat}
    (shares : ∀ first ∈ items, ∀ second ∈ items, Linked.Shares keys' first second ↔ Linked.Shares keys first second)
    {first second : Nat} (inFirst : first ∈ items) (inSecond : second ∈ items) :
    Linked.LinkedIn keys' items first second ↔ Linked.LinkedIn keys items first second := by
  have := linkedIn_map_iff (keys := keys) (keys' := keys') (items := items) id (fun _ _ _ _ same => same)
    (fun a aIn b bIn => shares a aIn b bIn) inFirst inSecond
  simpa using this

theorem linkedIn_of_mem_iff {keys : Nat → List Nat} {items items' : List Nat} (same : ∀ item, item ∈ items ↔ item ∈ items')
    {first second : Nat} : Linked.LinkedIn keys items first second ↔ Linked.LinkedIn keys items' first second :=
  ⟨fun linked => linked.mono fun item member => (same item).mp member,
    fun linked => linked.mono fun item member => (same item).mpr member⟩

/-! ## Entries of related blocks -/

/-- **Blocks whose places share alike and read alike have the same entries.** -/
theorem isEntry_congr {form form' : Prenex} {live : List Nat}
    (shares : ∀ first ∈ live, ∀ second ∈ live,
      Linked.Shares (keysAt block form') first second ↔ Linked.Shares (keysAt block form) first second)
    (entries : ∀ group : List Nat, (∀ place ∈ group, place ∈ live) → entryOf block form' group = entryOf block form group)
    (pattern : Pattern) : IsEntry block form' live pattern ↔ IsEntry block form live pattern := by
  have classSame : ∀ place ∈ live, classIn block form' live place = classIn block form live place := by
    intro place inLive
    classical
    unfold classIn
    apply List.filter_congr
    intro other inOther
    exact decide_eq_decide.mpr (linkedIn_congr shares inLive inOther)
  have classInside : ∀ place, ∀ other ∈ classIn block form live place, other ∈ live :=
    fun _ _ member => (mem_classIn.mp member).1
  constructor
  · rintro ⟨place, inLive, rfl⟩
    refine ⟨place, inLive, ?_⟩
    rw [classSame place inLive, entries _ (classInside place)]
  · rintro ⟨place, inLive, rfl⟩
    refine ⟨place, inLive, ?_⟩
    rw [classSame place inLive, entries _ (classInside place)]

/-- **Places renamed along a map telling them apart, sharing and reading alike, have the same entries.** -/
theorem isEntry_map {form form' : Prenex} {live : List Nat} (map : Nat → Nat)
    (injective : ∀ first ∈ live, ∀ second ∈ live, map first = map second → first = second)
    (shares : ∀ first ∈ live, ∀ second ∈ live,
      Linked.Shares (keysAt block form') (map first) (map second) ↔ Linked.Shares (keysAt block form) first second)
    (entries : ∀ group : List Nat, (∀ place ∈ group, place ∈ live) →
      entryOf block form' (group.map map) = entryOf block form group)
    (pattern : Pattern) : IsEntry block form' (live.map map) pattern ↔ IsEntry block form live pattern := by
  have classSame : ∀ place ∈ live,
      classIn block form' (live.map map) (map place) = (classIn block form live place).map map := by
    intro place inLive
    classical
    unfold classIn
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro other inOther
    simp only [Function.comp_apply]
    exact decide_eq_decide.mpr (linkedIn_map_iff map injective shares inLive inOther)
  have classInside : ∀ place, ∀ other ∈ classIn block form live place, other ∈ live :=
    fun _ _ member => (mem_classIn.mp member).1
  constructor
  · rintro ⟨place', inLive', rfl⟩
    obtain ⟨place, inLive, rfl⟩ := List.mem_map.mp inLive'
    exact ⟨place, inLive, by rw [classSame place inLive, entries _ (classInside place)]⟩
  · rintro ⟨place, inLive, rfl⟩
    exact ⟨map place, List.mem_map_of_mem inLive, by rw [classSame place inLive, entries _ (classInside place)]⟩

section Moves

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **Live places with the same members have the same entries.** -/
theorem isEntry_of_mem_iff {form : Prenex} (atomic : form.Atomic block.toBlock) {live live' : List Nat}
    (nodup : live.Nodup) (nodup' : live'.Nodup) (inside : ∀ place ∈ live, place < form.components.length)
    (same : ∀ place, place ∈ live ↔ place ∈ live') (pattern : Pattern) :
    IsEntry block form live pattern ↔ IsEntry block form live' pattern := by
  have classPerm : ∀ place, (classIn block form live place).Perm (classIn block form live' place) := by
    intro place
    classical
    have firstNodup : (classIn block form live place).Nodup := by unfold classIn; exact nodup.filter _
    have secondNodup : (classIn block form live' place).Nodup := by unfold classIn; exact nodup'.filter _
    rw [List.perm_ext_iff_of_nodup firstNodup secondNodup]
    intro other
    rw [mem_classIn, mem_classIn, same other, linkedIn_of_mem_iff same]
  have classInside : ∀ place, ∀ other ∈ classIn block form live place, other < form.components.length :=
    fun _ other member => inside other (mem_classIn.mp member).1
  constructor
  · rintro ⟨place, inLive, rfl⟩
    exact ⟨place, (same place).mp inLive,
      (entryOf_perm fresh restrictFresh atomic (classInside place) (classPerm place)).symm⟩
  · rintro ⟨place, inLive, rfl⟩
    exact ⟨place, (same place).mpr inLive, entryOf_perm fresh restrictFresh atomic (classInside place) (classPerm place)⟩

omit fresh restrictFresh in
/-- Dropping unused restrictions renames back to the block. -/
theorem prune_back (form : Prenex) : ∃ embed : Nat → Nat, Preserving form.prune.count form.count embed ∧
    (∀ index, pruneRelabel form.prune.count form.count embed index = index) ∧
    ∀ component ∈ form.components,
      rename embed (rename (Prenex.groupIndex form.count (usedOf form)) component) = component := by
  obtain ⟨count, components⟩ := form
  dsimp only
  set used := usedOf ⟨count, components⟩ with usedIs
  have nodup : used.Nodup := List.nodup_range.filter _
  have usedBelow : ∀ index ∈ used, index < count := fun index member => by
    rw [usedIs] at member
    unfold usedOf at member
    exact List.mem_range.mp (List.mem_filter.mp member).1
  let embed : Nat → Nat := fun index => if index < used.length then used.getD index 0 else index - used.length + count
  have embedBelow : ∀ index (below : index < used.length), embed index = used[index]'below := fun index below => by
    simp only [embed, if_pos below, List.getD_eq_getElem _ _ below]
  have embedAbove : ∀ index, used.length ≤ index → embed index = index - used.length + count := fun index above => by
    simp only [embed, if_neg (by omega : ¬ index < used.length)]
  have countIs : (Prenex.mk count components).prune.count = used.length := by rw [prune_eq]
  refine ⟨embed, ?_, ?_, ?_⟩
  · rw [countIs]
    refine ⟨fun first second same => ?_, fun index below => ?_, fun index above => ?_⟩
    · by_cases firstBelow : first < used.length <;> by_cases secondBelow : second < used.length
      · rw [embedBelow first firstBelow, embedBelow second secondBelow] at same
        exact (nodup.getElem_inj_iff).mp same
      · rw [embedBelow first firstBelow, embedAbove second (by omega)] at same
        have := usedBelow _ (List.getElem_mem firstBelow)
        omega
      · rw [embedAbove first (by omega), embedBelow second secondBelow] at same
        have := usedBelow _ (List.getElem_mem secondBelow)
        omega
      · rw [embedAbove first (by omega), embedAbove second (by omega)] at same
        omega
    · rw [embedBelow index below]
      exact usedBelow _ (List.getElem_mem below)
    · rw [embedAbove index above]
      omega
  · intro index
    rw [countIs]
    unfold pruneRelabel
    rw [embedAbove _ (by omega)]
    omega
  · intro component member
    rw [rename_comp]
    conv_rhs => rw [← rename_id component]
    apply rename_congr
    intro index free
    simp only [Function.comp, id]
    by_cases below : index < count
    · have inUsed : index ∈ used := by
        rw [usedIs]
        simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
        exact ⟨below, component, member, (mentions_iff _ _).mpr free⟩
      rw [groupIndex_below below, embedBelow _ (List.idxOf_lt_length_of_mem inUsed), List.getElem_idxOf]
    · rw [groupIndex_above (by omega), embedAbove _ (by omega)]
      omega

omit fresh restrictFresh in
/-- A place's component mentions a restriction only within the block. -/
theorem mem_components_of_mentions {components : List Pattern} {place restriction : Nat}
    (mentioned : mentions restriction (placeValue block components place) = true) :
    placeValue block components place ∈ components := by
  by_cases inside : place < components.length
  · exact placeValue_mem inside
  · have unitIs : placeValue block components place = .apply block.unit [] := by
      unfold placeValue
      exact List.getD_eq_default _ _ (by omega)
    rw [unitIs, mentions_iff, freeIn_apply] at mentioned
    simp at mentioned

omit fresh restrictFresh in
theorem mem_usedOf_of_mentions {form : Prenex} {place restriction : Nat} (below : restriction < form.count)
    (mentioned : mentions restriction (placeValue block form.components place) = true) :
    restriction ∈ usedOf form := by
  simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
  exact ⟨below, _, mem_components_of_mentions mentioned, mentioned⟩

/-- **Dropping unused restrictions keeps the entries.** -/
theorem isEntry_prune {form : Prenex} (atomic : form.Atomic block.toBlock) (pattern : Pattern) :
    IsEntry block form.prune (places form.prune) pattern ↔ IsEntry block form (places form) pattern := by
  have placesSame : places form.prune = places form := by
    rw [prune_eq]
    simp [places]
  rw [placesSame]
  obtain ⟨embed, preserving, outer, back⟩ := prune_back form
  refine isEntry_congr ?_ ?_ pattern
  · intro first _ second _
    refine shares_image (relabel := Prenex.groupIndex form.count (usedOf form)) ?_ ?_ first second
    · intro place restriction
      simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range]
      rw [prune_eq]
      simp only [placeValue_map_rename, mentions_iff, freeIn_rename]
      constructor
      · rintro ⟨below, original, free, rfl⟩
        by_cases low : original < form.count
        · exact ⟨original, ⟨low, free⟩, rfl⟩
        · rw [groupIndex_above (by omega)] at below
          omega
      · rintro ⟨original, ⟨low, free⟩, rfl⟩
        have inUsed := mem_usedOf_of_mentions (block := block) low ((mentions_iff _ _).mpr free)
        exact ⟨by rw [groupIndex_below low]; exact List.idxOf_lt_length_of_mem inUsed, original, free, rfl⟩
    · intro first second place place' inFirst inSecond same
      simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range] at inFirst inSecond
      have firstUsed := mem_usedOf_of_mentions inFirst.1 inFirst.2
      have secondUsed := mem_usedOf_of_mentions inSecond.1 inSecond.2
      rw [groupIndex_below inFirst.1, groupIndex_below inSecond.1] at same
      exact (List.idxOf_inj firstUsed).mp same
  · intro group inside
    unfold entryOf restrictTo
    have renamedIs : group.map (placeValue block form.prune.components) =
        (group.map (placeValue block form.components)).map (rename (Prenex.groupIndex form.count (usedOf form))) := by
      rw [prune_eq, List.map_map]
      exact List.map_congr_left fun place _ => placeValue_map_rename _ _ _
    have prunedCount : form.prune.count = (usedOf form).length := by rw [prune_eq]
    rw [renamedIs, prunedCount]
    have restrictedAtomic : (Prenex.mk (usedOf form).length ((group.map (placeValue block form.components)).map
        (rename (Prenex.groupIndex form.count (usedOf form))))).Atomic block.toBlock := by
      intro component member
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
      obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp inOriginal
      have inPlaces := inside place inGroup
      exact atomic_rename (atomic _ (placeValue_mem (by simpa [places] using inPlaces))) _
    rw [prunedCount] at preserving outer
    have backList : ((group.map (placeValue block form.components)).map
        (rename (Prenex.groupIndex form.count (usedOf form)))).map (rename embed) =
          group.map (placeValue block form.components) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (group.map (placeValue block form.components))]
      refine List.map_congr_left fun component member => ?_
      obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp member
      exact back _ (placeValue_mem (by simpa [places] using inside place inGroup))
    rw [← normal_rename_eq fresh restrictFresh preserving outer restrictedAtomic, backList]

/-- Reading a block's components again under an order of its restrictions keeps its canonical form. -/
theorem normal_read {count : Nat} {order : List Nat} (isOrder : IsOrder count order) {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock) :
    normal block ⟨count, components.map fun component =>
      recanon block (rename (Prenex.permute count order) component)⟩ = normal block ⟨count, components⟩ := by
  have readAtomic : (Prenex.mk count (components.map fun component =>
      recanon block (rename (Prenex.permute count order) component))).Atomic block.toBlock := by
    intro component member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    have bundle := bundle_all fresh restrictFresh (size original + 1)
    exact recanon_atomic bundle.atomic bundle.nonEmpty (by rw [size_rename]; omega)
      (atomic_rename (atomic original inOriginal) _)
  have similar : SimilarR block ⟨count, components⟩ ⟨count, components.map fun component =>
      recanon block (rename (Prenex.permute count order) component)⟩ := by
    refine ⟨rfl, order, _, isOrder, ?_, List.Perm.refl _⟩
    show List.Forall₂ (AlikeR block) (components.map (rename (Prenex.permute count order))) _
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun component _ => alike_recanon_all fresh restrictFresh _
  exact (normal_similar_all fresh restrictFresh similar atomic readAtomic).symm

/-- **Reading the components again under an order of the restrictions keeps the entries.** -/
theorem isEntry_read {count : Nat} {order : List Nat} (isOrder : IsOrder count order) {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock) (pattern : Pattern) :
    IsEntry block ⟨count, components.map fun component =>
        recanon block (rename (Prenex.permute count order) component)⟩
      (places (Prenex.mk count components)) pattern ↔
      IsEntry block ⟨count, components⟩ (places (Prenex.mk count components)) pattern := by
  have permuteInjective := permute_injective isOrder
  have permuteBelow : ∀ index, index < count → Prenex.permute count order index < count := by
    intro index below
    rw [Prenex.permute, if_pos below, List.getD_eq_getElem _ _ (by rw [isOrder.length]; exact below)]
    exact List.mem_range.mp (isOrder.subset (List.getElem_mem _))
  have readValue : ∀ place, placeValue block (components.map fun component =>
      recanon block (rename (Prenex.permute count order) component)) place =
        recanon block (rename (Prenex.permute count order) (placeValue block components place)) := by
    intro place
    unfold placeValue
    by_cases inside : place < components.length
    · rw [List.getD_eq_getElem _ _ (by simpa using inside), List.getD_eq_getElem _ _ inside, List.getElem_map]
    · rw [List.getD_eq_default _ _ (by simpa using inside), List.getD_eq_default _ _ (by omega)]
      rw [show rename (Prenex.permute count order) (Pattern.apply block.unit []) = .apply block.unit [] from rfl,
        recanon_apply]
      rfl
  refine isEntry_congr ?_ ?_ pattern
  · intro first _ second _
    refine shares_image (relabel := Prenex.permute count order) ?_ ?_ first second
    · intro place restriction
      simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range, readValue, mentions_iff]
      rw [freeIn_recanon (fun pattern _ index => freeIn_canonicalOf fresh restrictFresh pattern index), freeIn_rename]
      constructor
      · rintro ⟨below, original, free, rfl⟩
        by_cases low : original < count
        · exact ⟨original, ⟨low, free⟩, rfl⟩
        · rw [Prenex.permute, if_neg low] at below
          omega
      · rintro ⟨original, ⟨low, free⟩, rfl⟩
        exact ⟨permuteBelow original low, original, free, rfl⟩
    · intro first second _ _ _ _ same
      exact permuteInjective same
  · intro group inside
    unfold entryOf restrictTo
    have readIs : group.map (placeValue block (components.map fun component =>
        recanon block (rename (Prenex.permute count order) component))) =
          (group.map (placeValue block components)).map fun component =>
            recanon block (rename (Prenex.permute count order) component) := by
      rw [List.map_map]
      exact List.map_congr_left fun place _ => readValue place
    simp only
    rw [readIs, normal_read fresh restrictFresh isOrder (fun component member => by
      obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp member
      exact atomic _ (placeValue_mem (by simpa [places] using inside place inGroup)))]

/-- **Permuting the components keeps the entries.** -/
theorem isEntry_perm {count : Nat} {first second : List Pattern} (permutation : first.Perm second)
    (atomic : (Prenex.mk count first).Atomic block.toBlock) (pattern : Pattern) :
    IsEntry block ⟨count, second⟩ (places (Prenex.mk count second)) pattern ↔
      IsEntry block ⟨count, first⟩ (places (Prenex.mk count first)) pattern := by
  obtain ⟨kept, nodup, inside, lengthIs, mapped⟩ := exists_places_perm (block := block) permutation
  have secondAtomic : (Prenex.mk count second).Atomic block.toBlock :=
    fun component member => atomic component (permutation.symm.subset member)
  have lengthSame : first.length = second.length := permutation.length_eq
  have keptIs : (places (Prenex.mk count first)).map (fun place => kept.getD place 0) = kept := by
    simp only [places]
    rw [lengthSame, ← lengthIs]
    apply List.ext_getElem (by simp)
    intro index below _
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem _ _ (by simpa using below)
  have valueIs : ∀ place, place < first.length →
      placeValue block second (kept.getD place 0) = placeValue block first place := by
    intro place below
    have below' : place < kept.length := by omega
    have mappedAt : placeValue block first place = placeValue block second (kept[place]'below') := by
      conv_lhs => rw [← mapped]
      unfold placeValue
      rw [List.getD_eq_getElem _ _ (by simpa using below'), List.getElem_map]
    rw [List.getD_eq_getElem _ _ below', mappedAt]
  rw [← isEntry_map (form := ⟨count, first⟩) (form' := ⟨count, second⟩) (fun place => kept.getD place 0) ?_ ?_ ?_ pattern,
    keptIs]
  · refine isEntry_of_mem_iff fresh restrictFresh secondAtomic (places_nodup _) nodup ?_ ?_ pattern
    · intro place member
      simpa [places] using member
    · intro place
      constructor
      · intro member
        have below : place < second.length := by simpa [places] using member
        have full : kept.toFinset = (places (Prenex.mk count second)).toFinset := by
          apply Finset.eq_of_subset_of_card_le
          · intro other inKept
            simpa [places] using inside other (List.mem_toFinset.mp inKept)
          · rw [List.toFinset_card_of_nodup nodup, List.toFinset_card_of_nodup (places_nodup _), lengthIs]
            simp [places]
        have : place ∈ (places (Prenex.mk count second)).toFinset := List.mem_toFinset.mpr member
        rw [← full] at this
        exact List.mem_toFinset.mp this
      · intro member
        simpa [places] using inside place member
  · intro a aIn b bIn same
    have aBelow : a < kept.length := by simp [places] at aIn; omega
    have bBelow : b < kept.length := by simp [places] at bIn; omega
    rw [List.getD_eq_getElem _ _ aBelow, List.getD_eq_getElem _ _ bBelow] at same
    exact (nodup.getElem_inj_iff).mp same
  · intro a aIn b bIn
    have aBelow : a < first.length := by simpa [places] using aIn
    have bBelow : b < first.length := by simpa [places] using bIn
    simp only [Linked.Shares, keysAt, valueIs a aBelow, valueIs b bBelow]
  · intro group groupInside
    unfold entryOf restrictTo
    simp only [List.map_map]
    congr 4
    refine List.map_congr_left fun place inGroup => ?_
    simp only [Function.comp_apply]
    exact valueIs place (by simpa [places] using groupInside place inGroup)

omit fresh restrictFresh in
theorem classIn_nodup {form : Prenex} {live : List Nat} (nodup : live.Nodup) (place : Nat) :
    (classIn block form live place).Nodup := by
  classical
  unfold classIn
  exact nodup.filter _

omit fresh restrictFresh in
theorem self_mem_classIn {form : Prenex} {live : List Nat} {place : Nat} (inLive : place ∈ live) :
    place ∈ classIn block form live place :=
  mem_classIn.mpr ⟨inLive, Relation.ReflTransGen.refl⟩

omit fresh restrictFresh in
/-- **Linked places have one class.** -/
theorem classIn_perm_of_mem {form : Prenex} {live : List Nat} (nodup : live.Nodup) {place other : Nat}
    (member : other ∈ classIn block form live place) :
    (classIn block form live other).Perm (classIn block form live place) := by
  rw [List.perm_ext_iff_of_nodup (classIn_nodup nodup other) (classIn_nodup nodup place)]
  intro third
  obtain ⟨_, linked⟩ := mem_classIn.mp member
  rw [mem_classIn, mem_classIn]
  exact and_congr_right fun _ => ⟨fun linked' => linked.trans linked', fun linked' => linked.symm.trans linked'⟩

omit fresh restrictFresh in
/-- **A place using no restriction is alone in its class.** -/
theorem classIn_of_keys_nil {form : Prenex} {live : List Nat} (nodup : live.Nodup) {place : Nat}
    (inLive : place ∈ live) (alone : keysAt block form place = []) :
    classIn block form live place = [place] := by
  have isPerm : (classIn block form live place).Perm [place] := by
    rw [List.perm_ext_iff_of_nodup (classIn_nodup nodup place) (List.nodup_singleton place)]
    intro other
    rw [mem_classIn, List.mem_singleton]
    constructor
    · rintro ⟨_, linked⟩
      rcases Relation.ReflTransGen.cases_head linked with same | ⟨next, ⟨_, _, ⟨key, inKeys, _⟩⟩, _⟩
      · exact same.symm
      · rw [alone] at inKeys
        cases inKeys
    · rintro rfl
      exact ⟨inLive, Relation.ReflTransGen.refl⟩
  exact List.perm_singleton.mp isPerm

/-- **Dropping one of two equal replicated places keeps the entries.** -/
theorem isEntry_filter_twin {form : Prenex} (atomic : form.Atomic block.toBlock) {live : List Nat} (nodup : live.Nodup)
    (inside : ∀ place ∈ live, place < form.components.length) {dropped kept : Nat} (droppedLive : dropped ∈ live)
    (keptLive : kept ∈ live) (different : dropped ≠ kept)
    (same : placeValue block form.components dropped = placeValue block form.components kept)
    (replicated : isReplicated block (placeValue block form.components dropped) = true) (pattern : Pattern) :
    IsEntry block form (live.filter fun place => !(place == dropped)) pattern ↔ IsEntry block form live pattern := by
  set rest := live.filter fun place => !(place == dropped) with restIs
  have restNodup : rest.Nodup := nodup.filter _
  have keptRest : kept ∈ rest := List.mem_filter.mpr ⟨keptLive, by simpa using Ne.symm different⟩
  have inRest : ∀ place, place ∈ rest ↔ place ∈ live ∧ place ≠ dropped := by
    intro place
    simp [restIs]
  have keysSame : keysAt block form dropped = keysAt block form kept := by
    unfold keysAt
    rw [same]
  -- paths through the dropped place go through the kept one instead
  have reroute : ∀ first ∈ live, (first == dropped) = false → ∀ second ∈ live, (second == dropped) = false →
      Linked.LinkedIn (keysAt block form) live first second →
      Linked.LinkedIn (keysAt block form) (live.filter fun place => !(place == dropped)) first second := by
    intro first inFirst firstKept second _ secondKept linked
    have firstNot : first ≠ dropped := by simpa using firstKept
    have firstRest : first ∈ rest := (inRest first).mpr ⟨inFirst, firstNot⟩
    suffices general : ∀ target, Linked.LinkedIn (keysAt block form) live first target →
        (target ≠ dropped → Linked.LinkedIn (keysAt block form) rest first target) ∧
        (target = dropped → Linked.LinkedIn (keysAt block form) rest first kept) from
      (general second linked).1 (by simpa using secondKept)
    intro target path
    induction path with
    | refl => exact ⟨fun _ => Relation.ReflTransGen.refl, fun same => absurd same firstNot⟩
    | @tail middle last _ step reached =>
        obtain ⟨inMiddle, inLast, shares⟩ := step
        obtain ⟨throughMiddle, throughDropped⟩ := reached
        constructor
        · intro lastNot
          have lastRest : last ∈ rest := (inRest last).mpr ⟨inLast, lastNot⟩
          by_cases middleIs : middle = dropped
          · subst middleIs
            have toKept := throughDropped rfl
            obtain ⟨key, inMiddleKeys, inLastKeys⟩ := shares
            rw [keysSame] at inMiddleKeys
            exact toKept.tail ⟨keptRest, lastRest, ⟨key, inMiddleKeys, inLastKeys⟩⟩
          · exact (throughMiddle middleIs).tail ⟨(inRest middle).mpr ⟨inMiddle, middleIs⟩, lastRest, shares⟩
        · intro lastIs
          subst lastIs
          by_cases middleIs : middle = last
          · exact throughDropped middleIs
          · have toMiddle := throughMiddle middleIs
            obtain ⟨key, inMiddleKeys, inLastKeys⟩ := shares
            rw [keysSame] at inLastKeys
            by_cases middleKept : middle = kept
            · rw [← middleKept]
              exact toMiddle
            · exact toMiddle.tail ⟨(inRest middle).mpr ⟨inMiddle, middleIs⟩, keptRest, ⟨key, inMiddleKeys, inLastKeys⟩⟩
  have classFilter := fun place inLive keptPlace => classIn_filter (block := block) (form := form) (live := live)
    (fun place => place == dropped) reroute (place := place) inLive keptPlace
  have classInside : ∀ place, ∀ other ∈ classIn block form live place, other < form.components.length :=
    fun _ other member => inside other (mem_classIn.mp member).1
  -- the entry of a class without the dropped place
  have entryWithout : ∀ place ∈ live, place ≠ dropped →
      entryOf block form (classIn block form rest place) = entryOf block form (classIn block form live place) := by
    intro place inLive notDropped
    have filtered : (classIn block form rest place).Perm
        ((classIn block form live place).filter fun place => !(place == dropped)) := by
      rw [List.perm_ext_iff_of_nodup (classIn_nodup restNodup place) ((classIn_nodup nodup place).filter _)]
      exact classFilter place inLive (by simpa using notDropped)
    have filteredInside : ∀ other ∈ classIn block form rest place, other < form.components.length :=
      fun other member => inside other ((inRest other).mp (mem_classIn.mp member).1).1
    rw [entryOf_perm fresh restrictFresh atomic filteredInside filtered]
    by_cases droppedIn : dropped ∈ classIn block form live place
    · -- the dropped place is a duplicate of the kept one in the class
      have keptIn : kept ∈ classIn block form live place := by
        obtain ⟨_, toDropped⟩ := mem_classIn.mp droppedIn
        rcases Relation.ReflTransGen.cases_head toDropped.symm with isPlace | ⟨next, ⟨_, _, ⟨key, inKeys, _⟩⟩, _⟩
        · exact absurd isPlace notDropped.symm
        · have keyShared : Linked.Shares (keysAt block form) dropped kept := ⟨key, inKeys, keysSame ▸ inKeys⟩
          exact mem_classIn.mpr ⟨keptLive, toDropped.tail ⟨droppedLive, keptLive, keyShared⟩⟩
      have classPerm : (classIn block form live place).Perm
          (dropped :: (classIn block form live place).filter fun place => !(place == dropped)) := by
        rw [List.perm_ext_iff_of_nodup (classIn_nodup nodup place)
          (List.nodup_cons.mpr ⟨by simp, (classIn_nodup nodup place).filter _⟩)]
        intro other
        simp only [List.mem_cons, List.mem_filter, Bool.not_eq_true']
        constructor
        · intro member
          by_cases isDropped : other = dropped
          · exact .inl isDropped
          · exact .inr ⟨member, by simpa using isDropped⟩
        · rintro (rfl | ⟨member, _⟩)
          · exact droppedIn
          · exact member
      rw [entryOf_perm fresh restrictFresh atomic (classInside place) classPerm]
      unfold entryOf restrictTo
      simp only [List.map_cons]
      rw [normal_duplicate fresh restrictFresh _ _ _ _ (Nat.lt_succ_self _)
        (fun component member => by
          rcases List.mem_cons.mp member with rfl | inRest'
          · exact atomic _ (placeValue_mem (inside dropped droppedLive))
          · obtain ⟨other, inOther, rfl⟩ := List.mem_map.mp inRest'
            exact atomic _ (placeValue_mem (classInside place other (List.mem_filter.mp inOther).1)))
        (by
          rw [same]
          exact List.mem_map_of_mem (List.mem_filter.mpr ⟨keptIn, by simpa using Ne.symm different⟩))
        replicated]
    · congr 1
      rw [List.filter_eq_self.mpr]
      intro other member
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne]
      rintro rfl
      exact droppedIn member
  constructor
  · rintro ⟨place, inPlace, rfl⟩
    obtain ⟨inLive, notDropped⟩ := (inRest place).mp inPlace
    exact ⟨place, inLive, (entryWithout place inLive notDropped).symm⟩
  · rintro ⟨place, inLive, rfl⟩
    by_cases isDropped : place = dropped
    · subst isDropped
      by_cases alone : keysAt block form place = []
      · -- the dropped place is alone, and so is the kept one, with the same entry
        have keptAlone : keysAt block form kept = [] := keysSame ▸ alone
        refine ⟨kept, keptRest, ?_⟩
        rw [classIn_of_keys_nil restNodup keptRest keptAlone, classIn_of_keys_nil nodup inLive alone]
        unfold entryOf restrictTo
        simp only [List.map_cons, List.map_nil, same]
      · -- the kept place is in its class
        obtain ⟨key, inKeys⟩ := List.exists_mem_of_ne_nil _ alone
        have keptIn : kept ∈ classIn block form live place :=
          mem_classIn.mpr ⟨keptLive, Linked.LinkedIn.single inLive keptLive ⟨key, inKeys, keysSame ▸ inKeys⟩⟩
        refine ⟨kept, keptRest, ?_⟩
        rw [entryWithout kept keptLive (Ne.symm different)]
        exact entryOf_perm fresh restrictFresh atomic (classInside kept) (classIn_perm_of_mem nodup keptIn)
    · exact ⟨place, (inRest place).mpr ⟨inLive, isDropped⟩, entryWithout place inLive isDropped⟩

/-- **Dropping a replicated duplicate keeps the entries.** -/
theorem isEntry_cons_duplicate {count : Nat} {duplicate : Pattern} {components : List Pattern}
    (member : duplicate ∈ components) (replicated : isReplicated block duplicate = true)
    (atomic : (Prenex.mk count (duplicate :: components)).Atomic block.toBlock) (pattern : Pattern) :
    IsEntry block ⟨count, duplicate :: components⟩ (places (Prenex.mk count (duplicate :: components))) pattern ↔
      IsEntry block ⟨count, components⟩ (places (Prenex.mk count components)) pattern := by
  have twinBelow : components.idxOf duplicate < components.length := List.idxOf_lt_length_of_mem member
  have valueTwin : placeValue block (duplicate :: components) (components.idxOf duplicate + 1) = duplicate := by
    rw [placeValue_cons_succ]
    unfold placeValue
    rw [List.getD_eq_getElem _ _ twinBelow, List.getElem_idxOf]
  have zeroLive : 0 ∈ places (Prenex.mk count (duplicate :: components)) := by simp [places]
  have twinLive : components.idxOf duplicate + 1 ∈ places (Prenex.mk count (duplicate :: components)) := by
    simp [places]
    omega
  rw [← isEntry_filter_twin fresh restrictFresh atomic (places_nodup _)
    (fun place member => by simpa [places] using member) zeroLive twinLive (by omega)
    (by rw [valueTwin]; rfl) replicated pattern]
  have restNodup : ((places (Prenex.mk count (duplicate :: components))).filter fun place => !(place == 0)).Nodup :=
    (places_nodup _).filter _
  have shiftedNodup : ((places (Prenex.mk count components)).map (· + 1)).Nodup :=
    (places_nodup _).map fun a b same => by omega
  rw [isEntry_of_mem_iff fresh restrictFresh atomic restNodup shiftedNodup
    (fun place member => by
      have := (List.mem_filter.mp member).1
      simpa [places] using this)
    (fun place => by
      simp only [places, List.mem_filter, List.mem_range, List.mem_map, List.length_cons, Bool.not_eq_true',
        beq_eq_false_iff_ne]
      constructor
      · rintro ⟨below, notZero⟩
        exact ⟨place - 1, by omega, by omega⟩
      · rintro ⟨original, below, rfl⟩
        exact ⟨by omega, by omega⟩) pattern]
  refine isEntry_map (form := ⟨count, components⟩) (form' := ⟨count, duplicate :: components⟩) (· + 1)
    (fun a _ b _ same => by omega) (fun a _ b _ => Iff.rfl) ?_ pattern
  intro group _
  unfold entryOf restrictTo
  simp only [List.map_map]
  rfl

/-- **Keeping one of each replicated component keeps the entries.** -/
theorem isEntry_dedupReplicated {count : Nat} :
    ∀ (components extra : List Pattern), (Prenex.mk count (extra ++ components)).Atomic block.toBlock →
      ∀ pattern, IsEntry block ⟨count, extra ++ dedupReplicated block components⟩
          (places (Prenex.mk count (extra ++ dedupReplicated block components))) pattern ↔
        IsEntry block ⟨count, extra ++ components⟩ (places (Prenex.mk count (extra ++ components))) pattern
  | [], _, _, _ => Iff.rfl
  | component :: rest, extra, atomic, pattern => by
      unfold dedupReplicated
      split_ifs with drop
      · simp only [Bool.and_eq_true, List.contains_iff_mem] at drop
        have restAtomic : (Prenex.mk count (extra ++ rest)).Atomic block.toBlock := fun other member =>
          atomic other (by
            rcases List.mem_append.mp member with inExtra | inRest
            · exact List.mem_append_left _ inExtra
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ inRest))
        rw [isEntry_dedupReplicated rest extra restAtomic pattern]
        have permutation : (component :: (extra ++ rest)).Perm (extra ++ component :: rest) :=
          List.perm_middle.symm
        have consAtomic : (Prenex.mk count (component :: (extra ++ rest))).Atomic block.toBlock :=
          fun other member => atomic other (permutation.subset member)
        rw [isEntry_perm fresh restrictFresh permutation consAtomic,
          isEntry_cons_duplicate fresh restrictFresh (List.mem_append_right _ drop.2) drop.1 consAtomic]
      · have moved : extra ++ component :: dedupReplicated block rest =
            (extra ++ [component]) ++ dedupReplicated block rest := by simp
        have moved' : extra ++ component :: rest = (extra ++ [component]) ++ rest := by simp
        rw [moved, moved']
        exact isEntry_dedupReplicated rest (extra ++ [component]) (moved' ▸ atomic) pattern

end Moves

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
