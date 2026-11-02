import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationIdem

/-!
# Canonical blocks side by side

A copy group of a block stays one beside another block, which shares none of its restrictions
(`removes_union`, `append_iso`), so absorbing a block beside another removes the first one's copy groups
(`normal_par_absorbed`); its unused restrictions then go (`normal_par_prune`) and its components can be read again
under an order of its restrictions (`normal_par_reading`). Hence the canonical form of blocks side by side reads each
block only through its canonical form (`normal_par_normal_left`, `normal_par_normal_right`), and blocks side by side
commute (`normal_par_comm`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)

variable {block : ReplicationBlock}

/-! ## Copy groups among more components -/

/-- **A copy group stays one among more live components** none of which it links to. -/
theorem isCopy_union {system : CopyGroups.System Nat} {live extra : Finset Nat} {p : Nat} {group : Finset Nat}
    (isCopy : system.IsCopy live p group)
    (apart : ∀ member ∈ group, ∀ other ∈ extra, ¬ system.LinkFor p member other) :
    system.IsCopy (live ∪ extra) p group := by
  refine ⟨Finset.mem_union_left _ isCopy.isLive, isCopy.isReplicated,
    ⟨fun member inGroup => ?_, isCopy.isGroup.nonempty, isCopy.isGroup.linked,
      fun first inFirst second inSecond link => ?_⟩, isCopy.isCopy⟩
  · obtain ⟨different, inLive⟩ := Finset.mem_erase.mp (isCopy.isGroup.subset inGroup)
    exact Finset.mem_erase.mpr ⟨different, Finset.mem_union_left _ inLive⟩
  · obtain ⟨different, inUnion⟩ := Finset.mem_erase.mp inSecond
    rcases Finset.mem_union.mp inUnion with inLive | inExtra
    · exact isCopy.isGroup.closed first inFirst second (Finset.mem_erase.mpr ⟨different, inLive⟩) link
    · exact absurd link (apart first inFirst second inExtra)

/-- **Removing copy groups among more components**: a complete removal on some components removes the same
groups among them and others. -/
theorem removes_union {system other : CopyGroups.System Nat} {live final extra : Finset Nat}
    (absorbs : system.Absorbs live final) :
    Disjoint live extra →
    (∀ live' ⊆ live, ∀ p group, system.IsCopy live' p group → other.IsCopy (live' ∪ extra) p group) →
    other.Removes (live ∪ extra) (final ∪ extra) := by
  induction absorbs with
  | done => exact fun _ _ => .refl
  | @step live final p copied isCopy _ recurse =>
      intro disjoint transfer
      have restDisjoint : Disjoint (live \ copied) extra :=
        Finset.disjoint_of_subset_left Finset.sdiff_subset disjoint
      have rest := recurse restDisjoint fun live' inside => transfer live' (inside.trans Finset.sdiff_subset)
      have isCopy' := transfer live (Finset.Subset.refl _) p copied isCopy
      have unionRest : (live ∪ extra) \ copied = (live \ copied) ∪ extra := by
        ext member
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨inLive | inExtra, notCopied⟩
          · exact .inl ⟨inLive, notCopied⟩
          · exact .inr inExtra
        · rintro (⟨inLive, notCopied⟩ | inExtra)
          · exact ⟨.inl inLive, notCopied⟩
          · refine ⟨.inr inExtra, fun inCopied => ?_⟩
            have inLive := (Finset.mem_erase.mp (isCopy.isGroup.subset inCopied)).2
            exact Finset.disjoint_left.mp disjoint inLive inExtra
      exact .step isCopy' (by rw [unionRest]; exact rest)

/-- The components of a block are those of a longer block at their places. -/
theorem placeValue_append_left {first second : List Pattern} {place : Nat} (inside : place < first.length) :
    placeValue block (first ++ second) place = placeValue block first place := by
  unfold placeValue
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ inside, List.getElem_append_left]

theorem placeValue_append_right {first second : List Pattern} {offset : Nat} (inside : offset < second.length) :
    placeValue block (first ++ second) (first.length + offset) = placeValue block second offset := by
  unfold placeValue
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ inside, List.getElem_append_right (by omega)]
  simp

/-- **The system of a block is the system of a longer block on its places.** -/
theorem append_iso (count : Nat) (first second : List Pattern) :
    (blockSystem block ⟨count, first⟩).Iso (blockSystem block ⟨count, first ++ second⟩)
      (places ⟨count, first⟩).toFinset id id where
  injective := fun _ _ _ _ same => same
  relabelInjective := fun _ _ same => same
  mentions := fun place inPlaces => by
    have inside : place < first.length := by simpa [places] using inPlaces
    simp only [blockSystem, absorptionSystem, id, Finset.image_id]
    rw [placeValue_append_left inside]
  replicated := fun place inPlaces => by
    have inside : place < first.length := by simpa [places] using inPlaces
    simp only [blockSystem, absorptionSystem, id]
    rw [placeValue_append_left inside]
  copy := fun group groupInside p pIn _ _ => by
    have inside : p < first.length := by simpa [places] using pIn
    rw [Finset.image_id]
    show CopyTest block (canonicalOf block) count (placeValue block (first ++ second) p)
        (asGroup (allowedFor count (placeValue block (first ++ second) p)) count (placeValue block (first ++ second))
          (group.sort (· ≤ ·))) ↔
      CopyTest block (canonicalOf block) count (placeValue block first p)
        (asGroup (allowedFor count (placeValue block first p)) count (placeValue block first) (group.sort (· ≤ ·)))
    rw [placeValue_append_left inside, asGroup_map (move := id) (second := placeValue block first) fun place member => by
      have inGroup : place ∈ group := (Finset.mem_sort _).mp member
      have placeInside : place < first.length := by simpa [places] using groupInside inGroup
      exact placeValue_append_left placeInside, List.map_id]
  height := fun place inPlaces _ => by
    have inside : place < first.length := by simpa [places] using inPlaces
    simp only [blockSystem, absorptionSystem, id]
    rw [placeValue_append_left inside]

/-! ## Renamings and readings in context -/

/-- **A renaming keeping a block's restrictions and its outside keeps its canonical form.** -/
theorem normal_rename_eq (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) {count count' : Nat} {relabel : Nat → Nat}
    (preserving : Preserving count count' relabel) (outer : ∀ index, pruneRelabel count count' relabel index = index)
    {components : List Pattern} (atomic : (Prenex.mk count components).Atomic block.toBlock) :
    normal block ⟨count', components.map (rename relabel)⟩ = normal block ⟨count, components⟩ := by
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh atomic
  obtain ⟨final, _, _, normalIs, renamedIs⟩ :=
    normal_rename preserving (below_all fresh restrictFresh _) atomic laws blind
  rw [renamedIs, normalIs, renameOuter_of_id outer]

/-- Keeping one of each replicated component commutes with an injective renaming. -/
theorem dedupReplicated_map {read : Pattern → Pattern} (injective : Function.Injective read)
    (replicated : ∀ component, isReplicated block (read component) = isReplicated block component) :
    ∀ (components : List Pattern), dedupReplicated block (components.map read) = (dedupReplicated block components).map read
  | [] => rfl
  | component :: rest => by
      have containsSame : (rest.map read).contains (read component) = rest.contains component := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_map]
        exact ⟨fun ⟨other, member, same⟩ => injective same ▸ member, fun member => ⟨component, member, rfl⟩⟩
      simp only [List.map_cons]
      unfold dedupReplicated
      rw [replicated, containsSame]
      split_ifs
      · exact dedupReplicated_map injective replicated rest
      · rw [List.map_cons, dedupReplicated_map injective replicated rest]

theorem par_atomic {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock) : (first.par second).Atomic block.toBlock := by
  intro component member
  simp only [Prenex.par, List.mem_append, List.mem_map] at member
  rcases member with ⟨original, inFirst, rfl⟩ | ⟨original, inSecond, rfl⟩
  · rw [liftBVars_eq_rename]
    exact atomic_rename (firstAtomic original inFirst) _
  · rw [liftBVars_eq_rename]
    exact atomic_rename (secondAtomic original inSecond) _

/-- **Blocks side by side commute**, up to the order of their restrictions. -/
theorem par_comm_similarR (first second : Prenex) : SimilarR block (first.par second) (second.par first) := by
  obtain ⟨a, firstComponents⟩ := first
  obtain ⟨b, secondComponents⟩ := second
  have isOrder : IsOrder (a + b) (exchangeBlocks a b) := by
    simpa [Nat.add_comm] using exchangeBlocks_isOrder a b
  have permuted : Prenex.permute (a + b) (exchangeBlocks a b) =
      fun index => if index < b then index + a else if index < b + a then index - b else index := by
    rw [Nat.add_comm, permute_exchangeBlocks]
  have firstPart : (rename (fun index => if index < b then index + a else if index < b + a then index - b else index) ∘
      liftBVars 0 b) = liftBVars a b := by
    funext component
    simp only [Function.comp, liftBVars_eq_rename, rename_comp]
    congr 1
    funext index
    simp only [Function.comp, shiftAbove]
    split_ifs <;> omega
  have secondPart : (rename (fun index => if index < b then index + a else if index < b + a then index - b else index) ∘
      liftBVars b a) = liftBVars 0 a := by
    funext component
    simp only [Function.comp, liftBVars_eq_rename, rename_comp]
    congr 1
    funext index
    simp only [Function.comp, shiftAbove]
    split_ifs <;> omega
  refine ⟨by simp [Prenex.par]; omega, exchangeBlocks a b,
    firstComponents.map (liftBVars a b) ++ secondComponents.map (liftBVars 0 a), isOrder, ?_, ?_⟩
  · show List.Forall₂ (AlikeR block) ((firstComponents.map (liftBVars 0 b) ++ secondComponents.map (liftBVars b a)).map
      (rename (Prenex.permute (a + b) (exchangeBlocks a b)))) _
    rw [permuted, List.map_append, List.map_map, List.map_map, firstPart, secondPart]
    exact List.forall₂_same.mpr fun component _ => AlikeR.refl component
  · exact List.perm_append_comm

/-- The components of a canonical block are atoms. -/
theorem normal_atomic_of {bound : Nat} (bundle : Bundle block bound) {form : Prenex} (atomic : form.Atomic block.toBlock)
    (small : ∀ component ∈ form.components, size component ≤ bound) : (normal block form).Atomic block.toBlock := by
  rw [normal_eq_reading]
  intro component member
  obtain ⟨order, _, leastIs⟩ := least_reading_mem (block := block) (absorb block (canonicalOf block) form)
  simp only at member
  rw [leastIs] at member
  obtain ⟨absorbed, inAbsorbed, rfl⟩ := mem_reading member
  obtain ⟨original, inOriginal, relabel, rfl⟩ := mem_absorb inAbsorbed
  refine recanon_atomic bundle.atomic bundle.nonEmpty ?_ (atomic_rename (atomic_rename (atomic _ inOriginal) _) _)
  rw [size_rename, size_rename]
  exact small original inOriginal

theorem prune_atomic {form : Prenex} (atomic : form.Atomic block.toBlock) : form.prune.Atomic block.toBlock := by
  rw [prune_eq]
  exact atomic_map_rename atomic _

section Par

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **A canonical block of atoms is a block of atoms.** -/
theorem normal_atomic {form : Prenex} (atomic : form.Atomic block.toBlock) : (normal block form).Atomic block.toBlock :=
  normal_atomic_of (bundle_all fresh restrictFresh (sizeList form.components + 1)) atomic
    fun _ member => (size_lt_of_mem member).trans (Nat.le_succ _)

/-- **Blocks side by side have one canonical form in either order.** -/
theorem normal_par_comm {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock) :
    normal block (first.par second) = normal block (second.par first) :=
  normal_similar_all fresh restrictFresh (par_comm_similarR first second) (par_atomic firstAtomic secondAtomic)
    (par_atomic secondAtomic firstAtomic)

/-- **Absorbing a block beside another removes the first one's copy groups.** -/
theorem normal_par_absorbed {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock) {final : List Nat} (nodup : final.Nodup)
    (absorbs : (blockSystem block first).Absorbs (places first).toFinset final.toFinset) :
    normal block (first.par second) =
      normal block ((Prenex.mk first.count (final.map (placeValue block first.components))).par second) := by
  obtain ⟨a, firstComponents⟩ := first
  obtain ⟨b, secondComponents⟩ := second
  show normal block ((Prenex.mk a firstComponents).par ⟨b, secondComponents⟩) =
    normal block ((Prenex.mk a (final.map (placeValue block firstComponents))).par ⟨b, secondComponents⟩)
  set lifted := firstComponents.map (rename (shiftAbove 0 b)) with liftedIs
  set others := secondComponents.map (rename (shiftAbove b a)) with othersIs
  have liftedEq : firstComponents.map (liftBVars 0 b) = lifted :=
    List.map_congr_left fun component _ => liftBVars_eq_rename 0 b component
  have othersEq : secondComponents.map (liftBVars b a) = others :=
    List.map_congr_left fun component _ => liftBVars_eq_rename b a component
  have lengthIs : lifted.length = firstComponents.length := by simp [liftedIs]
  have parIs : (Prenex.mk a firstComponents).par ⟨b, secondComponents⟩ = ⟨a + b, lifted ++ others⟩ := by
    simp only [Prenex.par, liftedEq, othersEq]
  have finalInside : ∀ place ∈ final, place < firstComponents.length := fun place member => by
    have := absorbs_subset absorbs (List.mem_toFinset.mpr member)
    simpa [places] using this
  -- the first block's copy groups, renamed and beside the second block
  have preserving : Preserving a (a + b) (shiftAbove 0 b) := by
    refine ⟨fun first second same => ?_, fun index below => ?_, fun index above => ?_⟩
    · simp only [shiftAbove, Nat.not_lt_zero, if_false] at same
      omega
    · simp only [shiftAbove, Nat.not_lt_zero, if_false]
      omega
    · simp only [shiftAbove, Nat.not_lt_zero, if_false]
      omega
  have renamedIso := rename_iso preserving (below_all fresh restrictFresh _) firstAtomic
  have appendIso := append_iso (block := block) (a + b) lifted others
  have placesSame : (places (Prenex.mk (a + b) lifted)).toFinset = (places (Prenex.mk a firstComponents)).toFinset := by
    simp [places, liftedIs]
  set extra := ((List.range others.length).map (firstComponents.length + ·)).toFinset with extraIs
  have liftedMentions : ∀ place ∈ (places (Prenex.mk a firstComponents)).toFinset, ∀ restriction ∈
      (blockSystem block ⟨a + b, lifted ++ others⟩).mentions place, b ≤ restriction := by
    intro place inPlaces restriction mentioned
    have inside : place < firstComponents.length := by simpa [places] using inPlaces
    have mentionedIs : restriction ∈ (usedRestrictions (a + b) (placeValue block (lifted ++ others) place)).toFinset :=
      mentioned
    rw [List.mem_toFinset, mem_usedRestrictions, placeValue_append_left (by rw [lengthIs]; exact inside), liftedIs,
      placeValue_map_rename, mentions_iff, freeIn_rename] at mentionedIs
    obtain ⟨_, original, _, maps⟩ := mentionedIs
    simp only [shiftAbove, Nat.not_lt_zero, if_false] at maps
    omega
  have othersMentions : ∀ place ∈ extra, ∀ restriction ∈ (blockSystem block ⟨a + b, lifted ++ others⟩).mentions place,
      restriction < b := by
    intro place inExtra restriction mentioned
    simp only [extraIs, List.mem_toFinset, List.mem_map, List.mem_range] at inExtra
    obtain ⟨offset, inside, rfl⟩ := inExtra
    have mentionedIs : restriction ∈ (usedRestrictions (a + b)
        (placeValue block (lifted ++ others) (firstComponents.length + offset))).toFinset := mentioned
    rw [← lengthIs, List.mem_toFinset, mem_usedRestrictions, placeValue_append_right inside, othersIs,
      placeValue_map_rename, mentions_iff, freeIn_rename] at mentionedIs
    obtain ⟨below, original, _, maps⟩ := mentionedIs
    simp only [shiftAbove] at maps
    split_ifs at maps <;> omega
  have transfer : ∀ live' ⊆ (places (Prenex.mk a firstComponents)).toFinset, ∀ p group,
      (blockSystem block ⟨a, firstComponents⟩).IsCopy live' p group →
        (blockSystem block ⟨a + b, lifted ++ others⟩).IsCopy (live' ∪ extra) p group := by
    intro live' inside p group isCopy
    have renamedCopy := ((renamedIso.mono inside).isCopy_iff isCopy.isLive
      (fun member inGroup => (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup)).2)).mpr isCopy
    simp only [Finset.image_id, id] at renamedCopy
    have inside' : live' ⊆ (places (Prenex.mk (a + b) lifted)).toFinset := by
      rw [placesSame]
      exact inside
    have appendedCopy := ((appendIso.mono inside').isCopy_iff renamedCopy.isLive
      (fun member inGroup => (Finset.mem_erase.mp (renamedCopy.isGroup.subset inGroup)).2)).mpr renamedCopy
    simp only [Finset.image_id, id] at appendedCopy
    refine isCopy_union appendedCopy fun member inGroup other inExtra link => ?_
    obtain ⟨restriction, inMember, inOther, _⟩ := link
    have memberPlaces := inside (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup)).2
    have := liftedMentions member memberPlaces restriction inMember
    have := othersMentions other inExtra restriction inOther
    omega
  have disjoint : Disjoint (places (Prenex.mk a firstComponents)).toFinset extra := by
    rw [Finset.disjoint_left]
    intro place inPlaces inExtra
    have inside : place < firstComponents.length := by simpa [places] using inPlaces
    simp only [extraIs, List.mem_toFinset, List.mem_map, List.mem_range] at inExtra
    obtain ⟨offset, _, rfl⟩ := inExtra
    omega
  have removes := removes_union absorbs disjoint transfer
  -- the places of the blocks side by side
  have parPlaces : (places (Prenex.mk (a + b) (lifted ++ others))).toFinset =
      (places (Prenex.mk a firstComponents)).toFinset ∪ extra := by
    ext place
    simp only [places, extraIs, List.mem_toFinset, List.mem_range, Finset.mem_union, List.mem_map, List.length_append,
      lengthIs]
    constructor
    · intro below
      by_cases low : place < firstComponents.length
      · exact .inl low
      · exact .inr ⟨place - firstComponents.length, by omega, by omega⟩
    · rintro (low | ⟨offset, inside, rfl⟩) <;> omega
  set kept := final ++ (List.range others.length).map (firstComponents.length + ·) with keptIs
  have keptSet : kept.toFinset = final.toFinset ∪ extra := by
    rw [keptIs, extraIs, List.toFinset_append]
  have keptNodup : kept.Nodup := by
    rw [keptIs]
    refine List.nodup_append.mpr ⟨nodup, List.nodup_range.map fun _ _ same => by omega, ?_⟩
    intro place inFinal other inOthers same
    obtain ⟨offset, _, rfl⟩ := List.mem_map.mp inOthers
    have := finalInside place inFinal
    omega
  have keptInside : ∀ place ∈ kept, place < (lifted ++ others).length := by
    intro place member
    simp only [List.length_append, lengthIs]
    rcases List.mem_append.mp member with inFinal | inOthers
    · have := finalInside place inFinal
      omega
    · obtain ⟨offset, inside, rfl⟩ := List.mem_map.mp inOthers
      have := List.mem_range.mp inside
      omega
  have parAtomic := par_atomic (block := block) firstAtomic secondAtomic
  rw [parIs] at parAtomic
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh parAtomic
  have restricted := normal_restrict laws blind keptNodup keptInside (by rw [parPlaces, keptSet]; exact removes)
  -- the kept places read as the absorbed first block beside the second
  have firstPart : final.map (placeValue block (lifted ++ others)) =
      (final.map (placeValue block firstComponents)).map (liftBVars 0 b) := by
    rw [List.map_map]
    refine List.map_congr_left fun place member => ?_
    have inside := finalInside place member
    rw [Function.comp_apply, placeValue_append_left (by rw [lengthIs]; exact inside), liftedIs, placeValue_map_rename,
      liftBVars_eq_rename]
  have secondPart : ((List.range others.length).map (firstComponents.length + ·)).map
      (placeValue block (lifted ++ others)) = others := by
    rw [List.map_map]
    have pointwise : ∀ offset ∈ List.range others.length,
        (placeValue block (lifted ++ others) ∘ (firstComponents.length + ·)) offset = placeValue block others offset := by
      intro offset member
      rw [Function.comp_apply, ← lengthIs]
      exact placeValue_append_right (List.mem_range.mp member)
    rw [List.map_congr_left pointwise, map_range_placeValue]
  have restrictedIs : restrictTo block ⟨a + b, lifted ++ others⟩ kept =
      (Prenex.mk a (final.map (placeValue block firstComponents))).par ⟨b, secondComponents⟩ := by
    simp only [restrictTo, Prenex.par, keptIs, List.map_append, firstPart, secondPart, othersEq]
  rw [parIs, ← restricted, restrictedIs]

/-- **Dropping a block's unused restrictions beside another block keeps the canonical form.** -/
theorem normal_par_prune {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock) :
    normal block (first.prune.par second) = normal block (first.par second) := by
  obtain ⟨a, firstComponents⟩ := first
  obtain ⟨b, secondComponents⟩ := second
  set used := usedOf ⟨a, firstComponents⟩ with usedIs
  have nodup : used.Nodup := List.nodup_range.filter _
  have usedBelow : ∀ index ∈ used, index < a := fun index member => by
    rw [usedIs] at member
    unfold usedOf at member
    exact List.mem_range.mp (List.mem_filter.mp member).1
  have usedValue : ∀ position (below : position < used.length), used.getD position 0 = used[position] :=
    fun position below => List.getD_eq_getElem _ _ below
  -- the second block's restrictions stay, the first one's go back in place, the outside moves past them
  let back : Nat → Nat := fun index =>
    if index < b then index else if index < used.length + b then used.getD (index - b) 0 + b
    else index - used.length + a
  have backLow : ∀ index, index < b → back index = index := fun index low => by simp only [back, if_pos low]
  have backMiddle : ∀ index (low : b ≤ index) (high : index < used.length + b),
      back index = used[index - b]'(by omega) + b := fun index low high => by
    have position : index - b < used.length := by omega
    simp only [back, if_neg (by omega : ¬ index < b), if_pos high]
    rw [usedValue _ position]
  have backHigh : ∀ index, used.length + b ≤ index → back index = index - used.length + a := fun index high => by
    simp only [back, if_neg (by omega : ¬ index < b), if_neg (by omega : ¬ index < used.length + b)]
  have preserving : Preserving (used.length + b) (a + b) back := by
    refine ⟨fun first second same => ?_, fun index below => ?_, fun index above => ?_⟩
    · by_cases firstLow : first < b <;> by_cases secondLow : second < b
      · rwa [backLow _ firstLow, backLow _ secondLow] at same
      · by_cases secondHigh : second < used.length + b
        · rw [backLow _ firstLow, backMiddle _ (by omega) secondHigh] at same
          omega
        · rw [backLow _ firstLow, backHigh _ (by omega)] at same
          omega
      · by_cases firstHigh : first < used.length + b
        · rw [backMiddle _ (by omega) firstHigh, backLow _ secondLow] at same
          omega
        · rw [backHigh _ (by omega), backLow _ secondLow] at same
          omega
      · by_cases firstHigh : first < used.length + b <;> by_cases secondHigh : second < used.length + b
        · have firstPosition : first - b < used.length := by omega
          have secondPosition : second - b < used.length := by omega
          rw [backMiddle _ (by omega) firstHigh, backMiddle _ (by omega) secondHigh] at same
          have := (nodup.getElem_inj_iff).mp (by omega : used[first - b]'firstPosition = used[second - b]'secondPosition)
          omega
        · rw [backMiddle _ (by omega) firstHigh, backHigh _ (by omega)] at same
          have := usedBelow _ (List.getElem_mem (by omega : first - b < used.length))
          omega
        · rw [backHigh _ (by omega), backMiddle _ (by omega) secondHigh] at same
          have := usedBelow _ (List.getElem_mem (by omega : second - b < used.length))
          omega
        · rw [backHigh _ (by omega), backHigh _ (by omega)] at same
          omega
    · by_cases low : index < b
      · rw [backLow _ low]
        omega
      · rw [backMiddle _ (by omega) below]
        have := usedBelow _ (List.getElem_mem (by omega : index - b < used.length))
        omega
    · rw [backHigh _ above]
      omega
  have outer : ∀ index, pruneRelabel (used.length + b) (a + b) back index = index := by
    intro index
    unfold pruneRelabel
    rw [backHigh _ (by omega)]
    omega
  -- the pruned block beside the second, renamed back, is the block beside the second
  have prunedIs : (Prenex.mk a firstComponents).prune = ⟨used.length,
      firstComponents.map (rename (Prenex.groupIndex a used))⟩ := prune_eq _
  have prunedAtomic := par_atomic (prune_atomic firstAtomic) secondAtomic
  rw [prunedIs] at prunedAtomic
  have renamed := normal_rename_eq fresh restrictFresh preserving outer prunedAtomic
  have componentsSame : ((Prenex.mk used.length (firstComponents.map (rename (Prenex.groupIndex a used)))).par
      ⟨b, secondComponents⟩).components.map (rename back) =
      ((Prenex.mk a firstComponents).par ⟨b, secondComponents⟩).components := by
    simp only [Prenex.par, List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun component member => ?_
      simp only [Function.comp_apply, liftBVars_eq_rename, rename_comp]
      apply rename_congr
      intro index free
      simp only [Function.comp]
      by_cases below : index < a
      · have inUsed : index ∈ used := by
          rw [usedIs]
          simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
          exact ⟨below, component, member, (mentions_iff _ _).mpr free⟩
        have position := List.idxOf_lt_length_of_mem inUsed
        rw [groupIndex_below below]
        simp only [shiftAbove, Nat.not_lt_zero, if_false]
        rw [backMiddle _ (by omega) (by omega)]
        simp only [Nat.add_sub_cancel, List.getElem_idxOf]
      · rw [groupIndex_above (by omega)]
        simp only [shiftAbove, Nat.not_lt_zero, if_false]
        rw [backHigh _ (by omega)]
        omega
    · refine List.map_congr_left fun component _ => ?_
      simp only [Function.comp_apply, liftBVars_eq_rename, rename_comp]
      congr 1
      funext index
      simp only [Function.comp, shiftAbove]
      by_cases low : index < b
      · rw [if_pos low, if_pos low, backLow _ low]
      · rw [if_neg low, if_neg low, backHigh _ (by omega)]
        omega
  rw [prunedIs]
  calc normal block ((Prenex.mk used.length (firstComponents.map (rename (Prenex.groupIndex a used)))).par
          ⟨b, secondComponents⟩)
      = normal block ⟨a + b, ((Prenex.mk used.length (firstComponents.map (rename (Prenex.groupIndex a used)))).par
          ⟨b, secondComponents⟩).components.map (rename back)⟩ := renamed.symm
    _ = normal block ⟨a + b, ((Prenex.mk a firstComponents).par ⟨b, secondComponents⟩).components⟩ := by
        rw [componentsSame]
    _ = normal block ((Prenex.mk a firstComponents).par ⟨b, secondComponents⟩) := rfl

/-- **A block's components read again under an order of its restrictions, one of each replicated one, keep the
canonical form beside another block.** -/
theorem normal_par_reading {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock) :
    normal block ((Prenex.mk first.count (least (readingsR block first))).par second) =
      normal block (first.par second) := by
  obtain ⟨a, firstComponents⟩ := first
  obtain ⟨b, secondComponents⟩ := second
  obtain ⟨order, inOrders, leastIs⟩ := least_reading_mem (block := block) (Prenex.mk a firstComponents)
  have isOrder : IsOrder a order := readingOrders_isOrder inOrders
  show normal block ((Prenex.mk a (least (readingsR block ⟨a, firstComponents⟩))).par ⟨b, secondComponents⟩) =
    normal block ((Prenex.mk a firstComponents).par ⟨b, secondComponents⟩)
  rw [leastIs]
  set read := fun component => recanon block (rename (Prenex.permute a order) component) with readIs
  set others := secondComponents.map (liftBVars b a) with othersIs
  -- the first block's restrictions reordered beside the second's
  set order' := List.range b ++ order.map (· + b) with orderIs'
  have orderLength : order.length = a := isOrder.length
  have isOrder' : IsOrder (a + b) order' := by
    rw [orderIs']
    unfold IsOrder
    rw [Nat.add_comm a b, List.range_add]
    refine List.Perm.append_left _ ?_
    have shifted : (List.range a).map (b + ·) = (List.range a).map (· + b) :=
      List.map_congr_left fun _ _ => Nat.add_comm _ _
    rw [shifted]
    exact isOrder.map _
  have permuteFirst : Prenex.permute (a + b) order' ∘ shiftAbove 0 b = shiftAbove 0 b ∘ Prenex.permute a order := by
    funext index
    simp only [Function.comp, shiftAbove, Nat.not_lt_zero, if_false, Prenex.permute]
    by_cases below : index < a
    · rw [if_pos (by omega), if_pos below, List.getD_eq_getElem _ _ (by simp [orderIs', orderLength]; omega),
        List.getD_eq_getElem _ _ (by omega)]
      simp only [orderIs', List.getElem_append_right (by simp : (List.range b).length ≤ index + b), List.length_range,
        Nat.add_sub_cancel, List.getElem_map]
    · rw [if_neg (by omega), if_neg below]
  have permuteSecond : Prenex.permute (a + b) order' ∘ shiftAbove b a = shiftAbove b a := by
    funext index
    simp only [Function.comp]
    by_cases low : index < b
    · have shifted : shiftAbove b a index = index := by simp only [shiftAbove, if_pos low]
      rw [shifted, Prenex.permute, if_pos (by omega), List.getD_eq_getElem _ _ (by simp [orderIs', orderLength]; omega)]
      simp only [orderIs', List.getElem_append_left (by simp; omega : index < (List.range b).length),
        List.getElem_range]
    · have shifted : shiftAbove b a index = index + a := by simp only [shiftAbove, if_neg low]
      rw [shifted, Prenex.permute, if_neg (by omega)]
  have readAtomic : ∀ component ∈ firstComponents, decompose block.toBlock (read component) = Prenex.atom (read component) := by
    intro component member
    have bundle := bundle_all fresh restrictFresh (size component + 1)
    exact recanon_atomic bundle.atomic bundle.nonEmpty (by rw [size_rename]; omega)
      (atomic_rename (firstAtomic component member) _)
  set middle := (firstComponents.map read).map (liftBVars 0 b) ++ others with middleIs
  have middleAtomic : (Prenex.mk (a + b) middle).Atomic block.toBlock := by
    intro component member
    rcases List.mem_append.mp member with inFirst | inOthers
    · obtain ⟨readComponent, inRead, rfl⟩ := List.mem_map.mp inFirst
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inRead
      rw [liftBVars_eq_rename]
      exact atomic_rename (readAtomic original inOriginal) _
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inOthers
      rw [liftBVars_eq_rename]
      exact atomic_rename (secondAtomic original inOriginal) _
  have similar : SimilarR block ((Prenex.mk a firstComponents).par ⟨b, secondComponents⟩) ⟨a + b, middle⟩ := by
    refine ⟨rfl, order', middle, isOrder', ?_, List.Perm.refl _⟩
    show List.Forall₂ (AlikeR block) ((firstComponents.map (liftBVars 0 b) ++ secondComponents.map (liftBVars b a)).map
      (rename (Prenex.permute (a + b) order'))) middle
    rw [List.map_append, middleIs, othersIs]
    refine List.rel_append ?_ ?_
    · rw [List.map_map, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.forall₂_same.mpr fun component _ => ?_
      simp only [Function.comp_apply, liftBVars_eq_rename, rename_comp, permuteFirst]
      rw [← rename_comp]
      exact (alike_recanon_all fresh restrictFresh _).rename (fun first second same => by
        simp only [shiftAbove, Nat.not_lt_zero, if_false] at same
        omega)
    · rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.forall₂_same.mpr fun component _ => ?_
      simp only [Function.comp_apply, liftBVars_eq_rename, rename_comp, permuteSecond]
      exact AlikeR.refl _
  have parAtomic := par_atomic (block := block) (first := ⟨a, firstComponents⟩) firstAtomic secondAtomic
  rw [normal_similar_all fresh restrictFresh similar parAtomic middleAtomic]
  -- sorted, then one of each replicated component
  have sortPerm : (sortComponents (firstComponents.map read)).Perm (firstComponents.map read) :=
    List.perm_insertionSort _ _
  have liftInjective : Function.Injective (liftBVars 0 b) := by
    intro first second same
    rw [liftBVars_eq_rename, liftBVars_eq_rename] at same
    exact rename_injective (fun x y equal => by
      simp only [shiftAbove, Nat.not_lt_zero, if_false] at equal
      omega) same
  have liftReplicated : ∀ component, isReplicated block (liftBVars 0 b component) = isReplicated block component :=
    fun component => by rw [liftBVars_eq_rename, isReplicated_rename]
  show normal block ⟨a + b, (dedupReplicated block (sortComponents (firstComponents.map read))).map (liftBVars 0 b) ++
      secondComponents.map (liftBVars b a)⟩ = normal block ⟨a + b, middle⟩
  rw [← dedupReplicated_map liftInjective liftReplicated, ← othersIs]
  have sortedAtomic : (Prenex.mk (a + b) (others ++ (sortComponents (firstComponents.map read)).map (liftBVars 0 b))).Atomic
      block.toBlock := fun component member => middleAtomic component (by
        rw [middleIs]
        rcases List.mem_append.mp member with inOthers | inSorted
        · exact List.mem_append_right _ inOthers
        · exact List.mem_append_left _ ((sortPerm.map _).subset inSorted))
  have deduped := normal_dedupReplicated fresh restrictFresh (count := a + b)
    ((sortComponents (firstComponents.map read)).map (liftBVars 0 b)) others sortedAtomic
  rw [normal_perm fresh restrictFresh List.perm_append_comm (fun component member => sortedAtomic component (by
      rcases List.mem_append.mp member with inDeduped | inOthers
      · exact List.mem_append_right _ (dedupReplicated_subset _ inDeduped)
      · exact List.mem_append_left _ inOthers)),
    deduped, normal_perm fresh restrictFresh List.perm_append_comm sortedAtomic, middleIs]
  exact normal_perm fresh restrictFresh ((sortPerm.map _).append_right _) (fun component member => middleAtomic component (by
    rw [middleIs]
    rcases List.mem_append.mp member with inSorted | inOthers
    · exact List.mem_append_left _ ((sortPerm.map _).subset inSorted)
    · exact List.mem_append_right _ inOthers))

/-- **Blocks side by side read the first only through its canonical form.** -/
theorem normal_par_normal_left {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock) :
    normal block ((normal block first).par second) = normal block (first.par second) := by
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh firstAtomic
  obtain ⟨final, nodup, absorbs, absorbed⟩ := absorb_places blind
  have finalInside : ∀ place ∈ final, place < first.components.length := fun place member => by
    have := absorbs_subset absorbs (List.mem_toFinset.mpr member)
    simpa [places] using this
  have keptAtomic : (Prenex.mk first.count (final.map (placeValue block first.components))).Atomic block.toBlock := by
    intro component member
    obtain ⟨place, inFinal, rfl⟩ := List.mem_map.mp member
    exact firstAtomic _ (placeValue_mem (finalInside place inFinal))
  rw [normal_eq_reading first, absorbed,
    normal_par_reading fresh restrictFresh (prune_atomic keptAtomic) secondAtomic,
    normal_par_prune fresh restrictFresh keptAtomic secondAtomic,
    ← normal_par_absorbed fresh restrictFresh firstAtomic secondAtomic nodup absorbs]

/-- **Blocks side by side read the second only through its canonical form.** -/
theorem normal_par_normal_right {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock) :
    normal block (first.par (normal block second)) = normal block (first.par second) := by
  rw [normal_par_comm fresh restrictFresh firstAtomic (normal_atomic fresh restrictFresh secondAtomic),
    normal_par_normal_left fresh restrictFresh secondAtomic firstAtomic,
    normal_par_comm fresh restrictFresh secondAtomic firstAtomic]

end Par

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
