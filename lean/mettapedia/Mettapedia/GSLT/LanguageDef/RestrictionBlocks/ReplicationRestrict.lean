import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationNormal

/-!
# A block's components at some of its places

Reading a block's components at some of its places, in some order (`restrictTo`), gives a block whose absorption
system is that of the original on those places (`restrictTo_iso`), given a copy test blind to orders. So, under the
original's laws, normalizing it keeps the places outside every copy group among them (`normal_restrict`), and the
canonical form depends only on that set of places (`normal_eq_of_final`): permuting the components keeps it
(`normal_perm`), and so does removing a copy group (`normal_step`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {block : ReplicationBlock}

/-- **A block's components at some places**, in that order. -/
def restrictTo (block : ReplicationBlock) (form : Prenex) (kept : List Nat) : Prenex :=
  ⟨form.count, kept.map (placeValue block form.components)⟩

theorem placeValue_restrictTo {form : Prenex} {kept : List Nat} {position : Nat} (inside : position < kept.length) :
    placeValue block (restrictTo block form kept).components position =
      placeValue block form.components kept[position] := by
  simp only [placeValue, restrictTo]
  rw [List.getD_eq_getElem _ _ (by simpa using inside), List.getElem_map]
  rfl

theorem placeValue_idxOf {form : Prenex} {kept : List Nat} {place : Nat} (member : place ∈ kept) :
    placeValue block (restrictTo block form kept).components (kept.idxOf place) =
      placeValue block form.components place := by
  rw [placeValue_restrictTo (List.idxOf_lt_length_of_mem member), List.getElem_idxOf]

/-- The places of a group of the restricted block, as places of the original. -/
theorem sorted_image_perm {kept : List Nat} {group : Finset Nat} (inside : group ⊆ kept.toFinset) :
    (((group.image kept.idxOf).sort (· ≤ ·)).map fun position => kept.getD position 0).Perm (group.sort (· ≤ ·)) := by
  refine (List.perm_ext_iff_of_nodup ?_ (Finset.sort_nodup _ _)).mpr ?_
  · refine List.Nodup.map_on ?_ (Finset.sort_nodup _ _)
    intro first inFirst second inSecond same
    simp only [Finset.mem_sort, Finset.mem_image] at inFirst inSecond
    obtain ⟨place, placeIn, rfl⟩ := inFirst
    obtain ⟨place', placeIn', rfl⟩ := inSecond
    have member := List.mem_toFinset.mp (inside placeIn)
    have member' := List.mem_toFinset.mp (inside placeIn')
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem member), List.getElem_idxOf,
      List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem member'), List.getElem_idxOf] at same
    rw [same]
  · intro place
    simp only [List.mem_map, Finset.mem_sort, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨original, originalIn, rfl⟩, rfl⟩
      have member := List.mem_toFinset.mp (inside originalIn)
      rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem member), List.getElem_idxOf]
      exact originalIn
    · intro placeIn
      have member := List.mem_toFinset.mp (inside placeIn)
      exact ⟨kept.idxOf place, ⟨place, placeIn, rfl⟩, by
        rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem member), List.getElem_idxOf]⟩

/-- Reading a group's places through a map of places that keeps the components. -/
theorem asGroup_map {allowed : List Nat} {count : Nat} {first second : Nat → Pattern} {move : Nat → Nat}
    {group : List Nat} (same : ∀ place ∈ group, first place = second (move place)) :
    asGroup allowed count first group = asGroup allowed count second (group.map move) := by
  unfold asGroup restrictionsOf
  simp only [Group.mk.injEq, List.map_map]
  constructor
  · apply List.filter_congr
    intro index _
    rw [List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Function.comp_apply]
    exact exists_congr fun place => and_congr_right fun member => by
      unfold throughKeys
      rw [same place member]
  · exact List.map_congr_left fun place member => by simp only [Function.comp_apply, same place member]

/-- A blind copy test passes for a list of places that holds a group's places. -/
theorem copyTest_perm {form : Prenex} (blind : BlindOn block (canonicalOf block) form.count form.components)
    {place : Nat} (placeRange : place < form.components.length)
    (replicated : isReplicated block (placeValue block form.components place) = true)
    {first : List Nat} {group : Finset Nat} (notIn : place ∉ group) (permutation : first.Perm (group.sort (· ≤ ·)))
    (inRange : ∀ member ∈ group, member < form.components.length) :
    CopyTest block (canonicalOf block) form.count (placeValue block form.components place)
        (asGroup (allowedFor form.count (placeValue block form.components place)) form.count
          (placeValue block form.components) first) ↔
      CopyTest block (canonicalOf block) form.count (placeValue block form.components place)
        (asGroup (allowedFor form.count (placeValue block form.components place)) form.count
          (placeValue block form.components) (group.sort (· ≤ ·))) := by
  have nodup : first.Nodup := permutation.nodup_iff.mpr (Finset.sort_nodup _ _)
  have setIs : first.toFinset = group := by
    ext member
    simp [permutation.mem_iff]
  rw [← blind place first placeRange replicated (fun inFirst => notIn (by simpa using permutation.subset inFirst)) nodup
    fun member inFirst => inRange member (by simpa using permutation.subset inFirst), setIs]

/-- **The restricted block's system is the original's on the kept places.** -/
theorem restrictTo_iso {form : Prenex} (blind : BlindOn block (canonicalOf block) form.count form.components)
    {kept : List Nat} (inside : ∀ place ∈ kept, place < form.components.length) :
    (blockSystem block form).Iso (blockSystem block (restrictTo block form kept)) kept.toFinset kept.idxOf id where
  injective := fun first inFirst second inSecond same =>
    (List.idxOf_inj (List.mem_toFinset.mp inFirst)).mp same
  relabelInjective := Function.injective_id
  mentions := fun place member => by
    simp only [blockSystem, absorptionSystem, Finset.image_id]
    rw [show (restrictTo block form kept).count = form.count from rfl,
      placeValue_idxOf (List.mem_toFinset.mp member)]
  replicated := fun place member => by
    simp only [blockSystem, absorptionSystem]
    rw [placeValue_idxOf (List.mem_toFinset.mp member)]
  copy := fun group groupInside p pIn pReplicated pNot => by
    simp only [blockSystem, absorptionSystem]
    rw [show (restrictTo block form kept).count = form.count from rfl,
      placeValue_idxOf (List.mem_toFinset.mp pIn)]
    have groupRange : ∀ member ∈ group, member < form.components.length := fun member inGroup =>
      inside member (List.mem_toFinset.mp (groupInside inGroup))
    rw [asGroup_map (second := placeValue block form.components) (move := fun position => kept.getD position 0)
      (fun position inSorted => by
        simp only [Finset.mem_sort, Finset.mem_image] at inSorted
        obtain ⟨original, originalIn, rfl⟩ := inSorted
        have member := List.mem_toFinset.mp (groupInside originalIn)
        rw [placeValue_restrictTo (List.idxOf_lt_length_of_mem member), List.getD_eq_getElem _ _
          (List.idxOf_lt_length_of_mem member)])]
    exact copyTest_perm blind (inside p (List.mem_toFinset.mp pIn)) pReplicated pNot (sorted_image_perm groupInside)
      groupRange
  height := fun place member _ => by
    simp only [blockSystem, absorptionSystem]
    rw [placeValue_idxOf (List.mem_toFinset.mp member)]

/-- Pruning forgets the order of the components. -/
theorem prune_perm {count : Nat} {first second : List Pattern} (permutation : first.Perm second) :
    (Prenex.mk count first).prune.count = (Prenex.mk count second).prune.count ∧
      (Prenex.mk count first).prune.components.Perm (Prenex.mk count second).prune.components := by
  have usedSame : ((List.range count).filter fun index => first.any (mentions index)) =
      (List.range count).filter fun index => second.any (mentions index) :=
    List.filter_congr fun index _ => permutation.any_eq
  simp only [Prenex.prune]
  rw [usedSame]
  exact ⟨rfl, permutation.map _⟩

/-- **Blocks with the same restrictions over permuted components have one least reading.** -/
theorem least_reading_perm {count : Nat} {first second : List Pattern} (permutation : first.Perm second) :
    (⟨(Prenex.mk count first).prune.count, least (readingsR block (Prenex.mk count first).prune)⟩ : Prenex) =
      ⟨(Prenex.mk count second).prune.count, least (readingsR block (Prenex.mk count second).prune)⟩ := by
  obtain ⟨countSame, componentsPerm⟩ := prune_perm (count := count) permutation
  apply least_reading_eq
  refine ⟨countSame, List.range (Prenex.mk count first).prune.count, (Prenex.mk count first).prune.components,
    List.Perm.refl _, ?_, componentsPerm⟩
  have renameId : rename id = (id : Pattern → Pattern) := funext rename_id
  rw [permute_range, renameId, List.map_id]
  exact List.forall₂_same.mpr fun component _ => AlikeR.refl component

/-- **Normalizing a block at the places left by removing some copy groups** gives the block's canonical form,
under the laws of its system and a copy test blind to orders. -/
theorem normal_restrict {form : Prenex} (laws : (blockSystem block form).Laws (places form).toFinset)
    (blind : BlindOn block (canonicalOf block) form.count form.components) {kept : List Nat} (nodup : kept.Nodup)
    (inside : ∀ place ∈ kept, place < form.components.length)
    (removes : (blockSystem block form).Removes (places form).toFinset kept.toFinset) :
    normal block (restrictTo block form kept) = normal block form := by
  obtain ⟨final, finalNodup, absorbs, reached⟩ := absorbRounds_absorbs (height := fun place => size (canonicalOf block
    (argumentOf? (placeValue block form.components place)))) blind kept.length nodup inside (le_refl _)
  have finalIs := (removes.absorbs absorbs).eq laws (Finset.Subset.refl _)
  obtain ⟨final', nodup', finalIs', normalIs⟩ := normal_copies laws blind
  rw [normalIs, normal_eq_reading]
  have absorbed : absorb block (canonicalOf block) (restrictTo block form kept) =
      (Prenex.mk form.count (final.map (placeValue block form.components))).prune := by
    unfold absorb restrictTo
    simp only [List.length_map]
    rw [reached]
  rw [absorbed]
  apply least_reading_perm
  apply List.Perm.map
  rw [List.perm_ext_iff_of_nodup finalNodup nodup']
  intro place
  rw [← List.mem_toFinset, ← List.mem_toFinset (l := final'), finalIs', ← finalIs]

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
