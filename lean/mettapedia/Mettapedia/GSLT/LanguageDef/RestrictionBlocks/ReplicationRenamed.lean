import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRename

/-!
# The canonical form of a renamed block

Pruning a block read through a renaming keeping its restrictions gives the pruned original with its names outside
renamed (`pruneRelabel`) and its restrictions reordered (`prune_rename`), so the least readings agree
(`least_reading_prune_rename`). Under the original's laws and order-blind copy test, the renamed block absorbs the
same places, so its canonical form is the least reading of the absorbed original renamed outside (`normal_rename`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex)

variable {block : ReplicationBlock} {count count' : Nat} {relabel : Nat → Nat}

/-- The restrictions a block's components use, in increasing order. -/
def usedOf (form : Prenex) : List Nat :=
  (List.range form.count).filter fun index => form.components.any (mentions index)

theorem prune_eq (form : Prenex) :
    form.prune = ⟨(usedOf form).length, form.components.map (rename (Prenex.groupIndex form.count (usedOf form)))⟩ :=
  rfl

/-- **The names outside a pruned block, read through a renaming of the block.** -/
def pruneRelabel (count count' : Nat) (relabel : Nat → Nat) (index : Nat) : Nat := relabel (index + count) - count'

theorem imageOf_used (preserving : Preserving count count' relabel) (components : List Pattern) :
    ImageOf count count' relabel (usedOf ⟨count, components⟩) (usedOf ⟨count', components.map (rename relabel)⟩) where
  nodup := List.nodup_range.filter _
  nodup' := List.nodup_range.filter _
  inside := fun _ member => List.mem_range.mp (List.mem_filter.mp member).1
  inside' := fun _ member => List.mem_range.mp (List.mem_filter.mp member).1
  mem_iff := fun index' => by
    simp only [usedOf, List.mem_filter, List.mem_range, List.any_map, List.any_eq_true, Function.comp_apply]
    constructor
    · rintro ⟨below', component, member, mentioned'⟩
      obtain ⟨index, rfl, mentioned⟩ := mentions_rename_image component mentioned'
      exact ⟨index, ⟨preserving.lt_iff.mp below', component, member, mentioned⟩, rfl⟩
    · rintro ⟨index, ⟨below, component, member, mentioned⟩, rfl⟩
      exact ⟨preserving.below index below, component, member, by
        rw [mentions_rename_injective preserving.injective]; exact mentioned⟩

/-- **Pruning a renamed block** gives the pruned original, renamed outside and its restrictions reordered. -/
theorem prune_rename (preserving : Preserving count count' relabel) (components : List Pattern) :
    (Prenex.mk count' (components.map (rename relabel))).prune =
      ⟨(Prenex.mk count components).prune.count,
        ((Prenex.mk count components).prune.renameOuter (pruneRelabel count count' relabel)).components.map
          (rename (Prenex.permute (Prenex.mk count components).prune.count
            (copyOrder relabel (usedOf ⟨count, components⟩) (usedOf ⟨count', components.map (rename relabel)⟩))))⟩ := by
  have image := imageOf_used preserving components
  have lengthEq := image.length_eq preserving
  rw [prune_eq, prune_eq]
  simp only [Prenex.renameOuter, List.map_map, Prenex.mk.injEq]
  refine ⟨lengthEq, List.map_congr_left fun component member => ?_⟩
  simp only [Function.comp_apply, rename_comp]
  apply rename_congr
  intro index free
  simp only [Function.comp_apply]
  by_cases inside : index < count
  · have used : index ∈ usedOf ⟨count, components⟩ := List.mem_filter.mpr ⟨List.mem_range.mpr inside,
      List.any_eq_true.mpr ⟨component, member, (mentions_iff _ _).mpr free⟩⟩
    have placed := List.idxOf_lt_length_of_mem used
    rw [groupIndex_below (preserving.below index inside), groupIndex_below inside, liftIndex, if_pos placed,
      Prenex.permute, if_pos placed, copyOrder, List.getD_eq_getElem _ _ (by simpa using placed), List.getElem_map,
      List.getElem_idxOf]
  · have above : count ≤ index := Nat.le_of_not_lt inside
    have imageAbove := preserving.above index above
    rw [groupIndex_above imageAbove, groupIndex_above above, liftIndex, if_neg (by omega), pruneRelabel,
      Prenex.permute, if_neg (by omega), lengthEq, show index - count + (usedOf ⟨count, components⟩).length -
        (usedOf ⟨count, components⟩).length + count = index by omega]

/-- **A pruned renamed block reads as the pruned original renamed outside.** -/
theorem least_reading_prune_rename (preserving : Preserving count count' relabel) (components : List Pattern) :
    (⟨(Prenex.mk count' (components.map (rename relabel))).prune.count,
        least (readingsR block (Prenex.mk count' (components.map (rename relabel))).prune)⟩ : Prenex) =
      ⟨(Prenex.mk count components).prune.count,
        least (readingsR block ((Prenex.mk count components).prune.renameOuter (pruneRelabel count count' relabel)))⟩ := by
  have image := imageOf_used preserving components
  have isOrder := image.copyOrder_isOrder preserving
  rw [prune_rename preserving components]
  symm
  refine least_reading_eq (first := (Prenex.mk count components).prune.renameOuter (pruneRelabel count count' relabel))
    ⟨rfl, copyOrder relabel _ _, _, ?_, List.forall₂_same.mpr fun component _ => AlikeR.refl component,
      List.Perm.refl _⟩
  simpa [Prenex.renameOuter, prune_eq] using isOrder

/-- **The canonical form of a renamed block**: under the original's laws and order-blind copy test, the renamed
block absorbs the same places, and reads the absorbed original renamed outside. -/
theorem normal_rename (preserving : Preserving count count' relabel) {components : List Pattern}
    (below : Below block (Prenex.mass ⟨count, components⟩))
    (atomic : ∀ component ∈ components, decompose block.toBlock component = Prenex.atom component)
    (laws : (blockSystem block ⟨count, components⟩).Laws (places ⟨count, components⟩).toFinset)
    (blind : BlindOn block (canonicalOf block) count components) :
    ∃ final : List Nat, final.Nodup ∧
      final.toFinset = (places ⟨count, components⟩).toFinset \
        (blockSystem block ⟨count, components⟩).copies (places ⟨count, components⟩).toFinset ∧
      normal block ⟨count, components⟩ = ⟨(Prenex.mk count (final.map (placeValue block components))).prune.count,
        least (readingsR block (Prenex.mk count (final.map (placeValue block components))).prune)⟩ ∧
      normal block ⟨count', components.map (rename relabel)⟩ =
        ⟨(Prenex.mk count (final.map (placeValue block components))).prune.count,
          least (readingsR block ((Prenex.mk count (final.map (placeValue block components))).prune.renameOuter
            (pruneRelabel count count' relabel)))⟩ := by
  obtain ⟨final, nodup, finalIs, normalIs⟩ := normal_copies laws blind
  refine ⟨final, nodup, finalIs, normalIs, ?_⟩
  have iso := rename_iso preserving below atomic
  have placesSame : places (⟨count', components.map (rename relabel)⟩ : Prenex) = places ⟨count, components⟩ := by
    simp [places]
  have laws' : (blockSystem block ⟨count', components.map (rename relabel)⟩).Laws
      (places ⟨count', components.map (rename relabel)⟩).toFinset := by
    have := iso.laws laws
    rwa [Finset.image_id, ← placesSame] at this
  have blind' : BlindOn block (canonicalOf block) count' (components.map (rename relabel)) := by
    intro place group placeRange replicated' notIn groupNodup inRange
    rw [List.length_map] at placeRange
    have replicated : isReplicated block (placeValue block components place) = true := by
      rw [placeValue_map_rename, isReplicated_rename] at replicated'
      exact replicated'
    have inRange' : ∀ member ∈ group, member < components.length := fun member inGroup => by
      simpa using inRange member inGroup
    have sortedNodup : (place :: group.toFinset.sort (· ≤ ·)).Nodup :=
      List.nodup_cons.mpr ⟨fun inSorted => notIn (by simpa using inSorted), Finset.sort_nodup _ _⟩
    have sortedRange : ∀ member ∈ place :: group.toFinset.sort (· ≤ ·), member < components.length := by
      intro member inList
      rcases List.mem_cons.mp inList with rfl | inSorted
      · exact placeRange
      · exact inRange' member (by simpa using inSorted)
    have listRange : ∀ member ∈ place :: group, member < components.length := by
      intro member inList
      rcases List.mem_cons.mp inList with rfl | inGroup
      · exact placeRange
      · exact inRange' member inGroup
    rw [copyTest_rename preserving below atomic sortedNodup sortedRange replicated,
      copyTest_rename preserving below atomic (List.nodup_cons.mpr ⟨notIn, groupNodup⟩) listRange replicated]
    exact blind place group placeRange replicated notIn groupNodup inRange'
  obtain ⟨final', nodup', finalIs', normalIs'⟩ := normal_copies laws' blind'
  have copiesSame := iso.copies
  rw [Finset.image_id, Finset.image_id, ← placesSame] at copiesSame
  rw [normalIs']
  have permutation : final'.Perm final := by
    rw [List.perm_ext_iff_of_nodup nodup' nodup]
    intro place
    rw [← List.mem_toFinset, ← List.mem_toFinset (l := final), finalIs', finalIs, copiesSame, placesSame]
  rw [least_reading_perm (permutation.map _)]
  have valueRenamed : final.map (placeValue block (components.map (rename relabel))) =
      (final.map (placeValue block components)).map (rename relabel) := by
    rw [List.map_map]
    exact List.map_congr_left fun place _ => placeValue_map_rename relabel components place
  rw [valueRenamed]
  exact least_reading_prune_rename preserving _

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
