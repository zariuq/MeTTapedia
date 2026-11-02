import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationUnfolding
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ProtectedRemoval

/-!
# Copy groups removed around protected components, on blocks

Removing copy groups from some of a block's components keeps the canonical form of the block those components make
(`normal_restrict_from`). So a removal that avoids the components a redex takes keeps the canonical form both of the
block with the redex and of the block with what the redex leaves in its place (`normal_replace_avoiding`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {block : ReplicationBlock}

theorem restrictTo_atomic {form : Prenex} (atomic : form.Atomic block.toBlock) {kept : List Nat}
    (inside : ∀ place ∈ kept, place < form.components.length) : (restrictTo block form kept).Atomic block.toBlock := by
  intro component member
  simp only [restrictTo, List.mem_map] at member
  obtain ⟨place, inKept, rfl⟩ := member
  simp only [placeValue]
  rw [List.getD_eq_getElem _ _ (inside place inKept)]
  exact atomic _ (List.getElem_mem _)

/-- **Removing copy groups from some components keeps the canonical form of the block they make.** -/
theorem normal_restrict_from (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {form : Prenex} (atomic : form.Atomic block.toBlock) {live kept : List Nat} (liveNodup : live.Nodup)
    (liveInside : ∀ place ∈ live, place < form.components.length) (keptNodup : kept.Nodup)
    (keptLive : ∀ place ∈ kept, place ∈ live)
    (removes : (blockSystem block form).Removes live.toFinset kept.toFinset) :
    normal block (restrictTo block form kept) = normal block (restrictTo block form live) := by
  set restricted := restrictTo block form live with restrictedIs
  have restrictedAtomic : restricted.Atomic block.toBlock := restrictTo_atomic atomic liveInside
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh restrictedAtomic
  obtain ⟨-, formBlind⟩ := lawful_all fresh restrictFresh atomic
  have iso := restrictTo_iso formBlind liveInside
  have transported := iso.removes removes
  have placesIs : live.toFinset.image live.idxOf = (places restricted).toFinset := by
    ext position
    simp only [Finset.mem_image, List.mem_toFinset, places, restrictedIs, restrictTo, List.length_map, List.mem_range]
    constructor
    · rintro ⟨place, member, rfl⟩
      exact List.idxOf_lt_length_of_mem member
    · intro below
      exact ⟨live[position], List.getElem_mem below, liveNodup.idxOf_getElem position below⟩
  have keptIs : kept.toFinset.image live.idxOf = (kept.map live.idxOf).toFinset := by
    ext position
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  rw [placesIs, keptIs] at transported
  have positionsNodup : (kept.map live.idxOf).Nodup :=
    keptNodup.map_on fun first inFirst second inSecond same =>
      (List.idxOf_inj (keptLive first inFirst)).mp same
  have positionsInside : ∀ position ∈ kept.map live.idxOf, position < restricted.components.length := by
    intro position member
    obtain ⟨place, inKept, rfl⟩ := List.mem_map.mp member
    simp only [restrictedIs, restrictTo, List.length_map]
    exact List.idxOf_lt_length_of_mem (keptLive place inKept)
  have restricted' := normal_restrict laws blind positionsNodup positionsInside transported
  have sameBlock : restrictTo block restricted (kept.map live.idxOf) = restrictTo block form kept := by
    simp only [restrictTo, restrictedIs, List.map_map, Prenex.mk.injEq, true_and]
    refine List.map_congr_left fun place inKept => ?_
    simp only [Function.comp_apply]
    exact placeValue_idxOf (keptLive place inKept)
  rw [← sameBlock, restricted']

/-- The places among some list that a finite set holds, in the list's order. -/
theorem filter_toFinset {places : List Nat} {set : Finset Nat} (inside : set ⊆ places.toFinset) :
    (places.filter (· ∈ set)).toFinset = set := by
  ext place
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨_, member⟩ => member, fun member => ⟨List.mem_toFinset.mp (inside member), member⟩⟩

/-- **Protecting a redex's components and some kept components**: copy groups avoiding both are removed until every
copy group left meets them. The canonical forms of the block with the redex and of the block with what it leaves
in its place stay, when what it leaves mentions only restrictions the redex's or the kept components mention. -/
theorem protect (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {form : Prenex} (atomic : form.Atomic block.toBlock) {common parts results keep : List Nat}
    (nodup : (common ++ parts ++ results).Nodup)
    (inside : ∀ place ∈ common ++ parts ++ results, place < form.components.length)
    (keepCommon : ∀ place ∈ keep, place ∈ common)
    (plain : ∀ place ∈ parts, isReplicated block (placeValue block form.components place) = false)
    (leaves : ∀ place ∈ results, ∀ restriction ∈ (blockSystem block form).mentions place,
      ∃ held ∈ parts ++ keep, restriction ∈ (blockSystem block form).mentions held) :
    ∃ kept : List Nat, kept.Sublist common ∧ (∀ place ∈ keep, place ∈ kept) ∧
      normal block (restrictTo block form (kept ++ parts)) = normal block (restrictTo block form (common ++ parts)) ∧
      normal block (restrictTo block form (kept ++ results)) =
        normal block (restrictTo block form (common ++ results)) ∧
      ∀ p group, (blockSystem block form).IsCopy (kept ++ parts).toFinset p group →
        ¬ Disjoint group (parts ++ keep).toFinset := by
  classical
  have commonNodup : common.Nodup := (List.nodup_append.mp (List.nodup_append.mp nodup).1).1
  have partsNodup : parts.Nodup := (List.nodup_append.mp (List.nodup_append.mp nodup).1).2.1
  have resultsNodup : results.Nodup := (List.nodup_append.mp nodup).2.1
  have commonParts : ∀ a ∈ common, ∀ b ∈ parts, a ≠ b := (List.nodup_append.mp (List.nodup_append.mp nodup).1).2.2
  have outerResults : ∀ a ∈ common ++ parts, ∀ b ∈ results, a ≠ b := (List.nodup_append.mp nodup).2.2
  obtain ⟨rest, removes, maximal⟩ := (blockSystem block form).exists_removesAvoiding
    (parts.toFinset ∪ keep.toFinset ∪ results.toFinset) (common ++ parts).toFinset
  have liveIs : (common ++ parts).toFinset = common.toFinset ∪ parts.toFinset := by
    ext place
    simp
  rw [liveIs] at removes
  have keepCommon' : keep.toFinset ⊆ common.toFinset := fun place member =>
    List.mem_toFinset.mpr (keepCommon place (List.mem_toFinset.mp member))
  obtain ⟨common', inside', restIs, removesNew⟩ := removes.replace (common := common.toFinset)
    (old := parts.toFinset) (new := results.toFinset) (keep := keep.toFinset) rfl
    (Finset.disjoint_left.mpr fun _ inCommon inParts =>
      commonParts _ (List.mem_toFinset.mp inCommon) _ (List.mem_toFinset.mp inParts) rfl)
    (Finset.disjoint_left.mpr fun _ inCommon inResults =>
      outerResults _ (List.mem_append_left _ (List.mem_toFinset.mp inCommon)) _ (List.mem_toFinset.mp inResults) rfl)
    (fun place member => Finset.mem_union_left _ (Finset.mem_union_left _ member))
    (fun place member => Finset.mem_union_left _ (Finset.mem_union_right _ member)) keepCommon'
    (fun place inParts replicated => by
      have flat := plain place (List.mem_toFinset.mp inParts)
      simp only [blockSystem, absorptionSystem] at replicated
      rw [flat] at replicated
      exact Bool.false_ne_true replicated)
    (fun place inResults restriction mentioned => by
      obtain ⟨held, inHeld, mentioned'⟩ := leaves place (List.mem_toFinset.mp inResults) restriction mentioned
      refine ⟨held, ?_, mentioned'⟩
      rcases List.mem_append.mp inHeld with inParts | inKeep
      · exact Finset.mem_union_left _ (List.mem_toFinset.mpr inParts)
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr inKeep))
  set kept := common.filter (· ∈ common') with keptIs
  have keptToFinset : kept.toFinset = common' := filter_toFinset inside'
  have keptSublist : kept.Sublist common := List.filter_sublist
  have keptParts : (kept ++ parts).toFinset = rest := by
    rw [restIs, ← keptToFinset]
    ext place
    simp
  have keptResults : (kept ++ results).toFinset = common' ∪ results.toFinset := by
    rw [← keptToFinset]
    ext place
    simp
  have commonResults : (common ++ results).toFinset = common.toFinset ∪ results.toFinset := by
    ext place
    simp
  have insideAll : ∀ place ∈ common ++ parts, place < form.components.length := fun place member =>
    inside place (List.mem_append_left _ member)
  have insideResults : ∀ place ∈ common ++ results, place < form.components.length := fun place member => by
    rcases List.mem_append.mp member with inCommon | inResults
    · exact inside place (List.mem_append_left _ (List.mem_append_left _ inCommon))
    · exact inside place (List.mem_append_right _ inResults)
  refine ⟨kept, keptSublist, ?_, ?_, ?_, ?_⟩
  · intro place inKeep
    have inLive : place ∈ (common.toFinset ∪ parts.toFinset) ∩ (parts.toFinset ∪ keep.toFinset ∪ results.toFinset) :=
      Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (List.mem_toFinset.mpr (keepCommon place inKeep)),
        Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr inKeep))⟩
    have inRest := removes.keeps inLive
    rw [← keptParts] at inRest
    rcases List.mem_append.mp (List.mem_toFinset.mp inRest) with inKept | inParts
    · exact inKept
    · exact absurd rfl (commonParts place (keepCommon place inKeep) place inParts)
  · refine normal_restrict_from fresh restrictFresh atomic (List.nodup_append.mp nodup).1 insideAll ?_ ?_ ?_
    · exact (List.nodup_append.mpr ⟨keptSublist.nodup commonNodup, partsNodup, fun a inKept b inParts =>
        commonParts a (keptSublist.subset inKept) b inParts⟩)
    · intro place member
      rcases List.mem_append.mp member with inKept | inParts
      · exact List.mem_append_left _ (keptSublist.subset inKept)
      · exact List.mem_append_right _ inParts
    · rw [keptParts, liveIs]
      exact removes.removes
  · refine normal_restrict_from fresh restrictFresh atomic ?_ insideResults ?_ ?_ ?_
    · exact List.nodup_append.mpr ⟨commonNodup, resultsNodup, fun a inCommon b inResults =>
        outerResults a (List.mem_append_left _ inCommon) b inResults⟩
    · exact List.nodup_append.mpr ⟨keptSublist.nodup commonNodup, resultsNodup, fun a inKept b inResults =>
        outerResults a (List.mem_append_left _ (keptSublist.subset inKept)) b inResults⟩
    · intro place member
      rcases List.mem_append.mp member with inKept | inResults
      · exact List.mem_append_left _ (keptSublist.subset inKept)
      · exact List.mem_append_right _ inResults
    · rw [keptResults, commonResults]
      exact removesNew
  · intro p group isCopy disjoint
    rw [keptParts] at isCopy
    refine maximal p group isCopy ?_
    rw [show (parts ++ keep).toFinset = parts.toFinset ∪ keep.toFinset by ext; simp] at disjoint
    refine Finset.disjoint_union_right.mpr ⟨disjoint, Finset.disjoint_left.mpr fun _ inGroup inResults => ?_⟩
    have inRest := (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup)).2
    rw [restIs] at inRest
    rcases Finset.mem_union.mp inRest with inCommon | inParts
    · exact outerResults _ (List.mem_append_left _ (List.mem_toFinset.mp (inside' inCommon))) _
        (List.mem_toFinset.mp inResults) rfl
    · exact outerResults _ (List.mem_append_right _ (List.mem_toFinset.mp inParts)) _
        (List.mem_toFinset.mp inResults) rfl

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
