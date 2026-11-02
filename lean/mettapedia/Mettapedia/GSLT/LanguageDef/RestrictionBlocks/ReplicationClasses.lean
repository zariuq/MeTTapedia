import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationClose

/-!
# Replicated molecules by classes of places

The molecules of a block are its places grouped by the restrictions their components share (`groups_eq_build`), and
a molecule is the block of its places with the unused restrictions dropped (`molecule_asGroup`). The replicated
component of a molecule is the pattern of the canonical block of its places, replicated unless it is a replication
already (`moleculeEntry_prune`), so the replicated molecules of a block are the entries of its classes of places
(`replicatedOf_eq_entries`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)

variable {block : ReplicationBlock}

/-- The restrictions the component at a place uses. -/
def keysAt (block : ReplicationBlock) (form : Prenex) (place : Nat) : List Nat :=
  usedRestrictions form.count (placeValue block form.components place)

/-- A pattern replicated, unless it is a replication. -/
def bang (block : ReplicationBlock) (pattern : Pattern) : Pattern :=
  if isReplicated block pattern = true then pattern else .apply block.replicate [pattern]

/-- **The entry of some places of a block**: the pattern of their canonical block, replicated. -/
def entryOf (block : ReplicationBlock) (form : Prenex) (places : List Nat) : Pattern :=
  bang block (Prenex.toPattern block.toBlock (normal block (restrictTo block form places)))

/-- The replicated component of a molecule. -/
def moleculeEntry (block : ReplicationBlock) (form : Prenex) : Pattern :=
  match form.count, form.components with
  | 0, [.apply label [argument]] =>
      if label = block.replicate then .apply label [canonicalOf block argument]
      else .apply block.replicate [canonicalOf block (Prenex.toPattern block.toBlock form)]
  | _, _ => .apply block.replicate [canonicalOf block (Prenex.toPattern block.toBlock form)]

theorem replicatedOf_eq (inner : Prenex) :
    replicatedOf block (canonicalOf block) inner =
      (groups inner).map fun group => moleculeEntry block (Prenex.molecule inner.count group) := rfl

/-! ## Molecules are classes of places -/

theorem components_eq_places (form : Prenex) :
    form.components = (places form).map (placeValue block form.components) :=
  (congrArg Prenex.components (places_map (block := block) form)).symm

theorem groups_eq_groupsThrough (form : Prenex) :
    groups form = groupsThrough (List.range form.count) form.count form.components := by
  unfold groups groupsThrough
  have same : (fun groups component => insertComponent form.count component groups) =
      (fun groups component => insertUsing form.count
        ((usedRestrictions form.count component).filter (List.range form.count).contains) component groups) := by
    funext groups component
    unfold insertComponent
    congr 1
    symm
    apply List.filter_eq_self.mpr
    intro index member
    simp only [usedRestrictions, List.mem_filter, List.mem_range] at member
    simp [member.1]
  rw [same]

theorem throughKeys_range (count : Nat) (value : Nat → Pattern) :
    throughKeys (List.range count) count value = fun place => usedRestrictions count (value place) := by
  funext place
  unfold throughKeys
  apply List.filter_eq_self.mpr
  intro index member
  simp only [usedRestrictions, List.mem_filter, List.mem_range] at member
  simp [member.1]

/-- **The molecules of a block are its classes of places.** -/
theorem groups_eq_build (form : Prenex) :
    groups form = (Linked.build (keysAt block form) (places form)).map
      (asGroup (List.range form.count) form.count (placeValue block form.components)) := by
  rw [groups_eq_groupsThrough]
  have componentsIs := components_eq_places (block := block) form
  calc groupsThrough (List.range form.count) form.count form.components
      = groupsThrough (List.range form.count) form.count
          ((places form).map (placeValue block form.components)) := by rw [← componentsIs]
    _ = _ := by
        rw [groupsThrough_map, throughKeys_range]
        rfl

/-- **A molecule is the block of its places without the unused restrictions.** -/
theorem molecule_asGroup (count : Nat) (value : Nat → Pattern) (items : List Nat) :
    Prenex.molecule count (asGroup (List.range count) count value items) =
      (Prenex.mk count (items.map value)).prune := by
  have usedIs : restrictionsOf (List.range count) count value items = usedOf ⟨count, items.map value⟩ := by
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
  simp only [Prenex.molecule, asGroup, prune_eq, usedIs]

/-! ## The replicated component of a molecule -/

theorem moleculeEntry_of_pos {form : Prenex} (positive : 0 < form.count) :
    moleculeEntry block form = .apply block.replicate [canonicalOf block (Prenex.toPattern block.toBlock form)] := by
  obtain ⟨count, components⟩ := form
  cases count with
  | zero => exact absurd positive (Nat.lt_irrefl 0)
  | succ count => rfl

theorem moleculeEntry_single (multisetFresh : block.replicate ∉ block.multisets)
    (restrictFresh : block.replicate ≠ block.restrict) (component : Pattern) :
    moleculeEntry block ⟨0, [component]⟩ =
      if isReplicated block component = true then recanon block component
      else .apply block.replicate [canonicalOf block component] := by
  have partIs : ∀ argument, partOf block block.replicate argument = canonicalOf block argument := by
    intro argument
    unfold partOf
    rw [if_neg restrictFresh, if_neg multisetFresh]
  match component with
  | .apply label [argument] =>
      by_cases isReplicate : label = block.replicate
      · subst isReplicate
        simp only [moleculeEntry, if_true, isReplicated, beq_self_eq_true]
        rw [recanon_apply]
        simp only [List.map_cons, List.map_nil, partIs]
      · have notReplicated : isReplicated block (.apply label [argument]) = false := by
          simp [isReplicated, isReplicate]
        simp only [moleculeEntry, if_neg isReplicate, notReplicated]
        rfl
  | .apply label [] => rfl
  | .apply label (first :: second :: rest) => rfl
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .lambda _ _ => rfl
  | .multiLambda _ _ _ => rfl
  | .subst _ _ => rfl
  | .collection _ _ _ => rfl

theorem bang_of_not_replicated {pattern : Pattern} (notReplicated : isReplicated block pattern = false) :
    bang block pattern = .apply block.replicate [pattern] := by
  simp [bang, notReplicated]

theorem bang_of_replicated {pattern : Pattern} (replicated : isReplicated block pattern = true) :
    bang block pattern = pattern := by
  simp [bang, replicated]

section Entries

variable (multisetFresh : block.replicate ∉ block.multisets) (fresh : block.replicate ∉ block.emptyUnits)
  (restrictFresh : block.replicate ≠ block.restrict)

include multisetFresh fresh restrictFresh

/-- **The replicated component of a molecule is its canonical block's pattern, replicated**, when the molecule's
places are linked. -/
theorem moleculeEntry_prune {count : Nat} {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock) (nonempty : components ≠ [])
    (linked : 2 ≤ components.length → ∀ component ∈ components, ∃ index < count, mentions index component = true) :
    moleculeEntry block (Prenex.mk count components).prune =
      bang block (Prenex.toPattern block.toBlock (normal block ⟨count, components⟩)) := by
  rw [← normal_prune fresh restrictFresh _ atomic]
  have prunedAtomic := prune_atomic atomic
  have prunedUsed := used_prune (Prenex.mk count components)
  cases usedIs : usedOf (Prenex.mk count components) with
  | nil =>
      -- no restriction is used: a single component
      have single : components.length = 1 := by
        by_contra notOne
        have two : 2 ≤ components.length := by
          have := List.length_pos_of_ne_nil nonempty
          omega
        obtain ⟨first, member⟩ := List.exists_mem_of_ne_nil _ nonempty
        obtain ⟨index, below, mentioned⟩ := linked two first member
        have inUsed : index ∈ usedOf (Prenex.mk count components) := by
          simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
          exact ⟨below, first, member, mentioned⟩
        rw [usedIs] at inUsed
        simp at inUsed
      obtain ⟨component, rfl⟩ := List.length_eq_one_iff.mp single
      have prunedIs : (Prenex.mk count [component]).prune =
          ⟨0, [rename (Prenex.groupIndex count []) component]⟩ := by
        rw [prune_eq, usedIs]
        rfl
      rw [prunedIs, moleculeEntry_single multisetFresh restrictFresh]
      set renamed := rename (Prenex.groupIndex count []) component with renamedIs
      have renamedAtomic : decompose block.toBlock renamed = Prenex.atom renamed :=
        atomic_rename (atomic component List.mem_cons_self) _
      have canonicalIs : Prenex.toPattern block.toBlock (normal block ⟨0, [renamed]⟩) = recanon block renamed := by
        have := canonicalOf_atom (block := block) renamedAtomic
        unfold canonicalOf at this
        rwa [renamedAtomic] at this
      rw [canonicalIs, ← canonicalOf_atom renamedAtomic]
      by_cases replicated : isReplicated block renamed = true
      · rw [if_pos replicated, canonicalOf_atom renamedAtomic,
          bang_of_replicated (by rw [isReplicated_recanon]; exact replicated)]
      · rw [if_neg replicated, bang_of_not_replicated (by
          rw [canonicalOf_atom renamedAtomic, isReplicated_recanon]
          exact Bool.eq_false_iff.mpr replicated)]
  | cons used rest =>
      -- some restriction is used, by every component
      have positive : 0 < (Prenex.mk count components).prune.count := by
        rw [prune_eq, usedIs]
        simp
      rw [moleculeEntry_of_pos positive, canonicalOf_toPattern prunedAtomic prunedUsed]
      refine (bang_of_not_replicated ?_).symm
      rw [isReplicated_toPattern restrictFresh]
      -- the canonical block keeps a restriction
      obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh prunedAtomic
      obtain ⟨final, finalNodup, absorbs, absorbed⟩ := absorb_places blind
      have finalIs := absorbs.eq laws (Finset.Subset.refl _)
      have prunedNonempty : (places (Prenex.mk count components).prune).toFinset.Nonempty := by
        obtain ⟨first, member⟩ := List.exists_mem_of_ne_nil _ nonempty
        refine ⟨0, ?_⟩
        rw [prune_eq]
        simp only [places, List.mem_toFinset, List.mem_range, List.length_map]
        exact List.length_pos_of_ne_nil nonempty
      obtain ⟨kept, keptLive, keptNotCopy⟩ := CopyGroups.System.exists_not_copy laws (Finset.Subset.refl _)
        prunedNonempty
      have keptFinal : kept ∈ final := by
        rw [← List.mem_toFinset, finalIs]
        exact Finset.mem_sdiff.mpr ⟨keptLive, keptNotCopy⟩
      have keptInside : kept < (Prenex.mk count components).prune.components.length := by
        simpa [places] using keptLive
      -- the kept component uses a restriction
      have keptUses : ∃ index < (Prenex.mk count components).prune.count,
          mentions index (placeValue block (Prenex.mk count components).prune.components kept) = true := by
        have keptBelow : kept < components.length := by
          rw [prune_eq] at keptInside
          simpa using keptInside
        have original : placeValue block (Prenex.mk count components).prune.components kept =
            rename (Prenex.groupIndex count (usedOf ⟨count, components⟩)) components[kept] := by
          rw [prune_eq]
          unfold placeValue
          rw [List.getD_eq_getElem _ _ (by simpa using keptBelow), List.getElem_map]
        have usesOriginal : ∃ index < count, mentions index components[kept] = true := by
          by_cases two : 2 ≤ components.length
          · exact linked two _ (List.getElem_mem keptBelow)
          · have one : components.length = 1 := by
              have := List.length_pos_of_ne_nil nonempty
              omega
            have inUsed : used ∈ usedOf (Prenex.mk count components) := by rw [usedIs]; simp
            simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true] at inUsed
            obtain ⟨below, component, member, mentioned⟩ := inUsed
            have kZero : kept = 0 := by omega
            obtain ⟨only, rfl⟩ := List.length_eq_one_iff.mp one
            simp only [List.mem_singleton] at member
            subst member
            exact ⟨used, below, by simpa [kZero] using mentioned⟩
        obtain ⟨index, below, mentioned⟩ := usesOriginal
        have inUsed : index ∈ usedOf (Prenex.mk count components) := by
          simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
          exact ⟨below, _, List.getElem_mem keptBelow, mentioned⟩
        refine ⟨(usedOf (Prenex.mk count components)).idxOf index, ?_, ?_⟩
        · rw [prune_eq]
          exact List.idxOf_lt_length_of_mem inUsed
        · rw [original, mentions_iff, freeIn_rename]
          exact ⟨index, (mentions_iff _ _).mp mentioned, by rw [groupIndex_below below]⟩
      obtain ⟨index, below, mentioned⟩ := keptUses
      have countPositive : 0 < (normal block (Prenex.mk count components).prune).count := by
        rw [normal_eq_reading, absorbed]
        simp only [prune_eq]
        apply List.length_pos_of_mem (a := index)
        simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
        exact ⟨below, _, List.mem_map_of_mem keptFinal, mentioned⟩
      have notZero : decide ((normal block (Prenex.mk count components).prune).count = 0) = false := by
        simp only [decide_eq_false_iff_not]
        omega
      rw [notZero, Bool.false_and, Bool.false_and]

/-- **The replicated molecules of a block are the entries of its classes of places.** -/
theorem replicatedOf_eq_entries {form : Prenex} (atomic : form.Atomic block.toBlock) :
    replicatedOf block (canonicalOf block) form =
      (Linked.build (keysAt block form) (places form)).map (entryOf block form) := by
  rw [replicatedOf_eq, groups_eq_build (block := block), List.map_map]
  have grouping := Linked.build_grouping (keys := keysAt block form) (places form)
  refine List.map_congr_left fun group member => ?_
  simp only [Function.comp_apply]
  rw [molecule_asGroup]
  have groupInside : ∀ place ∈ group, place < form.components.length := fun place inGroup => by
    have := grouping.mem_items member inGroup
    simpa [places] using this
  refine moleculeEntry_prune multisetFresh fresh restrictFresh ?_ ?_ ?_
  · intro component inMap
    obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp inMap
    exact atomic _ (placeValue_mem (groupInside place inGroup))
  · simpa using grouping.nonempty group member
  · intro two component inMap
    obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp inMap
    rw [List.length_map] at two
    have groupNodup := grouping.group_nodup (places_nodup form) member
    obtain ⟨other, inOther, different⟩ : ∃ other ∈ group, other ≠ place := by
      have zeroMem : group[0]'(by omega) ∈ group := List.getElem_mem _
      have oneMem : group[1]'(by omega) ∈ group := List.getElem_mem _
      have distinct : group[0]'(by omega) ≠ group[1]'(by omega) := fun same => by
        have := (groupNodup.getElem_inj_iff).mp same
        omega
      by_cases zeroIs : group[0]'(by omega) = place
      · exact ⟨_, oneMem, fun same => distinct (zeroIs.trans same.symm)⟩
      · exact ⟨_, zeroMem, zeroIs⟩
    have linked := grouping.linked group member place inGroup other inOther
    rcases Relation.ReflTransGen.cases_head linked with same | ⟨next, ⟨_, _, shares⟩, _⟩
    · exact absurd same.symm different
    · obtain ⟨key, inKeys, _⟩ := shares
      simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range] at inKeys
      exact ⟨key, inKeys.1, inKeys.2⟩

end Entries

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
