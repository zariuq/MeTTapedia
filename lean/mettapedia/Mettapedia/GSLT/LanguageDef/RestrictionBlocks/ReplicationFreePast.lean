import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationShapes
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyTwins

/-!
# Free names past a block, below a size

Reading a block keeps the names it uses past its restrictions, once canonical forms of lighter patterns keep their free
names: a component read again keeps its free names (`freeIn_recanon`), absorbing copy groups keeps every name the
block uses (`absorbs_freeIn`), as do dropping unused restrictions (`freePast_prune`) and reading the components again
under an order (`freePast_reading`), so a canonical block uses past its restrictions exactly what the block it reads
uses (`freePast_normal`). These hold below a size, so the induction on size that establishes the laws of absorption
can carry them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_apply freeIn_lambda freeIn_multiLambda freeIn_collection)

variable {block : ReplicationBlock}

/-! ## Readings keep their components -/

/-- **Keeping one of each replicated component keeps every component.** -/
theorem mem_dedupReplicated {target : Pattern} : ∀ {components : List Pattern},
    target ∈ dedupReplicated block components ↔ target ∈ components
  | [] => by simp [dedupReplicated]
  | component :: rest => by
      unfold dedupReplicated
      split_ifs with drop
      · rw [mem_dedupReplicated, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | member)
          · simp only [Bool.and_eq_true, List.contains_iff_mem] at drop
            exact drop.2
          · exact member
      · rw [List.mem_cons, List.mem_cons, mem_dedupReplicated]

theorem mem_reading_iff {components : List Pattern} {read : Pattern → Pattern} {target : Pattern} :
    target ∈ dedupReplicated block (sortComponents (components.map read)) ↔
      ∃ component ∈ components, read component = target := by
  rw [mem_dedupReplicated, mem_sortComponents, List.mem_map]

/-! ## Parts read again keep free names -/

theorem freeIn_multisetOf {form : Prenex} {index : Nat} :
    FreeIn index (multisetOf block.toBlock form) ↔ FreeIn index (Prenex.toPattern block.toBlock form) := by
  unfold multisetOf
  split_ifs with empty
  · rw [freeIn_collection, freeIn_toPattern, empty]
    simp
  · rw [freeIn_collection]
    simp

/-- A list read through a map keeping free names keeps them. -/
theorem exists_freeIn_map {elements : List Pattern} {read : Pattern → Pattern} {index : Nat}
    (keeps : ∀ element ∈ elements, FreeIn index (read element) ↔ FreeIn index element) :
    (∃ element ∈ elements.map read, FreeIn index element) ↔ ∃ element ∈ elements, FreeIn index element := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨element, member, rfl⟩, used⟩
    exact ⟨element, member, (keeps element member).mp used⟩
  · rintro ⟨element, member, used⟩
    exact ⟨_, ⟨element, member, rfl⟩, (keeps element member).mpr used⟩

/-- **A named multiset's argument read again keeps free names**, when canonical forms up to its size do. -/
theorem freeIn_multisetPart {argument : Pattern}
    (free : ∀ pattern, size pattern ≤ size argument → ∀ index,
      FreeIn index (canonicalOf block pattern) ↔ FreeIn index pattern)
    (index : Nat) : FreeIn index (multisetPart block argument) ↔ FreeIn index argument := by
  by_cases isOpen : ∃ kind elements rest, argument = .collection kind elements (some rest)
  · obtain ⟨kind, elements, rest, rfl⟩ := isOpen
    simp only [multisetPart, freeIn_collection]
    refine exists_freeIn_map fun element member => free element ?_ index
    have := size_lt_of_mem member
    simp only [size]
    omega
  by_cases isSubst : ∃ body replacement, argument = .subst body replacement
  · obtain ⟨body, replacement, rfl⟩ := isSubst
    rfl
  push Not at isOpen isSubst
  rw [multisetPart_other isOpen isSubst, freeIn_multisetOf]
  exact free argument le_rfl index

/-- **Reading a component's parts again keeps its free names**, when canonical forms of lighter patterns do. -/
theorem freeIn_recanon {component : Pattern}
    (free : ∀ pattern, size pattern < size component → ∀ index,
      FreeIn index (canonicalOf block pattern) ↔ FreeIn index pattern) :
    ∀ index, FreeIn index (recanon block component) ↔ FreeIn index component := by
  intro index
  cases component with
  | apply label arguments =>
      rw [recanon_apply, freeIn_apply, freeIn_apply]
      refine exists_freeIn_map fun argument member => ?_
      have small : size argument < size (Pattern.apply label arguments) := by
        have := size_lt_of_mem member
        simp only [size]
        omega
      unfold partOf
      split_ifs
      · rfl
      · exact freeIn_multisetPart (fun pattern lighter => free pattern (by omega)) index
      · exact free argument small index
  | lambda binder body =>
      rw [recanon_lambda, freeIn_lambda, freeIn_lambda]
      exact free body (by simp only [size]; omega) (index + 1)
  | multiLambda arity binders body =>
      rw [recanon_multiLambda, freeIn_multiLambda, freeIn_multiLambda]
      exact free body (by simp only [size]; omega) (index + arity)
  | collection kind elements rest =>
      rw [recanon_collection, freeIn_collection, freeIn_collection]
      refine exists_freeIn_map fun element member => free element ?_ index
      have := size_lt_of_mem member
      simp only [size]
      omega
  | bvar => rfl
  | fvar => rfl
  | subst => rfl

/-! ## A copy uses only what its replicated component uses -/

/-- **A copy group uses outside its block only names its replicated component uses**, when canonical forms of
patterns lighter than the block keep free names. -/
theorem freeIn_of_copy {form : Prenex} {bound : Nat} (heavy : form.mass ≤ bound)
    (free : ∀ pattern, size pattern < bound → ∀ index,
      FreeIn index (canonicalOf block pattern) ↔ FreeIn index pattern)
    {live : Finset Nat} (inside : live ⊆ (places form).toFinset) {p : Nat} {group : Finset Nat}
    (isCopy : (blockSystem block form).IsCopy live p group) {member : Nat} (inGroup : member ∈ group)
    {index : Nat} (used : FreeIn (index + form.count) (placeValue block form.components member)) :
    FreeIn (index + form.count) (placeValue block form.components p) := by
  obtain ⟨count, components⟩ := form
  simp only at heavy used ⊢
  have test : CopyTest block (canonicalOf block) count (placeValue block components p)
      (asGroup (allowedFor count (placeValue block components p)) count (placeValue block components)
        (group.sort (· ≤ ·))) := isCopy.isCopy
  obtain ⟨same, -, -, -⟩ := test
  generalize itemsIs : group.sort (· ≤ ·) = items at same
  have itemsNodup : items.Nodup := itemsIs ▸ Finset.sort_nodup _ _
  have memberItems : member ∈ items := itemsIs ▸ (Finset.mem_sort _).mpr inGroup
  generalize valueIs : placeValue block components = value at same used ⊢
  generalize allowedIs : allowedFor count (value p) = allowed at same
  generalize restrictionsIs : restrictionsOf allowed count value items = restrictions at same
  have restrictionsNodup : restrictions.Nodup := restrictionsIs ▸ restrictionsOf_nodup _ _ _ _
  have restrictionsBelow : ∀ restriction ∈ restrictions, restriction < count := fun _ restricted =>
    restrictionsOf_lt (restrictionsIs ▸ restricted)
  have fewer := length_le_of_inside restrictionsNodup restrictionsBelow
  -- the replicated component and its argument
  obtain ⟨argument, componentIs⟩ := replicated_shape (block := block) (component := value p) (by
    have replicated : isReplicated block (placeValue block components p) = true := isCopy.isReplicated
    rwa [valueIs] at replicated)
  rw [componentIs] at same ⊢
  simp only [argumentOf?] at same
  -- sizes: the group's copy and the argument are lighter than the block
  have pPlace : p < components.length := by
    have := inside isCopy.isLive
    simpa [places] using this
  have itemsPlace : ∀ item ∈ items, item < components.length := fun item member' => by
    have inGroup' : item ∈ group := (Finset.mem_sort _).mp (itemsIs ▸ member')
    have := inside (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup')).2
    simpa [places] using this
  have pNot : p ∉ items := fun inItems => by
    have inGroup' : p ∈ group := (Finset.mem_sort _).mp (itemsIs ▸ inItems)
    exact (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup')).1 rfl
  have weights := sizeList_places_le (block := block) (List.nodup_cons.mpr ⟨pNot, itemsNodup⟩)
    (fun item member' => by
      rcases List.mem_cons.mp member' with rfl | inItems
      · exact pPlace
      · exact itemsPlace item inItems)
  rw [valueIs] at weights
  simp only [List.map_cons, sizeList, componentIs, size] at weights
  have argumentPositive := size_pos argument
  have copySmall : size (copyOf block.toBlock count ⟨restrictions, items.map value⟩) < bound := by
    have massBound : (copyBlock count restrictions (items.map value)).mass ≤
        2 * count + sizeList (items.map value) := by
      rw [← restrictionsIs]
      exact copyBlock_mass
    have patternBound := size_toPattern_le (block := block.toBlock) (copyBlock count restrictions (items.map value))
    rw [copyOf_eq_copyBlock]
    simp only [Prenex.mass] at heavy
    exact lt_of_le_of_lt patternBound (by omega)
  have argumentSmall : size (rename (Prenex.groupIndex count (outsideOf count restrictions)) argument) < bound := by
    rw [size_rename]
    simp only [Prenex.mass] at heavy
    omega
  -- the name, as the group's copy uses it
  have copyUses : FreeIn (index + count - restrictions.length)
      (copyOf block.toBlock count ⟨restrictions, items.map value⟩) := by
    unfold copyOf
    rw [freeIn_toPattern]
    simp only
    refine ⟨_, List.mem_map_of_mem (List.mem_map_of_mem memberItems), ?_⟩
    rw [freeIn_rename]
    exact ⟨index + count, used, by rw [permute_split_above (by omega)]; omega⟩
  have canonicalUses := (free _ copySmall _).mpr copyUses
  have asGroupIs : asGroup allowed count value items = ⟨restrictions, items.map value⟩ := by
    rw [← restrictionsIs]
    rfl
  rw [asGroupIs] at same
  rw [same] at canonicalUses
  have argumentUses := (free _ argumentSmall _).mp canonicalUses
  rw [freeIn_rename] at argumentUses
  obtain ⟨original, originalFree, maps⟩ := argumentUses
  have outsideLength := outsideOf_length restrictionsNodup restrictionsBelow
  rw [freeIn_apply]
  refine ⟨argument, List.mem_singleton_self _, ?_⟩
  by_cases below : original < count
  · exfalso
    rw [groupIndex_below below] at maps
    by_cases outside : original ∈ outsideOf count restrictions
    · have := List.idxOf_lt_length_of_mem outside
      omega
    · have owned : original ∈ restrictions := by
        by_contra notOwned
        exact outside (mem_outsideOf.mpr ⟨below, notOwned⟩)
      have isAllowed : original ∈ allowed := restrictionsOf_allowed (restrictionsIs ▸ owned)
      have notMentioned : mentions original (value p) = false := by
        rw [← allowedIs] at isAllowed
        unfold allowedFor at isAllowed
        have := (List.mem_filter.mp isAllowed).2
        simpa using this
      have mentioned : mentions original (value p) = true := by
        rw [componentIs, mentions_iff, freeIn_apply]
        exact ⟨argument, List.mem_singleton_self _, originalFree⟩
      rw [notMentioned] at mentioned
      cases mentioned
  · rw [groupIndex_above (by omega)] at maps
    rwa [show index + count = original by omega]

/-- **Absorbing copy groups keeps every name the block uses past its restrictions.** -/
theorem absorbs_freeIn {form : Prenex} {bound : Nat} (heavy : form.mass ≤ bound)
    (free : ∀ pattern, size pattern < bound → ∀ index,
      FreeIn index (canonicalOf block pattern) ↔ FreeIn index pattern)
    {live final : Finset Nat} (absorbs : (blockSystem block form).Absorbs live final) (index : Nat) :
    live ⊆ (places form).toFinset → ∀ member ∈ live,
      FreeIn (index + form.count) (placeValue block form.components member) →
        ∃ kept ∈ final, FreeIn (index + form.count) (placeValue block form.components kept) := by
  induction absorbs with
  | done => exact fun _ member inLive used => ⟨member, inLive, used⟩
  | @step live final p copied isCopy _ recurse =>
      intro inside member inLive used
      have restInside : live \ copied ⊆ (places form).toFinset := Finset.sdiff_subset.trans inside
      by_cases inCopied : member ∈ copied
      · exact recurse restInside p isCopy.live_rest (freeIn_of_copy heavy free inside isCopy inCopied used)
      · exact recurse restInside member (Finset.mem_sdiff.mpr ⟨inLive, inCopied⟩) used

/-! ## Pruning and reading keep free names -/

/-- **Dropping unused restrictions keeps the names a block uses past them.** -/
theorem freePast_prune (form : Prenex) (index : Nat) : form.prune.FreePast index ↔ form.FreePast index := by
  rw [prune_eq]
  simp only [Prenex.FreePast, List.mem_map]
  constructor
  · rintro ⟨_, ⟨component, member, rfl⟩, used⟩
    rw [freeIn_rename] at used
    obtain ⟨original, originalFree, maps⟩ := used
    by_cases below : original < form.count
    · exfalso
      rw [groupIndex_below below] at maps
      have inUsed : original ∈ usedOf form := by
        simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
        exact ⟨below, component, member, (mentions_iff _ _).mpr originalFree⟩
      have := List.idxOf_lt_length_of_mem inUsed
      omega
    · rw [groupIndex_above (by omega)] at maps
      exact ⟨component, member, by rwa [show index + form.count = original by omega]⟩
  · rintro ⟨component, member, used⟩
    refine ⟨_, ⟨component, member, rfl⟩, ?_⟩
    rw [freeIn_rename]
    exact ⟨index + form.count, used, by rw [groupIndex_above (by omega)]; omega⟩

/-- **A block reordered keeps the names it uses past its restrictions.** -/
theorem freeIn_permute_past {count : Nat} {order : List Nat} (isOrder : IsOrder count order) (component : Pattern)
    (index : Nat) :
    FreeIn (index + count) (rename (Prenex.permute count order) component) ↔ FreeIn (index + count) component := by
  rw [freeIn_rename]
  constructor
  · rintro ⟨original, originalFree, maps⟩
    by_cases below : original < count
    · exfalso
      rw [Prenex.permute, if_pos below] at maps
      have placed : order.getD original original < count := by
        rw [List.getD_eq_getElem _ _ (by rw [isOrder.length]; exact below)]
        exact List.mem_range.mp (isOrder.subset (List.getElem_mem _))
      omega
    · rw [Prenex.permute, if_neg below] at maps
      rwa [← maps]
  · intro used
    exact ⟨index + count, used, by rw [Prenex.permute, if_neg (by omega)]⟩

/-- **A reading of a block keeps the names it uses past its restrictions**, when reading its components again
keeps their free names. -/
theorem freePast_reading {count : Nat} {components : List Pattern} {order : List Nat} (isOrder : IsOrder count order)
    (recanonFree : ∀ component ∈ components, ∀ index,
      FreeIn index (recanon block (rename (Prenex.permute count order) component)) ↔
        FreeIn index (rename (Prenex.permute count order) component))
    (index : Nat) :
    (∃ component ∈ dedupReplicated block (sortComponents (components.map fun component =>
        recanon block (rename (Prenex.permute count order) component))), FreeIn (index + count) component) ↔
      ∃ component ∈ components, FreeIn (index + count) component := by
  simp only [mem_reading_iff]
  constructor
  · rintro ⟨_, ⟨component, member, rfl⟩, used⟩
    exact ⟨component, member,
      (freeIn_permute_past isOrder component index).mp ((recanonFree component member _).mp used)⟩
  · rintro ⟨component, member, used⟩
    exact ⟨_, ⟨component, member, rfl⟩,
      (recanonFree component member _).mpr ((freeIn_permute_past isOrder component index).mpr used)⟩

/-! ## Canonical forms keep free names -/

/-- Absorbing keeps some of the live components. -/
theorem absorbs_subset {system : CopyGroups.System Nat} {live final : Finset Nat} (absorbs : system.Absorbs live final) :
    final ⊆ live := by
  induction absorbs with
  | done => exact Finset.Subset.refl _
  | step _ _ recurse => exact recurse.trans Finset.sdiff_subset

/-- The absorbed block of a block of atoms, as the places absorption keeps. -/
theorem absorb_places {form : Prenex} (blind : BlindOn block (canonicalOf block) form.count form.components) :
    ∃ final : List Nat, final.Nodup ∧ (blockSystem block form).Absorbs (places form).toFinset final.toFinset ∧
      absorb block (canonicalOf block) form = (Prenex.mk form.count (final.map (placeValue block form.components))).prune := by
  obtain ⟨final, nodup, absorbs, reached⟩ := absorbRounds_absorbs
    (height := fun place => size (canonicalOf block (argumentOf? (placeValue block form.components place))))
    blind form.components.length (places_nodup form) (places_inRange form) (by simp [places])
  refine ⟨final, nodup, absorbs, ?_⟩
  rw [places_map] at reached
  unfold absorb
  rw [reached]

/-- **A canonical block uses the names its block uses past its restrictions**, when canonical forms of lighter
patterns keep free names. -/
theorem freePast_normal {form : Prenex} {bound : Nat} (heavy : form.mass ≤ bound)
    (blind : BlindOn block (canonicalOf block) form.count form.components)
    (free : ∀ pattern, size pattern < bound → ∀ index,
      FreeIn index (canonicalOf block pattern) ↔ FreeIn index pattern)
    (index : Nat) : (normal block form).FreePast index ↔ form.FreePast index := by
  obtain ⟨final, finalNodup, absorbs, absorbed⟩ := absorb_places blind
  have finalInside : ∀ place ∈ final, place < form.components.length := by
    intro place member
    have := absorbs_subset absorbs (List.mem_toFinset.mpr member)
    simpa [places] using this
  have componentsSmall : ∀ component ∈
      (Prenex.mk form.count (final.map (placeValue block form.components))).prune.components, size component ≤ bound := by
    intro component member
    rw [prune_eq] at member
    obtain ⟨original, inFinal, rfl⟩ := List.mem_map.mp member
    obtain ⟨place, inPlaces, rfl⟩ := List.mem_map.mp inFinal
    rw [size_rename]
    have := size_lt_of_mem (placeValue_mem (block := block) (finalInside place inPlaces))
    simp only [Prenex.mass] at heavy
    omega
  have pruned := freePast_prune (Prenex.mk form.count (final.map (placeValue block form.components))) index
  rw [normal_eq_reading, absorbed]
  generalize (Prenex.mk form.count (final.map (placeValue block form.components))).prune = kept at componentsSmall pruned ⊢
  obtain ⟨count, components⟩ := kept
  obtain ⟨order, inOrders, leastIs⟩ := least_reading_mem (block := block) (Prenex.mk count components)
  have isOrder : IsOrder count order := readingOrders_isOrder inOrders
  have reading := freePast_reading (block := block) isOrder (fun component member => freeIn_recanon
    fun pattern lighter => free pattern (by
      rw [size_rename] at lighter
      have := componentsSmall component member
      omega)) index
  rw [← leastIs] at reading
  refine reading.trans (pruned.trans ?_)
  -- absorbing copy groups keeps what the block uses
  simp only [Prenex.FreePast]
  constructor
  · rintro ⟨_, inFinal, used⟩
    obtain ⟨place, inPlaces, rfl⟩ := List.mem_map.mp inFinal
    exact ⟨_, placeValue_mem (finalInside place inPlaces), used⟩
  · rintro ⟨component, member, used⟩
    obtain ⟨place, inside, rfl⟩ := List.getElem_of_mem member
    have valueIs : placeValue block form.components place = form.components[place] :=
      List.getD_eq_getElem _ _ inside
    rw [← valueIs] at used
    obtain ⟨kept, inKept, keptUsed⟩ := absorbs_freeIn heavy free absorbs index (Finset.Subset.refl _) place
      (List.mem_toFinset.mpr (List.mem_range.mpr inside)) used
    exact ⟨_, List.mem_map_of_mem (List.mem_toFinset.mp inKept), keptUsed⟩

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
