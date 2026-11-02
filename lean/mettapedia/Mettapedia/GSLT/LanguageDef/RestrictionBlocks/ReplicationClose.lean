import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationPar

/-!
# Renaming and closing canonical blocks

An injective renaming of the outside reads a canonical block as it reads the block (`normal_renameOuter_normal`),
from the same fact for canonical forms. A copy group uses exactly the outside names of its replicated component
(`freeIn_of_copy`, `freeIn_of_copy_converse`), so it stays a copy group once the first outside name is bound by a
new restriction (`isCopy_close`), and closing a block reads it only through its canonical form
(`normal_close_normal`). Reading a block's components again under an order of its restrictions, one of each
replicated component, keeps its canonical form (`normal_reading`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex freeIn_apply)

variable {block : ReplicationBlock}

/-! ## Patterns of blocks renamed -/

/-- **Renaming a block's pattern renames its outside.** -/
theorem rename_toPattern (relabel : Nat → Nat) (form : Prenex) :
    rename relabel (Prenex.toPattern block.toBlock form) = Prenex.toPattern block.toBlock (form.renameOuter relabel) := by
  obtain ⟨count, components⟩ := form
  unfold Prenex.toPattern Prenex.renameOuter
  rw [rename_restricts (block := block.toBlock), rename_body (block := block.toBlock)]

/-- A block of atoms, every restriction used, reads canonically as its canonical block. -/
theorem canonicalOf_toPattern {form : Prenex} (atomic : form.Atomic block.toBlock) (used : form.Used) :
    canonicalOf block (Prenex.toPattern block.toBlock form) = Prenex.toPattern block.toBlock (normal block form) := by
  unfold canonicalOf
  rw [decompose_toPattern atomic used]

theorem renameOuter_atomic {form : Prenex} (atomic : form.Atomic block.toBlock) (relabel : Nat → Nat) :
    (form.renameOuter relabel).Atomic block.toBlock :=
  atomic_map_rename atomic _

theorem renameOuter_used {form : Prenex} (used : form.Used) (relabel : Nat → Nat) : (form.renameOuter relabel).Used := by
  obtain ⟨count, components⟩ := form
  exact used_rename used fun index below => by simp [liftIndex, below]

/-- Renaming the outside commutes with dropping unused restrictions. -/
theorem prune_renameOuter (form : Prenex) (relabel : Nat → Nat) :
    (form.renameOuter relabel).prune = form.prune.renameOuter relabel := by
  obtain ⟨count, components⟩ := form
  have usedSame : usedOf ⟨count, components.map (rename (liftIndex count relabel))⟩ = usedOf ⟨count, components⟩ := by
    unfold usedOf
    apply List.filter_congr
    intro index member
    have below : index < count := List.mem_range.mp member
    simp only [List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Function.comp_apply]
    refine exists_congr fun component => and_congr_right fun _ => ?_
    rw [mentions_iff, mentions_iff, freeIn_rename]
    constructor
    · rintro ⟨original, free, maps⟩
      by_cases low : original < count
      · simp only [liftIndex, if_pos low] at maps
        rwa [← maps]
      · simp only [liftIndex, if_neg low] at maps
        omega
    · intro free
      exact ⟨index, free, by simp [liftIndex, below]⟩
  simp only [Prenex.renameOuter, prune_eq, usedSame, List.map_map, Prenex.mk.injEq, true_and]
  refine List.map_congr_left fun component member => ?_
  simp only [Function.comp_apply, rename_comp]
  apply rename_congr
  intro index free
  simp only [Function.comp_apply]
  by_cases below : index < count
  · have inUsed : index ∈ usedOf ⟨count, components⟩ := by
      simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
      exact ⟨below, component, member, (mentions_iff _ _).mpr free⟩
    have position := List.idxOf_lt_length_of_mem inUsed
    rw [show liftIndex count relabel index = index by simp [liftIndex, below], groupIndex_below below]
    simp [liftIndex, position]
  · have shifted : liftIndex count relabel index = relabel (index - count) + count := by simp [liftIndex, below]
    rw [shifted, groupIndex_above (by omega), groupIndex_above (by omega)]
    simp only [liftIndex]
    rw [if_neg (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel]

section Close

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **An injective renaming of the outside reads a canonical block as it reads the block.** -/
theorem normal_renameOuter_normal {form : Prenex} (atomic : form.Atomic block.toBlock) {relabel : Nat → Nat}
    (injective : Function.Injective relabel) :
    normal block ((normal block form).renameOuter relabel) = normal block (form.renameOuter relabel) := by
  have prunedAtomic := prune_atomic atomic
  have prunedUsed := used_prune form
  have normalAtomic := normal_atomic fresh restrictFresh prunedAtomic
  have normalUsed := used_normal fresh restrictFresh _ prunedAtomic
  have key := canonicalOf_rename_canonicalOf fresh restrictFresh (Prenex.toPattern block.toBlock form.prune) injective
  rw [canonicalOf_toPattern prunedAtomic prunedUsed, rename_toPattern, rename_toPattern,
    canonicalOf_toPattern (renameOuter_atomic normalAtomic _) (renameOuter_used normalUsed _),
    canonicalOf_toPattern (renameOuter_atomic prunedAtomic _) (renameOuter_used prunedUsed _)] at key
  have renamedPrune : normal block (form.renameOuter relabel) = normal block (form.prune.renameOuter relabel) := by
    rw [← prune_renameOuter, normal_prune fresh restrictFresh _ (renameOuter_atomic atomic _)]
  rw [renamedPrune, ← normal_prune fresh restrictFresh form atomic]
  exact toPattern_injective (normal_atomic fresh restrictFresh (renameOuter_atomic normalAtomic _))
    (normal_atomic fresh restrictFresh (renameOuter_atomic prunedAtomic _)) key

/-- **Reading a block's components again under an order of its restrictions, one of each replicated component,
keeps its canonical form.** -/
theorem normal_reading {count : Nat} {order : List Nat} (isOrder : IsOrder count order) {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock) :
    normal block ⟨count, dedupReplicated block (sortComponents (components.map fun component =>
      recanon block (rename (Prenex.permute count order) component)))⟩ = normal block ⟨count, components⟩ := by
  set read := fun component => recanon block (rename (Prenex.permute count order) component) with readIs
  have readAtomic : (Prenex.mk count (components.map read)).Atomic block.toBlock := by
    intro component member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    have bundle := bundle_all fresh restrictFresh (size original + 1)
    exact recanon_atomic bundle.atomic bundle.nonEmpty (by rw [size_rename]; omega)
      (atomic_rename (atomic original inOriginal) _)
  have sortPerm : (sortComponents (components.map read)).Perm (components.map read) := List.perm_insertionSort _ _
  have sortedAtomic : (Prenex.mk count (sortComponents (components.map read))).Atomic block.toBlock :=
    fun component member => readAtomic component (sortPerm.subset member)
  have deduped := normal_dedupReplicated fresh restrictFresh (count := count)
    (sortComponents (components.map read)) [] sortedAtomic
  simp only [List.nil_append] at deduped
  rw [deduped, normal_perm fresh restrictFresh sortPerm sortedAtomic]
  have similar : SimilarR block ⟨count, components⟩ ⟨count, components.map read⟩ := by
    refine ⟨rfl, order, components.map read, isOrder, ?_, List.Perm.refl _⟩
    show List.Forall₂ (AlikeR block) (components.map (rename (Prenex.permute count order))) (components.map read)
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun component _ => alike_recanon_all fresh restrictFresh _
  exact (normal_similar_all fresh restrictFresh similar atomic readAtomic).symm

omit fresh restrictFresh in
/-- **A replicated component uses outside its block only names some member of each of its copy groups uses.** -/
theorem freeIn_of_copy_converse (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) {form : Prenex}
    {live : Finset Nat} (inside : live ⊆ (places form).toFinset) {p : Nat} {group : Finset Nat}
    (isCopy : (blockSystem block form).IsCopy live p group)
    {index : Nat} (used : FreeIn (index + form.count) (placeValue block form.components p)) :
    ∃ member ∈ group, FreeIn (index + form.count) (placeValue block form.components member) := by
  obtain ⟨count, components⟩ := form
  simp only at used ⊢
  have test : CopyTest block (canonicalOf block) count (placeValue block components p)
      (asGroup (allowedFor count (placeValue block components p)) count (placeValue block components)
        (group.sort (· ≤ ·))) := isCopy.isCopy
  obtain ⟨same, -, -, -⟩ := test
  generalize itemsIs : group.sort (· ≤ ·) = items at same
  generalize valueIs : placeValue block components = value at same used ⊢
  generalize allowedIs : allowedFor count (value p) = allowed at same
  generalize restrictionsIs : restrictionsOf allowed count value items = restrictions at same
  have restrictionsNodup : restrictions.Nodup := restrictionsIs ▸ restrictionsOf_nodup _ _ _ _
  have restrictionsBelow : ∀ restriction ∈ restrictions, restriction < count := fun _ restricted =>
    restrictionsOf_lt (restrictionsIs ▸ restricted)
  have fewer := length_le_of_inside restrictionsNodup restrictionsBelow
  obtain ⟨argument, componentIs⟩ := replicated_shape (block := block) (component := value p) (by
    have replicated : isReplicated block (placeValue block components p) = true := isCopy.isReplicated
    rwa [valueIs] at replicated)
  rw [componentIs] at same used
  simp only [argumentOf?] at same
  rw [freeIn_apply] at used
  obtain ⟨member, inArgument, argumentUses⟩ := used
  rw [List.mem_singleton] at inArgument
  rw [inArgument] at argumentUses
  have outsideLength := outsideOf_length restrictionsNodup restrictionsBelow
  -- the argument uses the name past the group's restrictions and the others
  have renamedUses : FreeIn (index + (outsideOf count restrictions).length)
      (rename (Prenex.groupIndex count (outsideOf count restrictions)) argument) := by
    rw [freeIn_rename]
    exact ⟨index + count, argumentUses, by rw [groupIndex_above (by omega)]; omega⟩
  have asGroupIs : asGroup allowed count value items = ⟨restrictions, items.map value⟩ := by
    rw [← restrictionsIs]
    rfl
  rw [asGroupIs] at same
  have canonicalUses := (freeIn_canonicalOf fresh restrictFresh _ _).mpr renamedUses
  rw [← same, freeIn_canonicalOf fresh restrictFresh] at canonicalUses
  unfold copyOf at canonicalUses
  rw [freeIn_toPattern] at canonicalUses
  simp only at canonicalUses
  obtain ⟨renamedComponent, inRenamed, renamedFree⟩ := canonicalUses
  obtain ⟨original, inItems, rfl⟩ := List.mem_map.mp inRenamed
  obtain ⟨item, inItemList, rfl⟩ := List.mem_map.mp inItems
  rw [freeIn_rename] at renamedFree
  obtain ⟨name, nameFree, maps⟩ := renamedFree
  have preserving := preserving_split restrictionsNodup restrictionsBelow
  by_cases below : name < count
  · have := preserving.below name below
    omega
  · rw [permute_split_above (by omega)] at maps
    refine ⟨item, ?_, ?_⟩
    · rw [← itemsIs] at inItemList
      exact (Finset.mem_sort _).mp inItemList
    · rwa [show index + count = name by omega]

omit fresh restrictFresh in
/-- **A copy group stays one once the first outside name is bound by a new restriction.** -/
theorem isCopy_close (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {count : Nat} {components : List Pattern} {live : Finset Nat}
    (inside : live ⊆ (places (Prenex.mk count components)).toFinset) {p : Nat} {group : Finset Nat}
    (isCopy : (blockSystem block ⟨count, components⟩).IsCopy live p group) :
    (blockSystem block ⟨count + 1, components⟩).IsCopy live p group := by
  set value := placeValue block components with valueIs
  -- the members of the group use the first outside name exactly when the replicated component does
  have memberUses : ∀ member ∈ group, mentions count (value member) = true → mentions count (value p) = true := by
    intro member inGroup mentioned
    rw [mentions_iff] at mentioned ⊢
    have := freeIn_of_copy (bound := size (Prenex.toPattern block.toBlock ⟨count, components⟩) + 1)
      (form := ⟨count, components⟩) (by have := mass_le_size_toPattern (block := block.toBlock) ⟨count, components⟩; omega)
      (fun pattern _ index => freeIn_canonicalOf fresh restrictFresh pattern index) inside isCopy inGroup
      (index := 0) (by simpa using mentioned)
    simpa using this
  have pUses : mentions count (value p) = true → ∃ member ∈ group, mentions count (value member) = true := by
    intro mentioned
    rw [mentions_iff] at mentioned
    obtain ⟨member, inGroup, free⟩ := freeIn_of_copy_converse fresh restrictFresh (form := ⟨count, components⟩) inside
      isCopy (index := 0) (by simpa using mentioned)
    exact ⟨member, inGroup, (mentions_iff _ _).mpr (by simpa using free)⟩
  have mentionsBelow : ∀ member index, index < count →
      (index ∈ (blockSystem block ⟨count + 1, components⟩).mentions member ↔
        index ∈ (blockSystem block ⟨count, components⟩).mentions member) := by
    intro member index below
    show index ∈ (usedRestrictions (count + 1) (value member)).toFinset ↔
      index ∈ (usedRestrictions count (value member)).toFinset
    simp only [List.mem_toFinset, mem_usedRestrictions]
    constructor
    · exact fun ⟨_, mentioned⟩ => ⟨below, mentioned⟩
    · exact fun ⟨_, mentioned⟩ => ⟨by omega, mentioned⟩
  have mentionsAt : ∀ member, count ∈ (blockSystem block ⟨count + 1, components⟩).mentions member ↔
      mentions count (value member) = true := by
    intro member
    show count ∈ (usedRestrictions (count + 1) (value member)).toFinset ↔ _
    simp only [List.mem_toFinset, mem_usedRestrictions]
    exact ⟨fun ⟨_, mentioned⟩ => mentioned, fun mentioned => ⟨by omega, mentioned⟩⟩
  have mentionsRange : ∀ member index, index ∈ (blockSystem block ⟨count + 1, components⟩).mentions member →
      index < count + 1 := by
    intro member index mentioned
    have : index ∈ (usedRestrictions (count + 1) (value member)).toFinset := mentioned
    simp only [List.mem_toFinset, mem_usedRestrictions] at this
    exact this.1
  -- links for the replicated component are those of the block, and none through the new restriction
  have linkBack : ∀ first ∈ group, ∀ second, (blockSystem block ⟨count + 1, components⟩).LinkFor p first second →
      (blockSystem block ⟨count, components⟩).LinkFor p first second := by
    intro first inFirst second link
    obtain ⟨restriction, inFirstMentions, inSecondMentions, notP⟩ := link
    have below := mentionsRange _ _ inFirstMentions
    by_cases isNew : restriction = count
    · subst isNew
      exact absurd ((mentionsAt p).mpr (memberUses first inFirst ((mentionsAt first).mp inFirstMentions))) notP
    · have low : restriction < count := by omega
      exact ⟨restriction, (mentionsBelow first restriction low).mp inFirstMentions,
        (mentionsBelow second restriction low).mp inSecondMentions,
        fun inP => notP ((mentionsBelow p restriction low).mpr inP)⟩
  have linkForth : ∀ first second, (blockSystem block ⟨count, components⟩).LinkFor p first second →
      (blockSystem block ⟨count + 1, components⟩).LinkFor p first second := by
    intro first second link
    obtain ⟨restriction, inFirstMentions, inSecondMentions, notP⟩ := link
    have low : restriction < count := by
      have : restriction ∈ (usedRestrictions count (value first)).toFinset := inFirstMentions
      simp only [List.mem_toFinset, mem_usedRestrictions] at this
      exact this.1
    exact ⟨restriction, (mentionsBelow first restriction low).mpr inFirstMentions,
      (mentionsBelow second restriction low).mpr inSecondMentions,
      fun inP => notP ((mentionsBelow p restriction low).mp inP)⟩
  refine ⟨isCopy.isLive, isCopy.isReplicated, ⟨isCopy.isGroup.subset, isCopy.isGroup.nonempty,
    fun first inFirst second inSecond => ?_, fun first inFirst second inSecond link =>
      isCopy.isGroup.closed first inFirst second inSecond (linkBack first inFirst second link)⟩, ?_⟩
  · have linked := isCopy.isGroup.linked first inFirst second inSecond
    clear inSecond
    induction linked with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step reached =>
        obtain ⟨inA, inB, link⟩ := step
        exact reached.tail ⟨inA, inB, linkForth _ _ link⟩
  -- the copy test reads the same group's copy and the same renamed argument
  have test : CopyTest block (canonicalOf block) count (value p)
      (asGroup (allowedFor count (value p)) count value (group.sort (· ≤ ·))) := isCopy.isCopy
  show CopyTest block (canonicalOf block) (count + 1) (value p)
    (asGroup (allowedFor (count + 1) (value p)) (count + 1) value (group.sort (· ≤ ·)))
  set items := group.sort (· ≤ ·) with itemsIs
  have itemsGroup : ∀ item ∈ items, item ∈ group := fun item member => (Finset.mem_sort _).mp member
  have restrictionsSame : restrictionsOf (allowedFor (count + 1) (value p)) (count + 1) value items =
      restrictionsOf (allowedFor count (value p)) count value items := by
    unfold restrictionsOf
    rw [List.range_succ, List.filter_append]
    have lastOut : List.filter (fun index => items.any fun item =>
        (throughKeys (allowedFor (count + 1) (value p)) (count + 1) value item).contains index) [count] = [] := by
      simp only [List.filter_cons, List.filter_nil]
      rw [if_neg]
      simp only [List.any_eq_true, List.contains_iff_mem, not_exists, not_and]
      intro item member keyed
      unfold throughKeys at keyed
      simp only [List.mem_filter, List.contains_iff_mem, mem_usedRestrictions, allowedFor, List.mem_range,
        Bool.not_eq_eq_eq_not, Bool.not_true] at keyed
      obtain ⟨⟨_, itemMentions⟩, _, pNot⟩ := keyed
      rw [memberUses item (itemsGroup item member) itemMentions] at pNot
      cases pNot
    rw [lastOut, List.append_nil]
    apply List.filter_congr
    intro index member
    have below := List.mem_range.mp member
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.contains_iff_mem]
    refine exists_congr fun item => and_congr_right fun _ => ?_
    unfold throughKeys allowedFor
    simp only [List.mem_filter, List.contains_iff_mem, mem_usedRestrictions, List.mem_range]
    constructor
    · rintro ⟨⟨_, mentioned⟩, _, notP⟩
      exact ⟨⟨below, mentioned⟩, below, notP⟩
    · rintro ⟨⟨_, mentioned⟩, _, notP⟩
      exact ⟨⟨by omega, mentioned⟩, by omega, notP⟩
  set restrictions := restrictionsOf (allowedFor count (value p)) count value items with restrictionsIs
  have restrictionsNodup : restrictions.Nodup := restrictionsOf_nodup _ _ _ _
  have restrictionsBelow : ∀ restriction ∈ restrictions, restriction < count := fun _ restricted =>
    restrictionsOf_lt restricted
  have outsideSucc : outsideOf (count + 1) restrictions = outsideOf count restrictions ++ [count] := by
    unfold outsideOf
    rw [List.range_succ, List.filter_append]
    have notIn : count ∉ restrictions := fun member => by
      have := restrictionsBelow count member
      omega
    simp [notIn]
  have outsideLength := outsideOf_length restrictionsNodup restrictionsBelow
  have fewer := length_le_of_inside restrictionsNodup restrictionsBelow
  -- the group's copy is the same pattern
  have splitSame : Prenex.permute (count + 1) (splitOrder (count + 1) (outsideOf (count + 1) restrictions)
      restrictions) = Prenex.permute count (splitOrder count (outsideOf count restrictions) restrictions) := by
    funext index
    by_cases owned : index ∈ restrictions
    · have below := restrictionsBelow index owned
      rw [permute_split_inside owned (by omega), permute_split_inside owned below]
    · by_cases below : index < count
      · rw [permute_split_outside owned (by omega), permute_split_outside owned below, outsideSucc,
          List.idxOf_append_of_mem (mem_outsideOf.mpr ⟨below, owned⟩)]
      · by_cases isCount : index = count
        · subst isCount
          rw [permute_split_outside owned (by omega), permute_split_above (le_refl _), outsideSucc,
            List.idxOf_append_of_notMem (fun inOutside => by
              have := (mem_outsideOf.mp inOutside).1
              omega)]
          simp only [List.idxOf_cons_self, Nat.add_zero]
          omega
        · rw [permute_split_above (by omega), permute_split_above (by omega)]
  have argumentSame : rename (Prenex.groupIndex (count + 1) (outsideOf (count + 1) restrictions))
      (argumentOf? (value p)) = rename (Prenex.groupIndex count (outsideOf count restrictions)) (argumentOf? (value p)) := by
    apply rename_congr
    intro index free
    have mentioned : mentions index (value p) = true := by
      obtain ⟨argument, componentIs⟩ := replicated_shape (block := block) (component := value p)
        (isCopy.isReplicated : isReplicated block (placeValue block components p) = true)
      rw [componentIs] at free ⊢
      exact (mentions_iff _ _).mpr (freeIn_apply.mpr ⟨argument, List.mem_singleton_self _, free⟩)
    by_cases below : index < count
    · have outside : index ∈ outsideOf count restrictions := by
        refine mem_outsideOf.mpr ⟨below, fun owned => ?_⟩
        have allowed := restrictionsOf_allowed owned
        unfold allowedFor at allowed
        simp only [List.mem_filter, mentioned] at allowed
        simp at allowed
      rw [groupIndex_below (by omega), groupIndex_below below, outsideSucc, List.idxOf_append_of_mem outside]
    · by_cases isCount : index = count
      · subst isCount
        rw [groupIndex_below (by omega), groupIndex_above (le_refl _), outsideSucc,
          List.idxOf_append_of_notMem (fun inOutside => by
            have := (mem_outsideOf.mp inOutside).1
            omega)]
        simp
      · rw [groupIndex_above (by omega), groupIndex_above (by omega), outsideSucc, List.length_append]
        simp only [List.length_singleton]
        omega
  have copySame : copyOf block.toBlock (count + 1) ⟨restrictions, items.map value⟩ =
      copyOf block.toBlock count ⟨restrictions, items.map value⟩ := by
    unfold copyOf
    simp only
    rw [splitSame]
  obtain ⟨same, notReplicated, smaller, mentionedAll⟩ := test
  have groupIs : asGroup (allowedFor (count + 1) (value p)) (count + 1) value items = ⟨restrictions, items.map value⟩ := by
    unfold asGroup
    rw [restrictionsSame]
  have groupIs' : asGroup (allowedFor count (value p)) count value items = ⟨restrictions, items.map value⟩ := rfl
  rw [groupIs'] at same notReplicated smaller mentionedAll
  rw [groupIs]
  refine ⟨?_, ?_, smaller, fun index below mentioned => ?_⟩
  · rw [copySame, same]
    simp only
    rw [← argumentSame]
  · rw [copySame]
    exact notReplicated
  · by_cases low : index < count
    · exact mentionedAll index low mentioned
    · have isCount : index = count := by omega
      subst isCount
      obtain ⟨member, inGroup, memberMentions⟩ := pUses mentioned
      have inItems : member ∈ items := (Finset.mem_sort _).mpr inGroup
      exact ⟨value member, List.mem_map_of_mem inItems, memberMentions⟩

omit fresh restrictFresh in
/-- **A complete removal of a block's copy groups removes copy groups of the block closed over its first outside
name.** -/
theorem removes_close (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {count : Nat} {components : List Pattern} {live final : Finset Nat}
    (absorbs : (blockSystem block ⟨count, components⟩).Absorbs live final) :
    live ⊆ (places (Prenex.mk count components)).toFinset →
      (blockSystem block ⟨count + 1, components⟩).Removes live final := by
  induction absorbs with
  | done => exact fun _ => .refl
  | step isCopy _ recurse =>
      intro inside
      exact .step (isCopy_close fresh restrictFresh inside isCopy) (recurse (Finset.sdiff_subset.trans inside))

/-- **A canonical block uses past its restrictions the names its block uses.** -/
theorem freePast_normal_all {form : Prenex} (atomic : form.Atomic block.toBlock) (index : Nat) :
    (normal block form).FreePast index ↔ form.FreePast index :=
  freePast_normal (bound := form.mass + 1) (Nat.le_succ _) (lawful_all fresh restrictFresh atomic).2
    (fun pattern _ index => freeIn_canonicalOf fresh restrictFresh pattern index) index

omit fresh restrictFresh in
theorem any_mentions_iff_freePast (form : Prenex) :
    form.components.any (mentions form.count) = true ↔ form.FreePast 0 := by
  simp only [List.any_eq_true, Prenex.FreePast, Nat.zero_add, mentions_iff]

omit fresh restrictFresh in
/-- The order of a block's restrictions, the closed restriction kept last. -/
theorem permute_append_last {count : Nat} {order : List Nat} (isOrder : IsOrder count order) :
    Prenex.permute (count + 1) (order ++ [count]) = Prenex.permute count order := by
  have lengthIs : order.length = count := isOrder.length
  funext index
  unfold Prenex.permute
  by_cases below : index < count
  · rw [if_pos (by omega), if_pos below, List.getD_eq_getElem _ _ (by simp; omega),
      List.getD_eq_getElem _ _ (by omega), List.getElem_append_left (by omega)]
  · rw [if_neg below]
    by_cases isCount : index = count
    · subst isCount
      rw [if_pos (by omega), List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
      simp [lengthIs]
    · rw [if_neg (by omega)]

/-- **Closing a block reads it only through its canonical form.** -/
theorem normal_close_normal {form : Prenex} (atomic : form.Atomic block.toBlock) :
    normal block (normal block form).close = normal block form.close := by
  have pastIff := freePast_normal_all fresh restrictFresh atomic 0
  by_cases used : form.components.any (mentions form.count) = true
  · -- the closed name is used: a new restriction
    have normalUsed : (normal block form).components.any (mentions (normal block form).count) = true :=
      (any_mentions_iff_freePast _).mpr (pastIff.mpr ((any_mentions_iff_freePast _).mp used))
    rw [close_of_used normalUsed, close_of_used used]
    obtain ⟨count, components⟩ := form
    simp only [Prenex.restrict]
    obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh atomic
    obtain ⟨final, nodup, absorbs, absorbed⟩ := absorb_places blind
    have finalInside : ∀ place ∈ final, place < components.length := fun place member => by
      have := absorbs_subset absorbs (List.mem_toFinset.mpr member)
      simpa [places] using this
    -- the block closed absorbs the block's copy groups
    have closedAtomic : (Prenex.mk (count + 1) components).Atomic block.toBlock := atomic
    obtain ⟨closedLaws, closedBlind⟩ := lawful_all fresh restrictFresh closedAtomic
    have restricted := normal_restrict closedLaws closedBlind nodup finalInside
      (removes_close fresh restrictFresh absorbs (Finset.Subset.refl _))
    rw [← restricted]
    simp only [restrictTo]
    -- the kept components use the closed restriction
    set kept := final.map (placeValue block components) with keptIs
    have keptAtomic : (Prenex.mk count kept).Atomic block.toBlock := by
      intro component member
      obtain ⟨place, inFinal, rfl⟩ := List.mem_map.mp member
      exact atomic _ (placeValue_mem (finalInside place inFinal))
    have keptUses : kept.any (mentions count) = true := by
      obtain ⟨component, member, mentioned⟩ := List.any_eq_true.mp used
      obtain ⟨place, inside, rfl⟩ := List.getElem_of_mem member
      have valueIs : placeValue block components place = components[place] := List.getD_eq_getElem _ _ inside
      rw [← valueIs, mentions_iff] at mentioned
      obtain ⟨kept', inKept, keptUsed⟩ := absorbs_freeIn (bound := (Prenex.mk count components).mass + 1)
        (Nat.le_succ _) (fun pattern _ index => freeIn_canonicalOf fresh restrictFresh pattern index) absorbs 0
        (Finset.Subset.refl _) place (List.mem_toFinset.mpr (List.mem_range.mpr inside)) (by simpa using mentioned)
      exact List.any_eq_true.mpr ⟨_, List.mem_map_of_mem (List.mem_toFinset.mp inKept),
        (mentions_iff _ _).mpr (by simpa using keptUsed)⟩
    -- dropping unused restrictions of the closed block is closing the pruned block
    have usedSucc : usedOf ⟨count + 1, kept⟩ = usedOf ⟨count, kept⟩ ++ [count] := by
      unfold usedOf
      rw [List.range_succ, List.filter_append]
      simp only [List.filter_singleton, keptUses, cond_true]
    have prunedClosed : (Prenex.mk (count + 1) kept).prune =
        ⟨(Prenex.mk count kept).prune.count + 1, (Prenex.mk count kept).prune.components⟩ := by
      rw [prune_eq, prune_eq, usedSucc]
      simp only [List.length_append, List.length_singleton, Prenex.mk.injEq, true_and]
      refine List.map_congr_left fun component member => rename_congr _ fun index free => ?_
      by_cases below : index < count
      · have inUsed : index ∈ usedOf ⟨count, kept⟩ := by
          simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true]
          exact ⟨below, component, member, (mentions_iff _ _).mpr free⟩
        rw [groupIndex_below (by omega), groupIndex_below below, List.idxOf_append_of_mem inUsed]
      · by_cases isCount : index = count
        · subst isCount
          have notUsed : index ∉ usedOf ⟨index, kept⟩ := by
            simp [usedOf]
          rw [groupIndex_below (by omega), groupIndex_above (le_refl _),
            List.idxOf_append_of_notMem notUsed]
          simp
        · rw [groupIndex_above (by omega), groupIndex_above (by omega)]
          simp only [List.length_append, List.length_singleton]
          omega
    rw [← normal_prune fresh restrictFresh ⟨count + 1, kept⟩ (by
      intro component member
      exact keptAtomic component member), prunedClosed]
    -- the canonical block is a reading of the pruned block
    rw [normal_eq_reading ⟨count, components⟩, absorbed]
    simp only
    obtain ⟨order, inOrders, leastIs⟩ := least_reading_mem (block := block) (Prenex.mk count kept).prune
    have isOrder : IsOrder (Prenex.mk count kept).prune.count order := readingOrders_isOrder inOrders
    have prunedAtomic := prune_atomic keptAtomic
    rw [leastIs]
    generalize (Prenex.mk count kept).prune = pruned at isOrder prunedAtomic ⊢
    obtain ⟨prunedCount, prunedComponents⟩ := pruned
    simp only at isOrder ⊢
    have extended : IsOrder (prunedCount + 1) (order ++ [prunedCount]) := by
      unfold IsOrder
      rw [List.range_succ]
      exact isOrder.append_right _
    rw [← permute_append_last isOrder]
    exact normal_reading fresh restrictFresh extended prunedAtomic
  · -- the closed name is not used: the outside moves down past it
    have unused : form.components.any (mentions form.count) = false := Bool.eq_false_iff.mpr used
    have normalUnused : (normal block form).components.any (mentions (normal block form).count) = false := by
      apply Bool.eq_false_iff.mpr
      intro normalUses
      exact used ((any_mentions_iff_freePast _).mpr (pastIff.mp ((any_mentions_iff_freePast _).mp normalUses)))
    rw [close_of_unused normalUnused, close_of_unused unused]
    -- a bound on the names the block uses
    obtain ⟨bound, bounded⟩ := exists_bound_of_list (fun pattern bound => ∀ index, FreeIn index pattern → index < bound)
      (fun _ _ _ le holds index free => lt_of_lt_of_le (holds index free) le) form.components
      fun pattern _ => exists_freeBound pattern
    obtain ⟨relabel, injective, agrees⟩ := exists_injective_agree (fun outer => outer - 1) bound (fun outer => 1 ≤ outer)
      (fun first second _ firstIn _ secondIn same => by omega)
    have formIs : (⟨form.count, form.components.map (rename (dropIndex form.count))⟩ : Prenex) =
        form.renameOuter relabel := by
      simp only [Prenex.renameOuter, Prenex.mk.injEq, true_and]
      refine List.map_congr_left fun component member => rename_congr _ fun index free => ?_
      have notCount : index ≠ form.count := fun same => by
        rw [same] at free
        exact unused_of_any unused component member free
      have small := bounded component member index free
      unfold dropIndex liftIndex
      split_ifs with below
      · rfl
      · rw [agrees (index - form.count) (by omega) (by omega)]
        omega
    have normalIs : (⟨(normal block form).count, (normal block form).components.map
        (rename (dropIndex (normal block form).count))⟩ : Prenex) = (normal block form).renameOuter relabel := by
      simp only [Prenex.renameOuter, Prenex.mk.injEq, true_and]
      refine List.map_congr_left fun component member => rename_congr _ fun index free => ?_
      have notCount : index ≠ (normal block form).count := fun same => by
        rw [same] at free
        exact unused_of_any normalUnused component member free
      unfold dropIndex liftIndex
      split_ifs with below
      · rfl
      · have outerUsed : form.FreePast (index - (normal block form).count) :=
          (freePast_normal_all fresh restrictFresh atomic _).mp
            ⟨component, member, by rwa [Nat.sub_add_cancel (by omega)]⟩
        obtain ⟨original, inOriginal, originalFree⟩ := outerUsed
        have small := bounded original inOriginal _ originalFree
        rw [agrees (index - (normal block form).count) (by omega) (by omega)]
        omega
    rw [formIs, normalIs]
    exact normal_renameOuter_normal fresh restrictFresh atomic injective

end Close

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
