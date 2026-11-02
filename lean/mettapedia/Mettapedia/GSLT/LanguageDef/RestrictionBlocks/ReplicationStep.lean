import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationFreePast

/-!
# The canonical form at every size

What absorption reads of canonical forms below a size (`Bundle`) holds at the next size (`Bundle.step`), so at
every size (`bundle_all`): the laws of every block's absorption system, canonical blocks of atoms that stay
nonempty, canonical forms read alike through injective renamings, with the same summary, of similar blocks alike.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex)

variable {block : ReplicationBlock}

/-! ## Readings -/

theorem mem_reading {components : List Pattern} {read : Pattern → Pattern} {target : Pattern}
    (member : target ∈ dedupReplicated block (sortComponents (components.map read))) :
    ∃ component ∈ components, read component = target := by
  have inSorted := dedupReplicated_subset _ member
  rw [mem_sortComponents] at inSorted
  exact List.mem_map.mp inSorted

/-- **Whether a block's pattern is a replication**: no restriction and one replicated component. -/
theorem isReplicated_toPattern (restrictFresh : block.replicate ≠ block.restrict) (form : Prenex) :
    isReplicated block (Prenex.toPattern block.toBlock form) =
      (decide (form.count = 0) && decide (form.components.length = 1) &&
        decide ((form.components.filter (isReplicated block)).length = 1)) := by
  obtain ⟨count, components⟩ := form
  cases count with
  | zero =>
      simp only [Prenex.toPattern, Prenex.restricts]
      match components with
      | [] => simp [Prenex.body, isReplicated]
      | [component] =>
          simp only [Prenex.body, List.length_singleton, List.filter_cons, List.filter_nil]
          cases isReplicated block component <;> simp
      | first :: second :: rest => simp [Prenex.body, isReplicated]
  | succ count =>
      simp only [Prenex.toPattern, Prenex.restricts_succ, isReplicated]
      simp [Ne.symm restrictFresh]

theorem isReplicated_toPattern_of_summary (restrictFresh : block.replicate ≠ block.restrict) {first second : Prenex}
    (same : first.summary block = second.summary block) :
    isReplicated block (Prenex.toPattern block.toBlock first) =
      isReplicated block (Prenex.toPattern block.toBlock second) := by
  rw [isReplicated_toPattern restrictFresh, isReplicated_toPattern restrictFresh]
  simp only [Prenex.summary, Prod.mk.injEq] at same
  rw [same.1, same.2.1, same.2.2.2]

/-- Reordering a block's restrictions and renaming its other names do not interfere. -/
theorem permute_liftIndex {count : Nat} {order : List Nat} (isOrder : IsOrder count order) (relabel : Nat → Nat)
    (index : Nat) :
    Prenex.permute count order (liftIndex count relabel index) =
      liftIndex count relabel (Prenex.permute count order index) := by
  have lengthIs := isOrder.length_eq
  simp only [List.length_range] at lengthIs
  by_cases below : index < count
  · have placed : order.getD index index < count := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.mem_range.mp (isOrder.subset (List.getElem_mem _))
    simp only [liftIndex, if_pos below, Prenex.permute, if_pos placed]
  · simp only [liftIndex, if_neg below, Prenex.permute, if_neg (by omega : ¬ relabel (index - count) + count < count)]

/-! ## What absorption reads below a size -/

/-- **What absorption reads of canonical forms below a size**: the canonical form below it, the summaries and the
atoms of canonical blocks, blocks staying nonempty, and the laws of lighter blocks. -/
structure Bundle (block : ReplicationBlock) (bound : Nat) : Prop where
  below : Below block bound
  summary : ∀ pattern, size pattern < bound → ∀ relabel, Function.Injective relabel →
    (normal block (decompose block.toBlock (rename relabel pattern))).summary block =
      (normal block (decompose block.toBlock pattern)).summary block
  atomic : ∀ pattern, size pattern < bound → (normal block (decompose block.toBlock pattern)).Atomic block.toBlock
  nonEmpty : ∀ pattern, size pattern < bound → (decompose block.toBlock pattern).components ≠ [] →
    (normal block (decompose block.toBlock pattern)).components ≠ []
  lawful : ∀ form : Prenex, form.mass < bound → form.Atomic block.toBlock →
    (blockSystem block form).Laws (places form).toFinset ∧ BlindOn block (canonicalOf block) form.count form.components
  /-- Canonical forms below the size keep the free names of the patterns they read. -/
  free : ∀ pattern, size pattern < bound → ∀ index, FreeIn index (canonicalOf block pattern) ↔ FreeIn index pattern

variable {bound : Nat}

/-- **The laws at the next size.** -/
theorem Bundle.lawful_next (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    (bundle : Bundle block bound) (form : Prenex) (small : form.mass ≤ bound) (atomic : form.Atomic block.toBlock) :
    (blockSystem block form).Laws (places form).toFinset ∧ BlindOn block (canonicalOf block) form.count form.components := by
  by_cases lighter : form.mass < bound
  · exact bundle.lawful form lighter atomic
  · exact lawful_step fresh restrictFresh bundle.below bundle.lawful form small atomic

/-- The components left by absorption are components of the block, renamed. -/
theorem mem_absorb {canonical : Pattern → Pattern} {form : Prenex} {component : Pattern}
    (member : component ∈ (absorb block canonical form).components) :
    ∃ original ∈ form.components, ∃ relabel, component = rename relabel original := by
  unfold absorb at member
  rw [prune_eq] at member
  obtain ⟨original, inRounds, rfl⟩ := List.mem_map.mp member
  exact ⟨original, (absorbRounds_subperm _ form).2.subset inRounds, _, rfl⟩

/-- The components of a block of a pattern weigh at most the pattern. -/
theorem size_le_of_decompose {pattern component : Pattern}
    (member : component ∈ (decompose block.toBlock pattern).components) : size component ≤ size pattern := by
  have := size_lt_of_mem member
  have := mass_decompose (block := block.toBlock) pattern
  simp only [Prenex.mass] at this
  omega

/-- **Canonical blocks are blocks of atoms at the next size.** -/
theorem Bundle.atomic_next (bundle : Bundle block bound) (pattern : Pattern) (small : size pattern ≤ bound) :
    (normal block (decompose block.toBlock pattern)).Atomic block.toBlock := by
  have formAtomic := decompose_atomic (base := block.toBlock) pattern
  rw [normal_eq_reading]
  intro component member
  obtain ⟨order, inOrders, leastIs⟩ :=
    least_reading_mem (block := block) (absorb block (canonicalOf block) (decompose block.toBlock pattern))
  simp only at member
  rw [leastIs] at member
  obtain ⟨absorbed, inAbsorbed, rfl⟩ := mem_reading member
  obtain ⟨original, inOriginal, relabel, rfl⟩ := mem_absorb inAbsorbed
  have originalSmall := size_le_of_decompose (block := block) inOriginal
  refine recanon_atomic bundle.atomic bundle.nonEmpty ?_ (atomic_rename (atomic_rename (formAtomic _ inOriginal) _) _)
  rw [size_rename, size_rename]
  omega

/-- **A nonempty block keeps a component at the next size.** -/
theorem Bundle.nonEmpty_next (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) (bundle : Bundle block bound) (pattern : Pattern)
    (small : size pattern ≤ bound) (nonempty : (decompose block.toBlock pattern).components ≠ []) :
    (normal block (decompose block.toBlock pattern)).components ≠ [] := by
  have formAtomic := decompose_atomic (base := block.toBlock) pattern
  have formMass := mass_decompose (block := block.toBlock) pattern
  obtain ⟨laws, blind⟩ := bundle.lawful_next fresh restrictFresh _ (by omega) formAtomic
  obtain ⟨final, finalNodup, finalIs, normalIs⟩ := normal_copies laws blind
  rw [normalIs]
  simp only
  -- something is left
  have placesNonempty : (places (decompose block.toBlock pattern)).toFinset.Nonempty := by
    obtain ⟨first, rest, isCons⟩ := List.exists_cons_of_ne_nil nonempty
    refine ⟨0, List.mem_toFinset.mpr (List.mem_range.mpr ?_)⟩
    rw [isCons]
    simp
  obtain ⟨left, leftIn, notCopy⟩ := CopyGroups.System.exists_not_copy laws (Finset.Subset.refl _) placesNonempty
  have inFinal : left ∈ final := by
    rw [← List.mem_toFinset, finalIs]
    exact Finset.mem_sdiff.mpr ⟨leftIn, notCopy⟩
  have finalNonempty : (Prenex.mk (decompose block.toBlock pattern).count
      (final.map (placeValue block (decompose block.toBlock pattern).components))).prune.components ≠ [] := by
    rw [prune_eq]
    simp only [List.map_eq_nil_iff, ne_eq]
    exact List.ne_nil_of_mem inFinal
  obtain ⟨order, _, leastIs⟩ := least_reading_mem (block := block) (Prenex.mk (decompose block.toBlock pattern).count
    (final.map (placeValue block (decompose block.toBlock pattern).components))).prune
  rw [leastIs]
  apply dedupReplicated_ne_nil
  intro sortedEmpty
  obtain ⟨first, firstIn⟩ := List.exists_mem_of_ne_nil _ finalNonempty
  have inSorted := mem_sortComponents.mpr (List.mem_map_of_mem
    (f := fun component => recanon block (rename (Prenex.permute (Prenex.mk (decompose block.toBlock pattern).count
      (final.map (placeValue block (decompose block.toBlock pattern).components))).prune.count order) component))
    firstIn)
  rw [sortedEmpty] at inSorted
  simp at inSorted

/-- **A pattern's canonical block and its renamed pattern's**, read off one absorbed block. -/
theorem Bundle.normal_rename_pattern (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) (bundle : Bundle block bound) (pattern : Pattern)
    (small : size pattern ≤ bound) {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    ∃ form : Prenex, (∀ component ∈ form.components, size component ≤ bound) ∧
      normal block (decompose block.toBlock pattern) = ⟨form.count, least (readingsR block form)⟩ ∧
      normal block (decompose block.toBlock (rename relabel pattern)) =
        ⟨form.count, least (readingsR block (form.renameOuter relabel))⟩ := by
  have formAtomic := decompose_atomic (base := block.toBlock) pattern
  have formMass := mass_decompose (block := block.toBlock) pattern
  obtain ⟨laws, blind⟩ := bundle.lawful_next fresh restrictFresh _ (by omega) formAtomic
  have preserving : Preserving (decompose block.toBlock pattern).count (decompose block.toBlock pattern).count
      (liftIndex (decompose block.toBlock pattern).count relabel) := by
    refine ⟨liftIndex_injective injective _, fun index below => ?_, fun index above => ?_⟩
    · simp only [liftIndex, if_pos below]
      exact below
    · simp only [liftIndex, if_neg (by omega : ¬ index < (decompose block.toBlock pattern).count)]
      omega
  obtain ⟨final, _, finalIs, normalIs, normalIs'⟩ := normal_rename (count := (decompose block.toBlock pattern).count)
    (count' := (decompose block.toBlock pattern).count) (components := (decompose block.toBlock pattern).components)
    preserving (bundle.below.mono (by simp only [Prenex.mass] at formMass ⊢; omega)) formAtomic laws blind
  have relabelIs : pruneRelabel (decompose block.toBlock pattern).count (decompose block.toBlock pattern).count
      (liftIndex (decompose block.toBlock pattern).count relabel) = relabel := by
    funext index
    simp only [pruneRelabel, liftIndex, if_neg (by omega : ¬ index + (decompose block.toBlock pattern).count <
      (decompose block.toBlock pattern).count), Nat.add_sub_cancel]
  rw [relabelIs] at normalIs'
  refine ⟨_, ?_, normalIs, ?_⟩
  · intro component member
    rw [prune_eq] at member
    obtain ⟨original, inFinal, rfl⟩ := List.mem_map.mp member
    obtain ⟨place, placeIn, rfl⟩ := List.mem_map.mp inFinal
    have placeRange : place < (decompose block.toBlock pattern).components.length := by
      have := (Finset.mem_sdiff.mp (finalIs ▸ List.mem_toFinset.mpr placeIn)).1
      simpa [places] using this
    rw [size_rename]
    have := size_le_of_decompose (block := block) (placeValue_mem (block := block) placeRange)
    omega
  · rw [decompose_renameOuter]
    exact normalIs'

/-- **The summary at the next size.** -/
theorem Bundle.summary_next (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) (bundle : Bundle block bound) (pattern : Pattern)
    (small : size pattern ≤ bound) {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    (normal block (decompose block.toBlock (rename relabel pattern))).summary block =
      (normal block (decompose block.toBlock pattern)).summary block := by
  obtain ⟨form, sizes, normalIs, normalIs'⟩ := bundle.normal_rename_pattern fresh restrictFresh pattern small injective
  rw [normalIs, normalIs']
  obtain ⟨order, inOrders, leastIs⟩ := least_reading_mem (block := block) form
  obtain ⟨order', inOrders', leastIs'⟩ := least_reading_mem (block := block) (form.renameOuter relabel)
  have isOrder := readingOrders_isOrder inOrders
  have isOrder' := readingOrders_isOrder inOrders'
  have renamedIs : (form.renameOuter relabel).components.map (fun component =>
      recanon block (rename (Prenex.permute (form.renameOuter relabel).count order') component)) =
      form.components.map (fun component => recanon block
        (rename (Prenex.permute form.count order' ∘ liftIndex form.count relabel) component)) := by
    simp only [Prenex.renameOuter, List.map_map]
    refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp_apply, rename_comp]
  rw [leastIs, leastIs', renamedIs]
  have first := reading_summary bundle.below bundle.atomic bundle.summary sizes (permute_injective isOrder)
  have second := reading_summary bundle.below bundle.atomic bundle.summary sizes
    (relabel := Prenex.permute form.count order' ∘ liftIndex form.count relabel)
    ((permute_injective isOrder').comp (liftIndex_injective injective form.count))
  simp only [Prenex.summary]
  rw [second.1, second.2.1, second.2.2, first.1, first.2.1, first.2.2]

/-- **Equal canonical forms stay equal under an injective renaming**, at the next size. -/
theorem Bundle.renamed_of_same (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) (bundle : Bundle block bound) {first second : Pattern}
    (firstSmall : size first ≤ bound) (secondSmall : size second ≤ bound) {relabel : Nat → Nat}
    (injective : Function.Injective relabel) (same : canonicalOf block first = canonicalOf block second) :
    canonicalOf block (rename relabel first) = canonicalOf block (rename relabel second) := by
  obtain ⟨formA, sizesA, normalA, normalA'⟩ := bundle.normal_rename_pattern fresh restrictFresh first firstSmall injective
  obtain ⟨formB, sizesB, normalB, normalB'⟩ :=
    bundle.normal_rename_pattern fresh restrictFresh second secondSmall injective
  have blocksSame : normal block (decompose block.toBlock first) = normal block (decompose block.toBlock second) :=
    toPattern_injective (bundle.atomic_next first firstSmall) (bundle.atomic_next second secondSmall) same
  rw [normalA, normalB] at blocksSame
  simp only [Prenex.mk.injEq] at blocksSame
  obtain ⟨countSame, leastSame⟩ := blocksSame
  unfold canonicalOf
  rw [normalA', normalB']
  -- the least readings, reordered to the orders that gave them
  obtain ⟨orderA, inOrdersA, leastA⟩ := least_reading_mem (block := block) formA
  obtain ⟨orderB, inOrdersB, leastB⟩ := least_reading_mem (block := block) formB
  have isOrderA := readingOrders_isOrder inOrdersA
  have isOrderB := readingOrders_isOrder inOrdersB
  set reorderedA : Prenex := ⟨formA.count, formA.components.map (rename (Prenex.permute formA.count orderA))⟩
    with reorderedAIs
  set reorderedB : Prenex := ⟨formB.count, formB.components.map (rename (Prenex.permute formB.count orderB))⟩
    with reorderedBIs
  have commute : ∀ (form : Prenex) (order : List Nat), IsOrder form.count order →
      (form.renameOuter relabel).components.map (rename (Prenex.permute form.count order)) =
        ((Prenex.mk form.count (form.components.map (rename (Prenex.permute form.count order)))).renameOuter
          relabel).components := by
    intro form order isOrder
    simp only [Prenex.renameOuter, List.map_map]
    refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp_apply, rename_comp]
    congr 1
    funext index
    exact permute_liftIndex isOrder relabel index
  have similarA : SimilarR block (formA.renameOuter relabel) (reorderedA.renameOuter relabel) := by
    refine ⟨rfl, orderA, _, isOrderA, ?_, List.Perm.refl _⟩
    show List.Forall₂ (AlikeR block) ((formA.renameOuter relabel).components.map
      (rename (Prenex.permute formA.count orderA))) (reorderedA.renameOuter relabel).components
    rw [commute formA orderA isOrderA]
    exact List.forall₂_same.mpr fun component _ => AlikeR.refl component
  have similarB : SimilarR block (formB.renameOuter relabel) (reorderedB.renameOuter relabel) := by
    refine ⟨rfl, orderB, _, isOrderB, ?_, List.Perm.refl _⟩
    show List.Forall₂ (AlikeR block) ((formB.renameOuter relabel).components.map
      (rename (Prenex.permute formB.count orderB))) (reorderedB.renameOuter relabel).components
    rw [commute formB orderB isOrderB]
    exact List.forall₂_same.mpr fun component _ => AlikeR.refl component
  have stepA := least_reading_eq (block := block) similarA
  have stepB := least_reading_eq (block := block) similarB
  simp only [Prenex.mk.injEq] at stepA stepB
  have reorderedSizesA : ∀ component ∈ reorderedA.components, size component ≤ bound := by
    intro component member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    rw [size_rename]
    exact sizesA original inOriginal
  have reorderedSizesB : ∀ component ∈ reorderedB.components, size component ≤ bound := by
    intro component member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    rw [size_rename]
    exact sizesB original inOriginal
  -- the reordered blocks read again alike, so they do through any renaming
  have identityReadings : dedupReplicated block (sortComponents (reorderedA.components.map (recanon block))) =
      dedupReplicated block (sortComponents (reorderedB.components.map (recanon block))) := by
    have viaA : reorderedA.components.map (recanon block) = formA.components.map fun component =>
        recanon block (rename (Prenex.permute formA.count orderA) component) := by
      rw [reorderedAIs]
      simp only [List.map_map]
      rfl
    have viaB : reorderedB.components.map (recanon block) = formB.components.map fun component =>
        recanon block (rename (Prenex.permute formB.count orderB) component) := by
      rw [reorderedBIs]
      simp only [List.map_map]
      rfl
    rw [viaA, viaB, ← leastA, ← leastB, leastSame]
  have countsSame : reorderedA.count = reorderedB.count := countSame
  -- the renamed blocks have one signature at each restriction: renaming outside the blocks keeps their signatures,
  -- reading again keeps names, and their components read again are the same
  have signaturesSame : ∀ index < (reorderedA.renameOuter relabel).count,
      signatureOf block (reorderedA.renameOuter relabel) index =
        signatureOf block (reorderedB.renameOuter relabel) index := by
    intro index inside
    simp only [Prenex.renameOuter] at inside ⊢
    have outside : ∀ form : Prenex, index < form.count →
        signatureOf block ⟨form.count, form.components.map (rename (liftIndex form.count relabel))⟩ index =
          signatureOf block form index := by
      intro form below
      refine signatureOf_map (fun component _ => ⟨fun other otherBelow => ?_, isReplicated_rename _ _⟩) below
      have fixed : liftIndex form.count relabel other = other := by simp [liftIndex, otherBelow]
      have kept := mentions_rename_of_injective (liftIndex_injective injective form.count) component other
      rwa [fixed] at kept
    have reading : ∀ form : Prenex, (∀ component ∈ form.components, size component ≤ bound) → index < form.count →
        signatureOf block ⟨form.count, form.components.map (recanon block)⟩ index = signatureOf block form index := by
      intro form small below
      refine signatureOf_map (fun component member => ⟨fun other _ => ?_, isReplicated_recanon _⟩) below
      apply Bool.eq_iff_iff.mpr
      rw [mentions_iff, mentions_iff]
      exact freeIn_recanon (fun pattern lighter => bundle.free pattern (by
        have := small component member
        omega)) other
    have members : ∀ component, component ∈ reorderedA.components.map (recanon block) ↔
        component ∈ reorderedB.components.map (recanon block) := by
      intro component
      have inA : component ∈ dedupReplicated block (sortComponents (reorderedA.components.map (recanon block))) ↔
          component ∈ reorderedA.components.map (recanon block) :=
        mem_dedupReplicated.trans (List.perm_insertionSort _ _).mem_iff
      have inB : component ∈ dedupReplicated block (sortComponents (reorderedB.components.map (recanon block))) ↔
          component ∈ reorderedB.components.map (recanon block) :=
        mem_dedupReplicated.trans (List.perm_insertionSort _ _).mem_iff
      rw [← inA, ← inB, identityReadings]
    have belowB : index < reorderedB.count := countsSame ▸ inside
    rw [outside reorderedA inside, outside reorderedB belowB, ← reading reorderedA reorderedSizesA inside,
      ← reading reorderedB reorderedSizesB belowB]
    exact signatureOf_congr (first := ⟨reorderedA.count, reorderedA.components.map (recanon block)⟩)
      (second := ⟨reorderedB.count, reorderedB.components.map (recanon block)⟩) countsSame members index
  have readingsSame : readingsR block (reorderedA.renameOuter relabel) = readingsR block (reorderedB.renameOuter relabel) := by
    unfold readingsR
    rw [readingOrders_congr (by simpa [Prenex.renameOuter] using countsSame) signaturesSame]
    simp only [Prenex.renameOuter]
    rw [countsSame]
    refine List.map_congr_left fun order inOrders => ?_
    have isOrder := readingOrders_isOrder inOrders
    simp only [List.map_map]
    have rewriteA : reorderedA.components.map ((fun component => recanon block
        (rename (Prenex.permute reorderedB.count order) component)) ∘ rename (liftIndex reorderedB.count relabel)) =
        reorderedA.components.map fun component => recanon block
          (rename (Prenex.permute reorderedB.count order ∘ liftIndex reorderedB.count relabel) component) := by
      refine List.map_congr_left fun component _ => ?_
      simp only [Function.comp_apply, rename_comp]
    have rewriteB : reorderedB.components.map ((fun component => recanon block
        (rename (Prenex.permute reorderedB.count order) component)) ∘ rename (liftIndex reorderedB.count relabel)) =
        reorderedB.components.map fun component => recanon block
          (rename (Prenex.permute reorderedB.count order ∘ liftIndex reorderedB.count relabel) component) := by
      refine List.map_congr_left fun component _ => ?_
      simp only [Function.comp_apply, rename_comp]
    rw [rewriteA, rewriteB]
    have injectiveRenaming := (permute_injective isOrder).comp (liftIndex_injective injective reorderedB.count)
    refine content_transfer (fun component member other otherMember => ?_) (fun component _ => ?_) identityReadings
    · have componentSmall : size component ≤ bound := by
        rcases List.mem_append.mp member with inA | inB
        · exact reorderedSizesA component inA
        · exact reorderedSizesB component inB
      have otherSmall : size other ≤ bound := by
        rcases List.mem_append.mp otherMember with inA | inB
        · exact reorderedSizesA other inA
        · exact reorderedSizesB other inB
      exact (recanon_rename_iff bundle.below bundle.atomic componentSmall otherSmall injectiveRenaming).symm
    · simp only [isReplicated_recanon, isReplicated_rename]
  congr 1
  simp only [Prenex.mk.injEq]
  refine ⟨countSame, ?_⟩
  rw [stepA.2, stepB.2, readingsSame]

/-- **Injective renamings read canonical forms alike exactly when they were alike**, at the next size. -/
theorem Bundle.renamed_next (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) (bundle : Bundle block bound) {first second : Pattern}
    (firstSmall : size first ≤ bound) (secondSmall : size second ≤ bound) {relabel : Nat → Nat}
    (injective : Function.Injective relabel) :
    canonicalOf block (rename relabel first) = canonicalOf block (rename relabel second) ↔
      canonicalOf block first = canonicalOf block second := by
  refine ⟨fun renamedSame => ?_, bundle.renamed_of_same fresh restrictFresh firstSmall secondSmall injective⟩
  classical
  -- undo the renaming on the names the renamed patterns read
  obtain ⟨back, backInjective, agree⟩ := exists_injective_on [rename relabel first, rename relabel second]
    (Function.invFun relabel) (fun index => ∃ original, relabel original = index)
    (fun pattern member index free => by
      rcases List.mem_cons.mp member with rfl | inRest
      · obtain ⟨original, _, sent⟩ := (freeIn_rename first).mp free
        exact ⟨original, sent⟩
      · rw [List.mem_singleton] at inRest
        subst inRest
        obtain ⟨original, _, sent⟩ := (freeIn_rename second).mp free
        exact ⟨original, sent⟩)
    (fun a b ⟨a0, aSent⟩ ⟨b0, bSent⟩ same => by
      subst aSent bSent
      rw [Function.leftInverse_invFun injective a0, Function.leftInverse_invFun injective b0] at same
      rw [same])
  have undo : ∀ pattern, rename (Function.invFun relabel) (rename relabel pattern) = pattern := by
    intro pattern
    rw [rename_comp, show Function.invFun relabel ∘ relabel = id from funext (Function.leftInverse_invFun injective),
      rename_id]
  have backAgain := bundle.renamed_of_same fresh restrictFresh (by rw [size_rename]; exact firstSmall)
    (by rw [size_rename]; exact secondSmall) backInjective renamedSame
  rw [agree _ List.mem_cons_self, agree _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), undo, undo]
    at backAgain
  exact backAgain

/-- **The canonical form at the next size.** -/
theorem Bundle.below_next (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) (bundle : Bundle block bound) : Below block (bound + 1) where
  similar := fun first second firstSmall secondSmall firstAtomic secondAtomic similar =>
    normal_similar similar bundle.below (by omega) (by omega) firstAtomic secondAtomic
      fun form small atomic => bundle.lawful_next fresh restrictFresh form small atomic
  renamed := fun first second firstSmall secondSmall relabel injective =>
    bundle.renamed_next fresh restrictFresh (by omega) (by omega) injective
  shape := fun pattern small relabel injective =>
    isReplicated_toPattern_of_summary restrictFresh
      (bundle.summary_next fresh restrictFresh pattern (by omega) injective)
  sized := fun pattern small relabel injective =>
    size_toPattern_of_summary (bundle.summary_next fresh restrictFresh pattern (by omega) injective) _

/-- **What absorption reads at one size holds at the next.** -/
theorem Bundle.step (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    (bundle : Bundle block bound) : Bundle block (bound + 1) where
  below := bundle.below_next fresh restrictFresh
  summary := fun pattern small _ injective => bundle.summary_next fresh restrictFresh pattern (by omega) injective
  atomic := fun pattern small => bundle.atomic_next pattern (by omega)
  nonEmpty := fun pattern small nonempty => bundle.nonEmpty_next fresh restrictFresh pattern (by omega) nonempty
  lawful := fun form small atomic => bundle.lawful_next fresh restrictFresh form (by omega) atomic
  free := fun pattern small index => by
    have heavy : (decompose block.toBlock pattern).mass ≤ bound :=
      (mass_decompose (block := block.toBlock) pattern).trans (by omega)
    have blind := (bundle.lawful_next fresh restrictFresh _ heavy (decompose_atomic (base := block.toBlock) pattern)).2
    unfold canonicalOf
    rw [freeIn_toPattern, freeIn_decompose (block := block.toBlock) pattern index]
    exact freePast_normal heavy blind bundle.free index

theorem bundle_zero : Bundle block 0 where
  below := ⟨fun _ _ small => absurd small (Nat.not_lt_zero _), fun _ _ small => absurd small (Nat.not_lt_zero _),
    fun _ small => absurd small (Nat.not_lt_zero _), fun _ small => absurd small (Nat.not_lt_zero _)⟩
  summary := fun _ small => absurd small (Nat.not_lt_zero _)
  atomic := fun _ small => absurd small (Nat.not_lt_zero _)
  nonEmpty := fun _ small => absurd small (Nat.not_lt_zero _)
  lawful := fun _ small => absurd small (Nat.not_lt_zero _)
  free := fun _ small => absurd small (Nat.not_lt_zero _)

/-- **What absorption reads of canonical forms holds at every size.** -/
theorem bundle_all (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict) :
    ∀ bound, Bundle block bound
  | 0 => bundle_zero
  | bound + 1 => (bundle_all fresh restrictFresh bound).step fresh restrictFresh

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks



