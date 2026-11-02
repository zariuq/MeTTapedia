import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationDuplicates

/-!
# The canonical form of a canonical form

Absorbing a block keeps its canonical form (`normal_absorb`): the copy groups go, then the unused restrictions
(`normal_prune`). A component is alike to its parts read again (`alike_recanon`) once canonical forms of its parts
are their own canonical forms, and a canonical block's components are such readings, one of each replicated one,
under some order of its restrictions; so a canonical block is its own canonical form (`normal_normal`), and so is a
canonical form (`canonicalOf_canonicalOf`). Hence a renaming reads a canonical form as it reads the pattern
(`canonicalOf_rename_canonicalOf`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)

variable {block : ReplicationBlock}

/-! ## Absorbing keeps the canonical form -/

theorem absorbs_removes {system : CopyGroups.System Nat} {live final : Finset Nat}
    (absorbs : system.Absorbs live final) : system.Removes live final := by
  induction absorbs with
  | done => exact .refl
  | step isCopy _ recurse => exact .step isCopy recurse

/-- **Dropping unused restrictions keeps the canonical form.** -/
theorem normal_prune (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    (form : Prenex) (atomic : form.Atomic block.toBlock) : normal block form.prune = normal block form := by
  obtain ⟨count, components⟩ := form
  set used := usedOf ⟨count, components⟩ with usedIs
  have nodup : used.Nodup := List.nodup_range.filter _
  have usedBelow : ∀ index ∈ used, index < count := fun index member => by
    rw [usedIs] at member
    unfold usedOf at member
    exact List.mem_range.mp (List.mem_filter.mp member).1
  -- the restrictions kept, back in place
  let embed : Nat → Nat := fun index => if index < used.length then used.getD index 0 else index - used.length + count
  have embedBelow : ∀ index (below : index < used.length), embed index = used[index]'below := fun index below => by
    simp only [embed, if_pos below, List.getD_eq_getElem _ _ below]
  have embedAbove : ∀ index, used.length ≤ index → embed index = index - used.length + count := fun index above => by
    simp only [embed, if_neg (by omega : ¬ index < used.length)]
  have preserving : Preserving used.length count embed := by
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
  have back : (components.map (rename (Prenex.groupIndex count used))).map (rename embed) = components := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id components]
    apply List.map_congr_left
    intro component member
    simp only [Function.comp, id]
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
  have prunedAtomic : ∀ component ∈ components.map (rename (Prenex.groupIndex count used)),
      decompose block.toBlock component = Prenex.atom component := atomic_map_rename atomic _
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh (form := ⟨used.length,
    components.map (rename (Prenex.groupIndex count used))⟩) prunedAtomic
  obtain ⟨final, _, _, normalIs, renamedIs⟩ := normal_rename preserving (below_all fresh restrictFresh _)
    prunedAtomic laws blind
  rw [prune_eq, ← usedIs, normalIs]
  conv_rhs => rw [← back]
  rw [renamedIs, renameOuter_of_id]
  intro index
  unfold pruneRelabel
  rw [embedAbove _ (by omega)]
  omega

/-- **Absorbing a block keeps its canonical form.** -/
theorem normal_absorb (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {form : Prenex} (atomic : form.Atomic block.toBlock) :
    normal block (absorb block (canonicalOf block) form) = normal block form := by
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh atomic
  obtain ⟨final, nodup, absorbs, absorbed⟩ := absorb_places blind
  have inside : ∀ place ∈ final, place < form.components.length := fun place member => by
    have := absorbs_subset absorbs (List.mem_toFinset.mpr member)
    simpa [places] using this
  have keptAtomic : (Prenex.mk form.count (final.map (placeValue block form.components))).Atomic block.toBlock := by
    intro component member
    obtain ⟨place, inFinal, rfl⟩ := List.mem_map.mp member
    exact atomic _ (placeValue_mem (inside place inFinal))
  rw [absorbed, normal_prune fresh restrictFresh _ keptAtomic]
  exact normal_restrict laws blind nodup inside (absorbs_removes absorbs)

/-- The components of an absorbed block are renamed components of the block. -/
theorem absorb_atomic {form : Prenex} (atomic : form.Atomic block.toBlock) :
    (absorb block (canonicalOf block) form).Atomic block.toBlock := by
  intro component member
  obtain ⟨original, inOriginal, relabel, rfl⟩ := mem_absorb member
  exact atomic_rename (atomic original inOriginal) relabel

theorem absorb_size {form : Prenex} {bound : Nat} (small : ∀ component ∈ form.components, size component ≤ bound) :
    ∀ component ∈ (absorb block (canonicalOf block) form).components, size component ≤ bound := by
  intro component member
  obtain ⟨original, inOriginal, relabel, rfl⟩ := mem_absorb member
  rw [size_rename]
  exact small original inOriginal

/-! ## A multiset read back -/

/-- **A canonical block read as a multiset decomposes into itself.** -/
theorem decompose_multisetOf {form : Prenex} (atomic : form.Atomic block.toBlock) (used : form.Used) :
    decompose block.toBlock (multisetOf block.toBlock form) = form := by
  unfold multisetOf
  split_ifs with empty
  · obtain ⟨count, components⟩ := form
    simp only at empty
    subst empty
    rw [decompose_bag, decomposeList_atoms atomic]
  · rw [decompose_bag]
    simp only [decomposeList]
    rw [decompose_toPattern atomic used, par_nil]

/-! ## Canonical forms are their own canonical forms -/

/-- Canonical forms below a size that are their own canonical forms. -/
def IdemUpTo (block : ReplicationBlock) (bound : Nat) : Prop :=
  ∀ pattern, size pattern < bound → canonicalOf block (canonicalOf block pattern) = canonicalOf block pattern

theorem IdemUpTo.mono {bound bound' : Nat} (idem : IdemUpTo block bound) (smaller : bound' ≤ bound) :
    IdemUpTo block bound' := fun pattern small => idem pattern (by omega)

section Idempotent

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- A canonical form that is its own canonical form has a canonical block that is its own. -/
theorem normal_normal_of_idem {pattern : Pattern}
    (idem : canonicalOf block (canonicalOf block pattern) = canonicalOf block pattern) :
    normal block (normal block (decompose block.toBlock pattern)) = normal block (decompose block.toBlock pattern) := by
  have twice : Prenex.toPattern block.toBlock (normal block (decompose block.toBlock (canonicalOf block pattern))) =
      Prenex.toPattern block.toBlock (normal block (decompose block.toBlock pattern)) := idem
  rw [decompose_canonicalOf fresh restrictFresh] at twice
  refine toPattern_injective ?_ (atomic_normal fresh restrictFresh pattern) twice
  have := atomic_normal fresh restrictFresh (canonicalOf block pattern)
  rwa [decompose_canonicalOf fresh restrictFresh] at this

/-- **A renaming reads a canonical form that is its own canonical form as it reads the pattern.** -/
theorem rename_canonicalOf_of_idem {pattern : Pattern}
    (idem : canonicalOf block (canonicalOf block pattern) = canonicalOf block pattern)
    {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    canonicalOf block (rename relabel (canonicalOf block pattern)) = canonicalOf block (rename relabel pattern) :=
  ((below_all fresh restrictFresh (max (size (canonicalOf block pattern)) (size pattern) + 1)).renamed _ _
    (Nat.lt_succ_of_le (le_max_left _ _)) (Nat.lt_succ_of_le (le_max_right _ _)) relabel injective).mpr idem

omit fresh restrictFresh in
theorem map_canonicalOf_idem {elements : List Pattern}
    (idem : ∀ element ∈ elements, canonicalOf block (canonicalOf block element) = canonicalOf block element) :
    (elements.map (canonicalOf block)).map (canonicalOf block) = elements.map (canonicalOf block) := by
  rw [List.map_map]
  exact List.map_congr_left fun element member => idem element member

/-- **Reading a part twice reads it once.** -/
theorem partOf_partOf {argument : Pattern} (idem : IdemUpTo block (size argument + 1)) (label : String) :
    partOf block label (partOf block label argument) = partOf block label argument := by
  unfold partOf
  split_ifs with isRestrict listed
  · rfl
  · by_cases isOpen : ∃ kind elements rest, argument = .collection kind elements (some rest)
    · obtain ⟨kind, elements, rest, rfl⟩ := isOpen
      simp only [multisetPart]
      rw [map_canonicalOf_idem fun element member => idem element (by
        have := size_lt_of_mem member
        simp only [size]
        omega)]
    by_cases isSubst : ∃ body replacement, argument = .subst body replacement
    · obtain ⟨body, replacement, rfl⟩ := isSubst
      rfl
    push Not at isOpen isSubst
    rw [multisetPart_other isOpen isSubst]
    have bagShape := multisetOf_shape block.toBlock (normal block (decompose block.toBlock argument))
    obtain ⟨elements, bagIs⟩ := bagShape
    rw [bagIs, multisetPart_other (fun _ _ _ equal => by cases equal) (fun _ _ equal => by cases equal), ← bagIs,
      decompose_multisetOf (atomic_normal fresh restrictFresh argument)
        (used_normal fresh restrictFresh _ (decompose_atomic (base := block.toBlock) argument)),
      normal_normal_of_idem fresh restrictFresh (idem argument (Nat.lt_succ_self _))]
  · exact idem argument (Nat.lt_succ_self _)

/-- **A part read again reads canonically as the argument.** -/
theorem canonicalOf_partOf {argument : Pattern} (idem : IdemUpTo block (size argument + 1)) (label : String) :
    canonicalOf block (partOf block label argument) = canonicalOf block argument := by
  unfold partOf
  split_ifs with isRestrict listed
  · rfl
  · by_cases isOpen : ∃ kind elements rest, argument = .collection kind elements (some rest)
    · obtain ⟨kind, elements, rest, rfl⟩ := isOpen
      simp only [multisetPart]
      rw [canonicalOf_atom (decompose_open kind (elements.map (canonicalOf block)) rest),
        canonicalOf_atom (decompose_open kind elements rest), recanon_collection, recanon_collection,
        map_canonicalOf_idem fun element member => idem element (by
          have := size_lt_of_mem member
          simp only [size]
          omega)]
    by_cases isSubst : ∃ body replacement, argument = .subst body replacement
    · obtain ⟨body, replacement, rfl⟩ := isSubst
      rfl
    push Not at isOpen isSubst
    rw [multisetPart_other isOpen isSubst]
    unfold canonicalOf
    rw [decompose_multisetOf (atomic_normal fresh restrictFresh argument)
        (used_normal fresh restrictFresh _ (decompose_atomic (base := block.toBlock) argument)),
      normal_normal_of_idem fresh restrictFresh (idem argument (Nat.lt_succ_self _))]
  · exact idem argument (Nat.lt_succ_self _)

/-- **Reading a component's parts twice reads them once.** -/
theorem recanon_recanon {component : Pattern} (idem : IdemUpTo block (size component)) :
    recanon block (recanon block component) = recanon block component := by
  cases component with
  | apply label arguments =>
      have parts : arguments.map (partOf block label ∘ partOf block label) = arguments.map (partOf block label) :=
        List.map_congr_left fun argument member => partOf_partOf fresh restrictFresh (idem.mono (by
          have := size_lt_of_mem member
          simp only [size]
          omega)) label
      rw [recanon_apply, recanon_apply, List.map_map, parts]
  | lambda binder body =>
      rw [recanon_lambda, recanon_lambda, idem body (by simp only [size]; omega)]
  | multiLambda arity binders body =>
      rw [recanon_multiLambda, recanon_multiLambda, idem body (by simp only [size]; omega)]
  | collection kind elements rest =>
      rw [recanon_collection, recanon_collection, map_canonicalOf_idem fun element member => idem element (by
        have := size_lt_of_mem member
        simp only [size]
        omega)]
  | bvar => rfl
  | fvar => rfl
  | subst => rfl

/-- **A component is alike to its parts read again**, once canonical forms of its parts are their own. -/
theorem alike_recanon {component : Pattern} (idem : IdemUpTo block (size component)) :
    AlikeR block component (recanon block component) := by
  refine ⟨fun index => (freeIn_recanon (fun pattern _ index =>
      freeIn_canonicalOf fresh restrictFresh pattern index) index).symm,
    (isReplicated_recanon component).symm, fun relabel injective => ?_, fun replicated relabel injective => ?_⟩
  · refine (recanon_rename_iff (below_all fresh restrictFresh
      (max (size component) (size (recanon block component))))
      (fun pattern _ => atomic_normal fresh restrictFresh pattern) (le_max_left _ _) (le_max_right _ _)
      injective).mpr ?_
    exact (recanon_recanon fresh restrictFresh idem).symm
  · obtain ⟨argument, rfl⟩ := replicated_shape replicated
    rw [recanon_apply]
    simp only [List.map_cons, List.map_nil, argumentOf?]
    have small : size argument + 1 ≤ size (Pattern.apply block.replicate [argument]) := by
      simp only [size, sizeList]
      omega
    refine ((below_all fresh restrictFresh (max (size argument)
      (size (partOf block block.replicate argument)) + 1)).renamed _ _ (Nat.lt_succ_of_le (le_max_left _ _))
      (Nat.lt_succ_of_le (le_max_right _ _)) relabel injective).mpr ?_
    exact (canonicalOf_partOf fresh restrictFresh (idem.mono small) _).symm

/-- **A canonical block is its own canonical form**, once canonical forms of its components' parts are their own. -/
theorem normal_normal_of {form : Prenex} {bound : Nat} (atomic : form.Atomic block.toBlock)
    (small : ∀ component ∈ form.components, size component ≤ bound) (idem : IdemUpTo block bound) :
    normal block (normal block form) = normal block form := by
  have absorbedAtomic := absorb_atomic (block := block) atomic
  have absorbedSmall := absorb_size (block := block) small
  have absorbedNormal := normal_absorb fresh restrictFresh atomic
  conv_lhs => rw [normal_eq_reading form]
  obtain ⟨order, inOrders, leastIs⟩ := least_reading_mem (block := block) (absorb block (canonicalOf block) form)
  rw [leastIs, ← absorbedNormal]
  generalize absorb block (canonicalOf block) form = absorbed at absorbedAtomic absorbedSmall inOrders ⊢
  obtain ⟨count, components⟩ := absorbed
  have isOrder : IsOrder count order := readingOrders_isOrder inOrders
  show normal block ⟨count, dedupReplicated block (sortComponents (components.map fun component =>
      recanon block (rename (Prenex.permute count order) component)))⟩ = normal block ⟨count, components⟩
  set read := fun component => recanon block (rename (Prenex.permute count order) component) with readIs
  have readAtomic : (Prenex.mk count (components.map read)).Atomic block.toBlock := by
    intro component member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    have bundle := bundle_all fresh restrictFresh (size original + 1)
    exact recanon_atomic bundle.atomic bundle.nonEmpty (by rw [size_rename]; omega)
      (atomic_rename (absorbedAtomic original inOriginal) _)
  have sortPerm : (sortComponents (components.map read)).Perm (components.map read) := List.perm_insertionSort _ _
  have sortedAtomic : (Prenex.mk count (sortComponents (components.map read))).Atomic block.toBlock :=
    fun component member => readAtomic component (sortPerm.subset member)
  have deduped := normal_dedupReplicated fresh restrictFresh (count := count)
    (sortComponents (components.map read)) [] sortedAtomic
  simp only [List.nil_append] at deduped
  rw [deduped, normal_perm fresh restrictFresh sortPerm sortedAtomic]
  -- the components read again are alike to the absorbed ones under the order
  have similar : SimilarR block ⟨count, components⟩ ⟨count, components.map read⟩ := by
    refine ⟨rfl, order, components.map read, isOrder, ?_, List.Perm.refl _⟩
    show List.Forall₂ (AlikeR block) (components.map (rename (Prenex.permute count order))) (components.map read)
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun component member => ?_
    exact alike_recanon fresh restrictFresh (idem.mono (by rw [size_rename]; exact absorbedSmall component member))
  exact (normal_similar_all fresh restrictFresh similar absorbedAtomic readAtomic).symm

/-- **A canonical form is its own canonical form.** -/
theorem canonicalOf_canonicalOf (pattern : Pattern) :
    canonicalOf block (canonicalOf block pattern) = canonicalOf block pattern := by
  suffices all : ∀ bound, IdemUpTo block bound from all _ pattern (Nat.lt_succ_self _)
  intro bound
  induction bound with
  | zero => exact fun _ small => absurd small (Nat.not_lt_zero _)
  | succ bound recurse =>
      intro pattern small
      have twice := normal_normal_of fresh restrictFresh (decompose_atomic (base := block.toBlock) pattern)
        (fun component member => (size_le_of_decompose member).trans (by omega)) recurse
      show Prenex.toPattern block.toBlock (normal block (decompose block.toBlock (canonicalOf block pattern))) =
        canonicalOf block pattern
      rw [decompose_canonicalOf fresh restrictFresh, twice]
      rfl

theorem idemUpTo_all (bound : Nat) : IdemUpTo block bound :=
  fun pattern _ => canonicalOf_canonicalOf fresh restrictFresh pattern

/-- **A canonical block is its own canonical form.** -/
theorem normal_normal {form : Prenex} (atomic : form.Atomic block.toBlock) :
    normal block (normal block form) = normal block form :=
  normal_normal_of fresh restrictFresh atomic (fun _ member => size_lt_of_mem member)
    (idemUpTo_all fresh restrictFresh _)

/-- **Every component is alike to its parts read again.** -/
theorem alike_recanon_all (component : Pattern) : AlikeR block component (recanon block component) :=
  alike_recanon fresh restrictFresh (idemUpTo_all fresh restrictFresh _)

/-- **An injective renaming reads a canonical form as it reads the pattern.** -/
theorem canonicalOf_rename_canonicalOf (pattern : Pattern) {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    canonicalOf block (rename relabel (canonicalOf block pattern)) = canonicalOf block (rename relabel pattern) :=
  rename_canonicalOf_of_idem fresh restrictFresh (canonicalOf_canonicalOf fresh restrictFresh pattern) injective

end Idempotent

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
