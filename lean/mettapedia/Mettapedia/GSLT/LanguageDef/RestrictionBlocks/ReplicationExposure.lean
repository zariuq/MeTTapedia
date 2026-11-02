import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationProtect

/-!
# A block without copy groups, in its canonical form

The canonical form of a block absorbs copies of replicated components. A block without copy groups absorbs nothing
(`absorb_of_no_copies`), so its components are in its canonical form, read again under the reading's renaming, one
of each replicated component kept, and every context reads beside them as beside the block's components
(`exposure_base`). A renaming injective on the restrictions a block uses keeps its canonical form
(`normal_rename_used`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex)

variable {block : ReplicationBlock}

/-! ## Renamings that keep the restrictions a block uses apart -/

/-- **The restrictions a renamed block uses are the images of those the block uses.** -/
theorem usedOf_rename_perm {count count' : Nat} {relabel : Nat → Nat} {components : List Pattern}
    (injective : ∀ first ∈ usedOf ⟨count, components⟩, ∀ second ∈ usedOf ⟨count, components⟩,
      relabel first = relabel second → first = second)
    (below : ∀ index ∈ usedOf ⟨count, components⟩, relabel index < count')
    (outer : ∀ index, count ≤ index → count' ≤ relabel index) :
    (usedOf ⟨count', components.map (rename relabel)⟩).Perm ((usedOf ⟨count, components⟩).map relabel) := by
  refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter _)
    ((List.nodup_range.filter _).map_on injective)).mpr fun index' => ?_
  constructor
  · intro member
    simp only [List.mem_filter, List.mem_range, List.any_map, List.any_eq_true, Function.comp_apply] at member
    obtain ⟨below', component, inComponents, mentioned'⟩ := member
    obtain ⟨index, rfl, mentioned⟩ := mentions_rename_image component mentioned'
    have inside : index < count := by
      by_contra notInside
      have := outer index (by omega)
      omega
    exact List.mem_map.mpr ⟨index, List.mem_filter.mpr ⟨List.mem_range.mpr inside,
      List.any_eq_true.mpr ⟨component, inComponents, mentioned⟩⟩, rfl⟩
  · intro member
    obtain ⟨index, used, rfl⟩ := List.mem_map.mp member
    obtain ⟨inside, mentionedAny⟩ := List.mem_filter.mp used
    obtain ⟨component, inComponents, mentioned⟩ := List.any_eq_true.mp mentionedAny
    refine List.mem_filter.mpr ⟨List.mem_range.mpr (below index used), List.any_eq_true.mpr
      ⟨rename relabel component, List.mem_map_of_mem inComponents, ?_⟩⟩
    rw [mentions_iff] at mentioned ⊢
    exact (freeIn_rename component).mpr ⟨index, mentioned, rfl⟩

/-- **A renaming injective on the restrictions a block uses keeps its canonical form**, when it maps them below the
new number of restrictions and the names outside past it, in their order. -/
theorem normal_rename_used (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {count count' : Nat} {relabel : Nat → Nat} {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock)
    (injective : ∀ first ∈ usedOf ⟨count, components⟩, ∀ second ∈ usedOf ⟨count, components⟩,
      relabel first = relabel second → first = second)
    (below : ∀ index ∈ usedOf ⟨count, components⟩, relabel index < count')
    (outer : ∀ index, relabel (count + index) = count' + index) :
    normal block ⟨count', components.map (rename relabel)⟩ = normal block ⟨count, components⟩ := by
  set used := usedOf ⟨count, components⟩ with usedIs
  set used' := usedOf ⟨count', components.map (rename relabel)⟩ with usedIs'
  have outerGe : ∀ index, count ≤ index → count' ≤ relabel index := fun index above => by
    have shifted := outer (index - count)
    rw [show count + (index - count) = index by omega] at shifted
    omega
  have perm : used'.Perm (used.map relabel) := usedOf_rename_perm injective below outerGe
  have usedNodup : used.Nodup := List.nodup_range.filter _
  have usedNodup' : used'.Nodup := List.nodup_range.filter _
  have lengthEq : used'.length = used.length := by rw [perm.length_eq, List.length_map]
  set order := used.map fun index => used'.idxOf (relabel index) with orderIs
  have inImage : ∀ index ∈ used, relabel index ∈ used' := fun index member =>
    perm.symm.subset (List.mem_map_of_mem member)
  have isOrder : IsOrder used.length order := by
    refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).mpr fun position => ?_
    · refine usedNodup.map_on fun first inFirst second inSecond same => injective first inFirst second inSecond ?_
      exact (List.idxOf_inj (inImage first inFirst)).mp same
    · simp only [orderIs, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨index, member, rfl⟩
        rw [← lengthEq]
        exact List.idxOf_lt_length_of_mem (inImage index member)
      · intro inside
        rw [← lengthEq] at inside
        obtain ⟨index, member, same⟩ := List.mem_map.mp (perm.subset (List.getElem_mem inside))
        exact ⟨index, member, by rw [same, usedNodup'.idxOf_getElem]⟩
  have preserving : Preserving used.length used.length (Prenex.permute used.length order) := by
    refine ⟨fun first second same => ?_, fun index inside => permute_lt isOrder inside, fun index above => ?_⟩
    · have back := congrFun (permute_inverse isOrder) first
      have back' := congrFun (permute_inverse isOrder) second
      simp only [Function.comp, id] at back back'
      rw [← back, ← back', same]
    · rw [permute_of_ge _ (by omega)]
      exact above
  have outerId : ∀ index, pruneRelabel used.length used.length (Prenex.permute used.length order) index = index := by
    intro index
    simp only [pruneRelabel]
    rw [permute_of_ge _ (by omega)]
    omega
  have renamedAtomic : (Prenex.mk count' (components.map (rename relabel))).Atomic block.toBlock :=
    atomic_map_rename atomic relabel
  have renamedPrune : (Prenex.mk count' (components.map (rename relabel))).prune =
      ⟨used.length, (Prenex.mk count components).prune.components.map
        (rename (Prenex.permute used.length order))⟩ := by
    rw [prune_eq, prune_eq]
    dsimp only
    simp only [List.map_map, Prenex.mk.injEq]
    refine ⟨lengthEq, List.map_congr_left fun component member => ?_⟩
    simp only [Function.comp_apply, rename_comp]
    apply rename_congr
    intro index free
    simp only [Function.comp_apply]
    by_cases inside : index < count
    · have usedIndex : index ∈ used := List.mem_filter.mpr ⟨List.mem_range.mpr inside,
        List.any_eq_true.mpr ⟨component, member, (mentions_iff _ _).mpr free⟩⟩
      have placed := List.idxOf_lt_length_of_mem usedIndex
      rw [groupIndex_below (below index usedIndex), groupIndex_below inside, Prenex.permute, if_pos placed,
        List.getD_eq_getElem _ _ (by simpa [orderIs] using placed), List.getElem_map, List.getElem_idxOf]
    · have above : count ≤ index := by omega
      rw [groupIndex_above (outerGe index above), groupIndex_above above]
      have shifted := outer (index - count)
      rw [show count + (index - count) = index by omega] at shifted
      rw [shifted, lengthEq]
      simp only [Prenex.permute]
      rw [← usedIs]
      split_ifs <;> omega
  have prunedAtomic : (Prenex.mk used.length (Prenex.mk count components).prune.components).Atomic block.toBlock :=
    prune_atomic atomic
  calc normal block ⟨count', components.map (rename relabel)⟩
      = normal block (Prenex.mk count' (components.map (rename relabel))).prune :=
        (normal_prune fresh restrictFresh _ renamedAtomic).symm
    _ = normal block ⟨used.length, (Prenex.mk count components).prune.components.map
          (rename (Prenex.permute used.length order))⟩ := by rw [renamedPrune]
    _ = normal block ⟨used.length, (Prenex.mk count components).prune.components⟩ :=
        normal_rename_eq fresh restrictFresh preserving outerId prunedAtomic
    _ = normal block (Prenex.mk count components).prune := rfl
    _ = normal block ⟨count, components⟩ := normal_prune fresh restrictFresh _ atomic

/-! ## Keeping one of each replicated component, counted -/

theorem count_dedupReplicated_plain {target : Pattern} (plain : isReplicated block target = false) :
    ∀ components : List Pattern, (dedupReplicated block components).count target = components.count target
  | [] => rfl
  | component :: rest => by
      unfold dedupReplicated
      split_ifs with drop
      · have different : component ≠ target := by
          rintro rfl
          simp [plain] at drop
        rw [count_dedupReplicated_plain plain rest, List.count_cons]
        simp [different]
      · rw [List.count_cons, List.count_cons, count_dedupReplicated_plain plain rest]

theorem count_dedupReplicated_replicated {target : Pattern} (replicated : isReplicated block target = true) :
    ∀ components : List Pattern,
      (dedupReplicated block components).count target = if target ∈ components then 1 else 0
  | [] => by simp [dedupReplicated]
  | component :: rest => by
      have recurse := count_dedupReplicated_replicated replicated rest
      unfold dedupReplicated
      by_cases drop : (isReplicated block component && rest.contains component) = true
      · rw [if_pos drop, recurse]
        simp only [Bool.and_eq_true, List.contains_iff_mem] at drop
        have same : target ∈ component :: rest ↔ target ∈ rest := by
          constructor
          · intro member
            rcases List.mem_cons.mp member with rfl | inRest
            · exact drop.2
            · exact inRest
          · exact List.mem_cons_of_mem _
        simp only [same]
      · rw [if_neg drop, List.count_cons, recurse]
        by_cases same : component = target
        · subst same
          have notRest : component ∉ rest := fun member => drop (by simp [replicated, member])
          simp [notRest]
        · have membership : target ∈ component :: rest ↔ target ∈ rest := by
            constructor
            · intro member
              rcases List.mem_cons.mp member with equal | inRest
              · exact absurd equal.symm same
              · exact inRest
            · exact List.mem_cons_of_mem _
          simp only [membership]
          simp [same]

/-- **Keeping one of each replicated component, beside components that are not replicated.** -/
theorem dedupReplicated_append_plain {plains components : List Pattern}
    (plain : ∀ component ∈ plains, isReplicated block component = false) :
    (dedupReplicated block (plains ++ components)).Perm (plains ++ dedupReplicated block components) := by
  rw [List.perm_iff_count]
  intro target
  cases replicatedIs : isReplicated block target with
  | false =>
      rw [count_dedupReplicated_plain replicatedIs, List.count_append, List.count_append,
        count_dedupReplicated_plain replicatedIs]
  | true =>
      have notPlain : target ∉ plains := fun member => by
        rw [plain target member] at replicatedIs
        exact Bool.false_ne_true replicatedIs
      rw [count_dedupReplicated_replicated replicatedIs, List.count_append,
        count_dedupReplicated_replicated replicatedIs, List.count_eq_zero_of_not_mem notPlain, Nat.zero_add]
      simp [List.mem_append, notPlain]

theorem dedupReplicated_perm {first second : List Pattern} (permutation : first.Perm second) :
    (dedupReplicated block first).Perm (dedupReplicated block second) := by
  rw [List.perm_iff_count]
  intro target
  cases replicatedIs : isReplicated block target with
  | false => rw [count_dedupReplicated_plain replicatedIs, count_dedupReplicated_plain replicatedIs, permutation.count_eq]
  | true =>
      rw [count_dedupReplicated_replicated replicatedIs, count_dedupReplicated_replicated replicatedIs]
      simp only [permutation.mem_iff]

/-! ## A block without copy groups -/

section Base

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- A component that is its own block, read again, is its own block. -/
theorem recanon_atom_all {component : Pattern}
    (atomic : decompose block.toBlock component = Prenex.atom component) :
    decompose block.toBlock (recanon block component) = Prenex.atom (recanon block component) := by
  have bundle := bundle_all fresh restrictFresh (size component + 1)
  exact recanon_atomic bundle.atomic bundle.nonEmpty (le_of_lt (Nat.lt_succ_self _)) atomic

/-- **Reading some components again keeps the canonical form.** -/
theorem normal_recanon_append {count : Nat} (others components : List Pattern)
    (atomic : (Prenex.mk count (others ++ components)).Atomic block.toBlock) :
    normal block ⟨count, others ++ components.map (recanon block)⟩ = normal block ⟨count, others ++ components⟩ := by
  have readAtomic : (Prenex.mk count (others ++ components.map (recanon block))).Atomic block.toBlock := by
    intro component member
    rcases List.mem_append.mp member with inOthers | inRead
    · exact atomic component (List.mem_append_left _ inOthers)
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inRead
      exact recanon_atom_all fresh restrictFresh (atomic original (List.mem_append_right _ inOriginal))
  refine normal_similar_all fresh restrictFresh ⟨rfl, List.range count, others ++ components, List.Perm.refl _, ?_,
    List.Perm.refl _⟩ readAtomic atomic
  rw [map_rename_permute_range]
  refine List.rel_append (List.forall₂_same.mpr fun component _ => AlikeR.refl component) ?_
  rw [List.forall₂_map_left_iff]
  exact List.forall₂_same.mpr fun component _ => (alike_recanon_all fresh restrictFresh component).symm

/-- **A block without copy groups absorbs nothing**: its absorption is its pruning. -/
theorem absorb_of_no_copies {form : Prenex} (atomic : form.Atomic block.toBlock)
    (none : ∀ p group, ¬ (blockSystem block form).IsCopy (places form).toFinset p group) :
    absorb block (canonicalOf block) form = form.prune := by
  obtain ⟨-, blind⟩ := lawful_all fresh restrictFresh atomic
  have once : absorbOnce block (canonicalOf block) form = Option.none := by
    cases found : absorbOnce block (canonicalOf block) form with
    | none => rfl
    | some next =>
        have mapped : (⟨form.count, (places form).map (placeValue block form.components)⟩ : Prenex) = form :=
          places_map form
        rw [← mapped] at found
        obtain ⟨position, inside, group, _, isCopy, _⟩ := absorbOnce_step (height := fun place =>
          size (canonicalOf block (argumentOf? (placeValue block form.components place)))) blind (places_nodup form)
          (places_inRange form) found
        exact absurd isCopy (none _ _)
  unfold absorb
  have rounds : ∀ rounds, absorbRounds block (canonicalOf block) rounds form = form := by
    intro rounds
    cases rounds with
    | zero => rfl
    | succ rounds => simp only [absorbRounds, once]
  rw [rounds]

/-- **The canonical form of a block without copy groups reads its components again under one renaming**, fixed by
the block: its components are the block's read again, one of each replicated component kept. The renaming keeps the
restrictions the block uses apart and below the canonical form's, and moves the names outside past them; beside any of
the block's components, every context using only restrictions the block uses reads as it reads, renamed, beside them
read again, one of each replicated component kept. -/
theorem exposure_base_uniform {count : Nat} {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock)
    (none : ∀ p group, ¬ (blockSystem block ⟨count, components⟩).IsCopy
      (places ⟨count, components⟩).toFinset p group) :
    ∃ relabel : Nat → Nat,
      (normal block ⟨count, components⟩).components.Perm
        (dedupReplicated block (components.map fun component => recanon block (rename relabel component))) ∧
      (∀ index, relabel (count + index) = (normal block ⟨count, components⟩).count + index) ∧
      (∀ index ∈ usedOf ⟨count, components⟩, relabel index < (normal block ⟨count, components⟩).count) ∧
      (∀ first ∈ usedOf ⟨count, components⟩, ∀ second ∈ usedOf ⟨count, components⟩,
        relabel first = relabel second → first = second) ∧
      ∀ others : List Pattern, (∀ other ∈ others, other ∈ components) →
      ∀ context : List Pattern, (∀ component ∈ context, decompose block.toBlock component = Prenex.atom component) →
        (∀ component ∈ context, ∀ index < count, mentions index component = true →
          index ∈ usedOf ⟨count, components⟩) →
        normal block ⟨count, others ++ context⟩ =
          normal block ⟨(normal block ⟨count, components⟩).count,
            dedupReplicated block (others.map fun other => recanon block (rename relabel other)) ++
              context.map (rename relabel)⟩ := by
  set form : Prenex := ⟨count, components⟩ with formIs
  have normalIs := normal_eq_reading (block := block) form
  rw [absorb_of_no_copies fresh restrictFresh atomic none] at normalIs
  obtain ⟨order, inOrders, readingIs⟩ : ∃ order ∈ readingOrders block form.prune,
      dedupReplicated block (sortComponents (form.prune.components.map fun component =>
        recanon block (rename (Prenex.permute form.prune.count order) component))) =
          least (readingsR block form.prune) := by
    have member := least_mem (readingsR_ne_nil (block := block) form.prune)
    simp only [readingsR, List.mem_map] at member
    exact member
  have isOrder : IsOrder form.prune.count order := readingOrders_isOrder inOrders
  set used := usedOf form with usedIs
  have countIs : form.prune.count = used.length := rfl
  set relabel := Prenex.permute form.prune.count order ∘ Prenex.groupIndex count used with relabelIs
  set read := fun component : Pattern => recanon block (rename relabel component) with readIs
  have componentsIs : (normal block form).components = dedupReplicated block (sortComponents (components.map read)) := by
    rw [normalIs]
    simp only
    rw [← readingIs, prune_eq]
    simp only [List.map_map]
    congr 2
    refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp_apply, readIs, rename_comp, relabelIs]
    rfl
  have countIs' : (normal block form).count = used.length := by rw [normalIs]; rfl
  have relabelBelow : ∀ index ∈ used, relabel index < used.length := by
    intro index member
    rw [relabelIs, Function.comp_apply, groupIndex_below (List.mem_range.mp (List.mem_filter.mp member).1)]
    rw [← countIs]
    exact permute_lt isOrder (by rw [countIs]; exact List.idxOf_lt_length_of_mem member)
  have relabelInjective : ∀ first ∈ used, ∀ second ∈ used, relabel first = relabel second → first = second := by
    intro first inFirst second inSecond same
    rw [relabelIs, Function.comp_apply, Function.comp_apply,
      groupIndex_below (List.mem_range.mp (List.mem_filter.mp inFirst).1),
      groupIndex_below (List.mem_range.mp (List.mem_filter.mp inSecond).1)] at same
    have back := congrFun (permute_inverse isOrder) (used.idxOf first)
    have back' := congrFun (permute_inverse isOrder) (used.idxOf second)
    simp only [Function.comp, id] at back back'
    have positions : used.idxOf first = used.idxOf second := by rw [← back, ← back', same]
    exact (List.idxOf_inj inFirst).mp positions
  have outer : ∀ index, relabel (count + index) = used.length + index := by
    intro index
    rw [relabelIs, Function.comp_apply, groupIndex_above (by omega : count ≤ count + index)]
    simp only [Prenex.permute]
    rw [countIs]
    split_ifs <;> omega
  refine ⟨relabel, ?_, ?_, ?_, relabelInjective, ?_⟩
  · rw [componentsIs]
    exact dedupReplicated_perm (List.perm_insertionSort _ _)
  · intro index
    rw [countIs', outer]
  · intro index member
    rw [countIs']
    exact relabelBelow index member
  · intro others inComponents context contextAtomic attached
    have othersAtomic : ∀ component ∈ others, decompose block.toBlock component = Prenex.atom component :=
      fun component member => atomic component (inComponents component member)
    have renamedContextAtomic : ∀ component ∈ context.map (rename relabel),
        decompose block.toBlock component = Prenex.atom component := by
      intro component member
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
      exact atomic_rename (contextAtomic original inOriginal) relabel
    -- the used restrictions of the context and the others are used by the block
    have usedInside : ∀ index ∈ usedOf ⟨count, context ++ others⟩, index ∈ used := by
      intro index member
      obtain ⟨inside, mentionedAny⟩ := List.mem_filter.mp member
      obtain ⟨component, inComponents', mentioned⟩ := List.any_eq_true.mp mentionedAny
      rcases List.mem_append.mp inComponents' with inContext | inOthers
      · exact attached component inContext index (List.mem_range.mp inside) mentioned
      · refine List.mem_filter.mpr ⟨inside, List.any_eq_true.mpr ?_⟩
        exact ⟨component, inComponents component inOthers, mentioned⟩
    have combinedAtomic : (Prenex.mk count (context ++ others)).Atomic block.toBlock := by
      intro component member
      rcases List.mem_append.mp member with inContext | inOthers
      · exact contextAtomic component inContext
      · exact othersAtomic component inOthers
    calc normal block ⟨count, others ++ context⟩
        = normal block ⟨count, context ++ others⟩ :=
          normal_perm fresh restrictFresh List.perm_append_comm (fun component member =>
            combinedAtomic component (List.perm_append_comm.subset member))
      _ = normal block ⟨used.length, (context ++ others).map (rename relabel)⟩ :=
          (normal_rename_used fresh restrictFresh combinedAtomic
            (fun first inFirst second inSecond same => relabelInjective first (usedInside first inFirst) second
              (usedInside second inSecond) same)
            (fun index member => relabelBelow index (usedInside index member)) outer).symm
      _ = normal block ⟨used.length, context.map (rename relabel) ++ others.map read⟩ := by
          rw [List.map_append]
          have readAll : others.map read = (others.map (rename relabel)).map (recanon block) := by
            rw [List.map_map]
            rfl
          rw [readAll, normal_recanon_append fresh restrictFresh _ _ (by
            intro component member
            rcases List.mem_append.mp member with inContext | inOthers
            · exact renamedContextAtomic component inContext
            · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inOthers
              exact atomic_rename (othersAtomic original inOriginal) relabel)]
      _ = normal block ⟨used.length, context.map (rename relabel) ++ dedupReplicated block (others.map read)⟩ := by
          refine (normal_dedupReplicated fresh restrictFresh _ _ ?_).symm
          intro component member
          rcases List.mem_append.mp member with inContext | inOthers
          · exact renamedContextAtomic component inContext
          · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inOthers
            exact recanon_atom_all fresh restrictFresh (atomic_rename (othersAtomic original inOriginal) relabel)
      _ = normal block ⟨(normal block form).count, dedupReplicated block (others.map read) ++
            context.map (rename relabel)⟩ := by
          rw [countIs']
          refine normal_perm fresh restrictFresh List.perm_append_comm ?_
          intro component member
          rcases List.mem_append.mp member with inContext | inRest
          · exact renamedContextAtomic component inContext
          · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp (mem_dedupReplicated.mp inRest)
            exact recanon_atom_all fresh restrictFresh (atomic_rename (othersAtomic original inOriginal) relabel)

/-- **The components of a block without copy groups are in its canonical form**, read again under the reading's
renaming: the parts beside the others, of which one of each replicated component is kept. The renaming keeps the
restrictions the block uses apart and below the canonical form's, and moves the names outside past them; every
context using only restrictions the block uses reads beside the others as it reads, renamed, beside the others kept. -/
theorem exposure_base {count : Nat} {components parts others : List Pattern}
    (permutation : components.Perm (parts ++ others))
    (atomic : (Prenex.mk count components).Atomic block.toBlock)
    (plain : ∀ part ∈ parts, isReplicated block part = false)
    (none : ∀ p group, ¬ (blockSystem block ⟨count, components⟩).IsCopy
      (places ⟨count, components⟩).toFinset p group) :
    ∃ (relabel : Nat → Nat) (restUnfolded : List Pattern),
      (normal block ⟨count, components⟩).components.Perm
        (parts.map (fun part => recanon block (rename relabel part)) ++ restUnfolded) ∧
      (∀ other ∈ others, recanon block (rename relabel other) ∈ restUnfolded) ∧
      (∀ index, relabel (count + index) = (normal block ⟨count, components⟩).count + index) ∧
      (∀ index ∈ usedOf ⟨count, components⟩, relabel index < (normal block ⟨count, components⟩).count) ∧
      (∀ first ∈ usedOf ⟨count, components⟩, ∀ second ∈ usedOf ⟨count, components⟩,
        relabel first = relabel second → first = second) ∧
      ∀ context : List Pattern, (∀ component ∈ context, decompose block.toBlock component = Prenex.atom component) →
        (∀ component ∈ context, ∀ index < count, mentions index component = true →
          index ∈ usedOf ⟨count, components⟩) →
        normal block ⟨count, others ++ context⟩ =
          normal block ⟨(normal block ⟨count, components⟩).count, restUnfolded ++ context.map (rename relabel)⟩ := by
  obtain ⟨relabel, componentsPerm, outer, below, injective, aligned⟩ := exposure_base_uniform fresh restrictFresh
    atomic none
  set read := fun component : Pattern => recanon block (rename relabel component) with readIs
  have plainRead : ∀ component ∈ parts.map read, isReplicated block component = false := by
    intro component member
    obtain ⟨part, inParts, rfl⟩ := List.mem_map.mp member
    simp only [readIs, isReplicated_recanon, isReplicated_rename]
    exact plain part inParts
  refine ⟨relabel, dedupReplicated block (others.map read), ?_, fun other member =>
    mem_dedupReplicated.mpr (List.mem_map_of_mem member), outer, below, injective, fun context contextAtomic attached =>
      aligned others (fun other member => permutation.symm.subset (List.mem_append_right _ member)) context contextAtomic
        attached⟩
  refine componentsPerm.trans ((dedupReplicated_perm (permutation.map read)).trans ?_)
  rw [List.map_append]
  exact dedupReplicated_append_plain plainRead

end Base

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
