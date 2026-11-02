import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationEntryAbsorb

/-!
# Replicated molecules of canonical blocks

The replicated molecules of a block are those of its canonical block (`mem_replicatedOf_normal`), so a block of
replicated molecules reads its block only through the canonical block (`normal_replicatedOf_normal`). Replicated
molecules depend only on the replications they hold (`normal_replicated_of_mem_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex)

variable {block : ReplicationBlock}

theorem isReplicated_bang (pattern : Pattern) : isReplicated block (bang block pattern) = true := by
  unfold bang
  split_ifs with replicated
  · exact replicated
  · simp [isReplicated]

/-- **A replication is an atom.** -/
theorem replicated_atomic (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {component : Pattern} (replicated : isReplicated block component = true) :
    decompose block.toBlock component = Prenex.atom component := by
  obtain ⟨argument, rfl⟩ := replicated_shape replicated
  refine decompose_atom (fun equal => by simp at equal) (fun binder body equal => ?_) (fun elements equal => by
    cases equal) (fun label argument' equal => ?_)
  · simp only [Pattern.apply.injEq] at equal
    exact restrictFresh equal.1
  · simp only [Pattern.apply.injEq, List.cons.injEq] at equal
    rw [← equal.1]
    exact fresh

section Molecules

variable (multisetFresh : block.replicate ∉ block.multisets) (fresh : block.replicate ∉ block.emptyUnits)
  (restrictFresh : block.replicate ≠ block.restrict)

include multisetFresh fresh restrictFresh

/-- **The replicated molecules of a block are the entries of its places.** -/
theorem mem_replicatedOf_iff {form : Prenex} (atomic : form.Atomic block.toBlock) (pattern : Pattern) :
    pattern ∈ replicatedOf block (canonicalOf block) form ↔ IsEntry block form (places form) pattern := by
  rw [replicatedOf_eq_entries multisetFresh fresh restrictFresh atomic]
  exact mem_build_entries fresh restrictFresh atomic (places_nodup form)
    (fun place member => by simpa [places] using member) pattern

/-- **A block and its canonical block have the same replicated molecules.** -/
theorem mem_replicatedOf_normal {form : Prenex} (atomic : form.Atomic block.toBlock) (pattern : Pattern) :
    pattern ∈ replicatedOf block (canonicalOf block) (normal block form) ↔
      pattern ∈ replicatedOf block (canonicalOf block) form := by
  rw [mem_replicatedOf_iff multisetFresh fresh restrictFresh (normal_atomic fresh restrictFresh atomic),
    mem_replicatedOf_iff multisetFresh fresh restrictFresh atomic]
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh atomic
  obtain ⟨final, finalNodup, absorbs, absorbed⟩ := absorb_places blind
  have finalInside : ∀ place ∈ final, place < form.components.length := fun place member => by
    have := absorbs_subset absorbs (List.mem_toFinset.mpr member)
    simpa [places] using this
  set kept := Prenex.mk form.count (final.map (placeValue block form.components)) with keptIs
  have keptAtomic : kept.Atomic block.toBlock := by
    intro component member
    obtain ⟨place, inFinal, rfl⟩ := List.mem_map.mp member
    exact atomic _ (placeValue_mem (finalInside place inFinal))
  -- the canonical block is a reading of the absorbed block
  rw [normal_eq_reading form, absorbed]
  obtain ⟨order, inOrders, leastIs⟩ := least_reading_mem (block := block) kept.prune
  have isOrder : IsOrder kept.prune.count order := readingOrders_isOrder inOrders
  have prunedAtomic := prune_atomic keptAtomic
  rw [leastIs]
  have readAtomic : (Prenex.mk kept.prune.count (kept.prune.components.map fun component =>
      recanon block (rename (Prenex.permute kept.prune.count order) component))).Atomic block.toBlock := by
    intro component member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    have bundle := bundle_all fresh restrictFresh (size original + 1)
    exact recanon_atomic bundle.atomic bundle.nonEmpty (by rw [size_rename]; omega)
      (atomic_rename (prunedAtomic original inOriginal) _)
  have sortPerm : (sortComponents (kept.prune.components.map fun component =>
      recanon block (rename (Prenex.permute kept.prune.count order) component))).Perm
        (kept.prune.components.map fun component =>
          recanon block (rename (Prenex.permute kept.prune.count order) component)) := List.perm_insertionSort _ _
  have sortedAtomic : (Prenex.mk kept.prune.count (sortComponents (kept.prune.components.map fun component =>
      recanon block (rename (Prenex.permute kept.prune.count order) component)))).Atomic block.toBlock :=
    fun component member => readAtomic component (sortPerm.subset member)
  have deduped := isEntry_dedupReplicated fresh restrictFresh (count := kept.prune.count)
    (sortComponents (kept.prune.components.map fun component =>
      recanon block (rename (Prenex.permute kept.prune.count order) component))) [] sortedAtomic pattern
  simp only [List.nil_append] at deduped
  rw [deduped, isEntry_perm fresh restrictFresh sortPerm.symm readAtomic]
  rw [show (Prenex.mk kept.prune.count (kept.prune.components.map fun component =>
      recanon block (rename (Prenex.permute kept.prune.count order) component))) =
      ⟨kept.prune.count, kept.prune.components.map fun component =>
        recanon block (rename (Prenex.permute kept.prune.count order) component)⟩ from rfl]
  have placesRead : places (Prenex.mk kept.prune.count (kept.prune.components.map fun component =>
      recanon block (rename (Prenex.permute kept.prune.count order) component))) = places kept.prune := by
    simp [places]
  rw [placesRead]
  rw [isEntry_read fresh restrictFresh isOrder (components := kept.prune.components) prunedAtomic pattern]
  -- dropping unused restrictions, then the absorbed places
  rw [show (Prenex.mk kept.prune.count kept.prune.components) = kept.prune from rfl,
    isEntry_prune fresh restrictFresh keptAtomic pattern]
  -- the kept block's places are the places absorption keeps
  have keptPlaces : (places kept).map (fun position => final.getD position 0) = final := by
    simp only [places, keptIs, List.length_map]
    apply List.ext_getElem (by simp)
    intro index below _
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem _ _ (by simpa using below)
  have valueAt : ∀ position, position < final.length → placeValue block kept.components position =
      placeValue block form.components (final.getD position 0) := by
    intro position below
    rw [List.getD_eq_getElem _ _ below]
    show (final.map (placeValue block form.components)).getD position (.apply block.unit []) = _
    rw [List.getD_eq_getElem _ _ (by simpa using below), List.getElem_map]
  have mapped := isEntry_map (block := block) (form := kept) (form' := form) (live := places kept)
    (fun position => final.getD position 0)
    (fun first firstIn second secondIn same => by
      have firstBelow : first < final.length := by simpa [places, keptIs] using firstIn
      have secondBelow : second < final.length := by simpa [places, keptIs] using secondIn
      rw [List.getD_eq_getElem _ _ firstBelow, List.getD_eq_getElem _ _ secondBelow] at same
      exact (finalNodup.getElem_inj_iff).mp same)
    (fun first firstIn second secondIn => by
      have firstBelow : first < final.length := by simpa [places, keptIs] using firstIn
      have secondBelow : second < final.length := by simpa [places, keptIs] using secondIn
      simp only [Linked.Shares, keysAt, ← valueAt first firstBelow, ← valueAt second secondBelow]
      rfl)
    (fun group groupInside => by
      unfold entryOf restrictTo
      simp only [List.map_map]
      congr 4
      refine List.map_congr_left fun position member => ?_
      have below : position < final.length := by simpa [places, keptIs] using groupInside position member
      simp only [Function.comp_apply]
      exact (valueAt position below).symm)
    pattern
  rw [keptPlaces] at mapped
  rw [← mapped]
  -- absorbing keeps the entries
  have chain := isEntry_absorbs multisetFresh fresh restrictFresh atomic absorbs (Finset.Subset.refl _) pattern
  rw [isEntry_of_mem_iff fresh restrictFresh atomic (live' := final.toFinset.sort (· ≤ ·)) finalNodup
      (Finset.sort_nodup _ _) finalInside
      (fun place => by rw [Finset.mem_sort, List.mem_toFinset]) pattern, chain,
    isEntry_of_mem_iff fresh restrictFresh atomic (live := (places form).toFinset.sort (· ≤ ·))
      (live' := places form) (Finset.sort_nodup _ _) (places_nodup form)
      (fun place member => by
        have := (Finset.mem_sort _).mp member
        simpa [places] using this)
      (fun place => by rw [Finset.mem_sort, List.mem_toFinset]) pattern]

omit multisetFresh in
/-- **Blocks of the same replications have one canonical form.** -/
theorem normal_replicated_of_mem_iff {first second : List Pattern}
    (firstReplicated : ∀ component ∈ first, isReplicated block component = true)
    (secondReplicated : ∀ component ∈ second, isReplicated block component = true)
    (same : ∀ component, component ∈ first ↔ component ∈ second) :
    normal block ⟨0, first⟩ = normal block ⟨0, second⟩ := by
  have firstAtomic : (Prenex.mk 0 first).Atomic block.toBlock :=
    fun component member => replicated_atomic fresh restrictFresh (firstReplicated component member)
  have secondAtomic : (Prenex.mk 0 second).Atomic block.toBlock :=
    fun component member => replicated_atomic fresh restrictFresh (secondReplicated component member)
  have firstSorted : (sortComponents first).Perm first := List.perm_insertionSort _ _
  have secondSorted : (sortComponents second).Perm second := List.perm_insertionSort _ _
  have dedupFirst := normal_dedupReplicated fresh restrictFresh (count := 0) (sortComponents first) []
    (fun component member => firstAtomic component (firstSorted.subset member))
  have dedupSecond := normal_dedupReplicated fresh restrictFresh (count := 0) (sortComponents second) []
    (fun component member => secondAtomic component (secondSorted.subset member))
  simp only [List.nil_append] at dedupFirst dedupSecond
  have content : dedupReplicated block (sortComponents first) = dedupReplicated block (sortComponents second) := by
    apply content_eq
    intro target
    rw [count_content, count_content]
    split_ifs with replicated firstIn secondIn secondIn
    · rfl
    · exact absurd ((same target).mp firstIn) secondIn
    · exact absurd ((same target).mpr secondIn) firstIn
    · rfl
    · rw [List.count_eq_zero_of_not_mem (fun member => replicated (firstReplicated target member)),
        List.count_eq_zero_of_not_mem (fun member => replicated (secondReplicated target member))]
  rw [← normal_perm fresh restrictFresh firstSorted (fun component member => firstAtomic component
      (firstSorted.subset member)), ← dedupFirst, content, dedupSecond,
    normal_perm fresh restrictFresh secondSorted (fun component member => secondAtomic component
      (secondSorted.subset member))]

omit multisetFresh fresh restrictFresh in
theorem replicatedOf_replicated {form : Prenex} (component : Pattern)
    (member : component ∈ replicatedOf block (canonicalOf block) form) : isReplicated block component = true := by
  rw [replicatedOf_eq, groups_eq_build (block := block), List.map_map] at member
  obtain ⟨group, _, rfl⟩ := List.mem_map.mp member
  simp only [Function.comp_apply, moleculeEntry]
  split <;> (try split_ifs) <;> simp [isReplicated, *]

/-- **A block of replicated molecules reads its block only through the canonical block.** -/
theorem normal_replicatedOf_normal {form : Prenex} (atomic : form.Atomic block.toBlock) :
    normal block ⟨0, replicatedOf block (canonicalOf block) (normal block form)⟩ =
      normal block ⟨0, replicatedOf block (canonicalOf block) form⟩ :=
  normal_replicated_of_mem_iff fresh restrictFresh
    (replicatedOf_replicated) (replicatedOf_replicated)
    (mem_replicatedOf_normal multisetFresh fresh restrictFresh atomic)

omit multisetFresh in
/-- **Places sharing no restriction across two lists have the entries of either.** -/
theorem isEntry_append {form : Prenex} (atomic : form.Atomic block.toBlock) {first second : List Nat}
    (nodup : (first ++ second).Nodup) (inside : ∀ place ∈ first ++ second, place < form.components.length)
    (apart : ∀ a ∈ first, ∀ b ∈ second, ¬ Linked.Shares (keysAt block form) a b) (pattern : Pattern) :
    IsEntry block form (first ++ second) pattern ↔ IsEntry block form first pattern ∨ IsEntry block form second pattern := by
  have firstNodup : first.Nodup := (List.nodup_append.mp nodup).1
  have secondNodup : second.Nodup := (List.nodup_append.mp nodup).2.1
  -- links from one side stay on that side
  have stays : ∀ {side : List Nat}, (∀ a ∈ side, ∀ b ∈ first ++ second, b ∉ side →
      ¬ Linked.Shares (keysAt block form) a b) → ∀ start ∈ side, ∀ target,
      Linked.LinkedIn (keysAt block form) (first ++ second) start target →
      target ∈ side ∧ Linked.LinkedIn (keysAt block form) side start target := by
    intro side closed start inStart target path
    induction path with
    | refl => exact ⟨inStart, Relation.ReflTransGen.refl⟩
    | @tail middle last _ step reached =>
        obtain ⟨inMiddle, inLast, shares⟩ := step
        obtain ⟨middleSide, toMiddle⟩ := reached
        by_cases lastSide : last ∈ side
        · exact ⟨lastSide, toMiddle.tail ⟨middleSide, lastSide, shares⟩⟩
        · exact absurd shares (closed _ middleSide _ inLast lastSide)
  have firstClosed : ∀ a ∈ first, ∀ b ∈ first ++ second, b ∉ first → ¬ Linked.Shares (keysAt block form) a b := by
    intro a inA b inB notFirst
    rcases List.mem_append.mp inB with inFirst | inSecond
    · exact absurd inFirst notFirst
    · exact apart a inA b inSecond
  have secondClosed : ∀ a ∈ second, ∀ b ∈ first ++ second, b ∉ second → ¬ Linked.Shares (keysAt block form) a b := by
    intro a inA b inB notSecond shares
    rcases List.mem_append.mp inB with inFirst | inSecond
    · exact apart b inFirst a inA shares.symm
    · exact notSecond inSecond
  have classSide : ∀ {side : List Nat}, side.Nodup → (∀ place ∈ side, place ∈ first ++ second) →
      (∀ a ∈ side, ∀ b ∈ first ++ second, b ∉ side → ¬ Linked.Shares (keysAt block form) a b) →
      ∀ place ∈ side, (classIn block form (first ++ second) place).Perm (classIn block form side place) := by
    intro side sideNodup sideIn closed place inSide
    rw [List.perm_ext_iff_of_nodup (classIn_nodup nodup place) (classIn_nodup sideNodup place)]
    intro other
    rw [mem_classIn, mem_classIn]
    constructor
    · rintro ⟨_, linked⟩
      exact stays closed place inSide other linked
    · rintro ⟨inOther, linked⟩
      exact ⟨sideIn other inOther, linked.mono sideIn⟩
  have classInside : ∀ place, ∀ other ∈ classIn block form (first ++ second) place, other < form.components.length :=
    fun _ other member => inside other (mem_classIn.mp member).1
  constructor
  · rintro ⟨place, inPlace, rfl⟩
    rcases List.mem_append.mp inPlace with inFirst | inSecond
    · exact .inl ⟨place, inFirst, (entryOf_perm fresh restrictFresh atomic (classInside place)
        (classSide firstNodup (fun _ member => List.mem_append_left _ member) firstClosed place inFirst)).symm⟩
    · exact .inr ⟨place, inSecond, (entryOf_perm fresh restrictFresh atomic (classInside place)
        (classSide secondNodup (fun _ member => List.mem_append_right _ member) secondClosed place inSecond)).symm⟩
  · rintro (⟨place, inFirst, rfl⟩ | ⟨place, inSecond, rfl⟩)
    · exact ⟨place, List.mem_append_left _ inFirst, entryOf_perm fresh restrictFresh atomic (classInside place)
        (classSide firstNodup (fun _ member => List.mem_append_left _ member) firstClosed place inFirst)⟩
    · exact ⟨place, List.mem_append_right _ inSecond, entryOf_perm fresh restrictFresh atomic (classInside place)
        (classSide secondNodup (fun _ member => List.mem_append_right _ member) secondClosed place inSecond)⟩

/-- **The replicated molecules of blocks side by side are those of either.** -/
theorem mem_replicatedOf_par {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock) (pattern : Pattern) :
    pattern ∈ replicatedOf block (canonicalOf block) (first.par second) ↔
      pattern ∈ replicatedOf block (canonicalOf block) first ∨ pattern ∈ replicatedOf block (canonicalOf block) second := by
  obtain ⟨a, firstComponents⟩ := first
  obtain ⟨b, secondComponents⟩ := second
  have parAtomic := par_atomic (block := block) (first := ⟨a, firstComponents⟩) firstAtomic secondAtomic
  rw [mem_replicatedOf_iff multisetFresh fresh restrictFresh parAtomic,
    mem_replicatedOf_iff multisetFresh fresh restrictFresh firstAtomic,
    mem_replicatedOf_iff multisetFresh fresh restrictFresh secondAtomic]
  set par := (Prenex.mk a firstComponents).par ⟨b, secondComponents⟩ with parIs
  have parComponents : par.components = firstComponents.map (liftBVars 0 b) ++
      secondComponents.map (liftBVars b a) := rfl
  have parCount : par.count = a + b := rfl
  have lengthIs : par.components.length = firstComponents.length + secondComponents.length := by
    rw [parComponents]
    simp
  set left := List.range firstComponents.length with leftIs
  set right := (List.range secondComponents.length).map (firstComponents.length + ·) with rightIs
  have splitNodup : (left ++ right).Nodup := by
    refine List.nodup_append.mpr ⟨List.nodup_range, List.nodup_range.map fun x y same => by omega, ?_⟩
    intro x inLeft y inRight same
    obtain ⟨offset, _, rfl⟩ := List.mem_map.mp inRight
    have := List.mem_range.mp inLeft
    omega
  have splitInside : ∀ place ∈ left ++ right, place < par.components.length := by
    intro place member
    rw [lengthIs]
    rcases List.mem_append.mp member with inLeft | inRight
    · have := List.mem_range.mp inLeft
      omega
    · obtain ⟨offset, below, rfl⟩ := List.mem_map.mp inRight
      have := List.mem_range.mp below
      omega
  -- the places side by side are the first block's then the second's
  rw [isEntry_of_mem_iff fresh restrictFresh parAtomic (live' := left ++ right) (places_nodup par) splitNodup
    (fun place member => by simpa [places] using member)
    (fun place => by
      simp only [places, List.mem_range, lengthIs, leftIs, rightIs, List.mem_append, List.mem_map]
      constructor
      · intro below
        by_cases low : place < firstComponents.length
        · exact .inl low
        · exact .inr ⟨place - firstComponents.length, by omega, by omega⟩
      · rintro (low | ⟨offset, below, rfl⟩) <;> omega) pattern]
  -- the values at the places
  have leftValue : ∀ place, place < firstComponents.length →
      placeValue block par.components place = liftBVars 0 b (placeValue block firstComponents place) := by
    intro place below
    rw [parComponents, placeValue_append_left (by simpa using below)]
    unfold placeValue
    rw [List.getD_eq_getElem _ _ (by simpa using below), List.getD_eq_getElem _ _ below, List.getElem_map]
  have rightValue : ∀ offset, offset < secondComponents.length →
      placeValue block par.components (firstComponents.length + offset) =
        liftBVars b a (placeValue block secondComponents offset) := by
    intro offset below
    have shifted : firstComponents.length = (firstComponents.map (liftBVars 0 b)).length := by simp
    rw [parComponents, shifted, placeValue_append_right (by simpa using below)]
    unfold placeValue
    rw [List.getD_eq_getElem _ _ (by simpa using below), List.getD_eq_getElem _ _ below, List.getElem_map]
  have leftKeys : ∀ place, place < firstComponents.length → ∀ restriction,
      restriction ∈ keysAt block par place ↔ ∃ original ∈ keysAt block ⟨a, firstComponents⟩ place,
        original + b = restriction := by
    intro place below restriction
    simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range, parCount, leftValue place below,
      mentions_iff, liftBVars_eq_rename, freeIn_rename]
    constructor
    · rintro ⟨inRange, original, free, rfl⟩
      simp only [shiftAbove, Nat.not_lt_zero, if_false] at inRange ⊢
      exact ⟨original, ⟨by omega, free⟩, rfl⟩
    · rintro ⟨original, ⟨low, free⟩, rfl⟩
      exact ⟨by omega, original, free, by simp [shiftAbove]⟩
  have rightKeys : ∀ offset, offset < secondComponents.length → ∀ restriction,
      restriction ∈ keysAt block par (firstComponents.length + offset) ↔
        restriction ∈ keysAt block ⟨b, secondComponents⟩ offset := by
    intro offset below restriction
    simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range, parCount, rightValue offset below,
      mentions_iff, liftBVars_eq_rename, freeIn_rename]
    constructor
    · rintro ⟨inRange, original, free, rfl⟩
      simp only [shiftAbove] at inRange ⊢
      split_ifs at inRange ⊢ with low
      · exact ⟨low, free⟩
      · omega
    · rintro ⟨low, free⟩
      exact ⟨by omega, restriction, free, by simp [shiftAbove, low]⟩
  rw [isEntry_append fresh restrictFresh parAtomic splitNodup splitInside (fun x inLeft y inRight shares => by
    obtain ⟨offset, below, rfl⟩ := List.mem_map.mp inRight
    obtain ⟨key, inX, inY⟩ := shares
    have xBelow := List.mem_range.mp inLeft
    obtain ⟨original, _, rfl⟩ := (leftKeys x xBelow key).mp inX
    have := (rightKeys offset (List.mem_range.mp below) _).mp inY
    simp only [keysAt, usedRestrictions, List.mem_filter, List.mem_range] at this
    omega) pattern]
  -- each side reads as its block, renamed
  have leftPreserving : Preserving a (a + b) (shiftAbove 0 b) := by
    refine ⟨fun x y same => ?_, fun index below => ?_, fun index above => ?_⟩ <;>
      simp only [shiftAbove, Nat.not_lt_zero, if_false] at * <;> omega
  have rightPreserving : Preserving b (a + b) (shiftAbove b a) := by
    refine ⟨fun x y same => ?_, fun index below => ?_, fun index above => ?_⟩ <;> simp only [shiftAbove] at *
    · split_ifs at same <;> omega
    · rw [if_pos below]; omega
    · rw [if_neg (by omega)]; omega
  have leftSide := isEntry_map (block := block) (form := ⟨a, firstComponents⟩) (form' := par)
    (live := places (Prenex.mk a firstComponents)) id (fun _ _ _ _ same => same)
    (fun x inX y inY => by
      have xBelow : x < firstComponents.length := by simpa [places] using inX
      have yBelow : y < firstComponents.length := by simpa [places] using inY
      constructor
      · rintro ⟨key, inXKeys, inYKeys⟩
        obtain ⟨original, inOriginal, rfl⟩ := (leftKeys x xBelow key).mp inXKeys
        obtain ⟨original', inOriginal', same⟩ := (leftKeys y yBelow _).mp inYKeys
        have equal : original' = original := by omega
        exact ⟨original, inOriginal, equal ▸ inOriginal'⟩
      · rintro ⟨key, inXKeys, inYKeys⟩
        exact ⟨key + b, (leftKeys x xBelow _).mpr ⟨key, inXKeys, rfl⟩, (leftKeys y yBelow _).mpr ⟨key, inYKeys, rfl⟩⟩)
    (fun group groupInside => by
      unfold entryOf restrictTo
      simp only [List.map_id]
      have renamed : group.map (placeValue block par.components) =
          (group.map (placeValue block firstComponents)).map (rename (shiftAbove 0 b)) := by
        rw [List.map_map]
        refine List.map_congr_left fun place member => ?_
        have below : place < firstComponents.length := by simpa [places] using groupInside place member
        rw [Function.comp_apply, leftValue place below, liftBVars_eq_rename]
      rw [renamed, parCount, normal_rename_eq fresh restrictFresh leftPreserving
        (fun index => by simp only [pruneRelabel, shiftAbove, Nat.not_lt_zero, if_false]; omega)
        (fun component member => by
          obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp member
          exact firstAtomic _ (placeValue_mem (by simpa [places] using groupInside place inGroup)))])
    pattern
  have rightSide := isEntry_map (block := block) (form := ⟨b, secondComponents⟩) (form' := par)
    (live := places (Prenex.mk b secondComponents)) (firstComponents.length + ·) (fun _ _ _ _ same => by omega)
    (fun x inX y inY => by
      have xBelow : x < secondComponents.length := by simpa [places] using inX
      have yBelow : y < secondComponents.length := by simpa [places] using inY
      simp only [Linked.Shares, rightKeys x xBelow, rightKeys y yBelow])
    (fun group groupInside => by
      unfold entryOf restrictTo
      have renamed : (group.map (firstComponents.length + ·)).map (placeValue block par.components) =
          (group.map (placeValue block secondComponents)).map (rename (shiftAbove b a)) := by
        rw [List.map_map, List.map_map]
        refine List.map_congr_left fun place member => ?_
        have below : place < secondComponents.length := by simpa [places] using groupInside place member
        rw [Function.comp_apply, Function.comp_apply, rightValue place below, liftBVars_eq_rename]
      rw [renamed, parCount, normal_rename_eq fresh restrictFresh rightPreserving
        (fun index => by
          simp only [pruneRelabel, shiftAbove]
          rw [if_neg (by omega)]
          omega)
        (fun component member => by
          obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp member
          exact secondAtomic _ (placeValue_mem (by simpa [places] using groupInside place inGroup)))])
    pattern
  have leftPlaces : (places (Prenex.mk a firstComponents)).map id = left := by simp [places, leftIs]
  have rightPlaces : (places (Prenex.mk b secondComponents)).map (firstComponents.length + ·) = right := by
    simp [places, rightIs]
  rw [leftPlaces] at leftSide
  rw [rightPlaces] at rightSide
  rw [leftSide, rightSide]

/-- **Blocks side by side have the replicated molecules of both.** -/
theorem normal_replicatedOf_par {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock) :
    normal block ⟨0, replicatedOf block (canonicalOf block) (first.par second)⟩ =
      normal block ⟨0, replicatedOf block (canonicalOf block) first ++ replicatedOf block (canonicalOf block) second⟩ :=
  normal_replicated_of_mem_iff fresh restrictFresh replicatedOf_replicated
    (fun component member => by
      rcases List.mem_append.mp member with inFirst | inSecond
      · exact replicatedOf_replicated component inFirst
      · exact replicatedOf_replicated component inSecond)
    (fun component => by
      rw [mem_replicatedOf_par multisetFresh fresh restrictFresh firstAtomic secondAtomic, List.mem_append])

omit multisetFresh fresh restrictFresh in
/-- Renaming the outside keeps which restrictions each place uses. -/
theorem keysAt_renameOuter (form : Prenex) (relabel : Nat → Nat) :
    keysAt block (form.renameOuter relabel) = keysAt block form := by
  funext place
  unfold keysAt Prenex.renameOuter
  simp only
  rw [placeValue_map_rename]
  unfold usedRestrictions
  apply List.filter_congr
  intro index member
  have below := List.mem_range.mp member
  apply Bool.eq_iff_iff.mpr
  rw [mentions_iff, mentions_iff, freeIn_rename]
  constructor
  · rintro ⟨original, free, maps⟩
    by_cases low : original < form.count
    · simp only [Mettapedia.OSLF.MeTTaIL.CanonicalBags.liftIndex, if_pos low] at maps
      rwa [← maps]
    · simp only [Mettapedia.OSLF.MeTTaIL.CanonicalBags.liftIndex, if_neg low] at maps
      omega
  · intro free
    exact ⟨index, free, by simp [Mettapedia.OSLF.MeTTaIL.CanonicalBags.liftIndex, below]⟩

/-- **Renaming the outside renames the replicated molecules**, each read again. -/
theorem replicatedOf_renameOuter {form : Prenex} (atomic : form.Atomic block.toBlock) {relabel : Nat → Nat}
    (injective : Function.Injective relabel) :
    replicatedOf block (canonicalOf block) (form.renameOuter relabel) =
      (replicatedOf block (canonicalOf block) form).map fun entry => recanon block (rename relabel entry) := by
  have renamedAtomic := renameOuter_atomic atomic relabel
  rw [replicatedOf_eq_entries multisetFresh fresh restrictFresh renamedAtomic,
    replicatedOf_eq_entries multisetFresh fresh restrictFresh atomic, keysAt_renameOuter, List.map_map]
  have placesSame : places (form.renameOuter relabel) = places form := by simp [places, Prenex.renameOuter]
  rw [placesSame]
  refine List.map_congr_left fun group member => ?_
  have grouping := Linked.build_grouping (keys := keysAt block form) (places form)
  have groupInside : ∀ place ∈ group, place < form.components.length := fun place inGroup => by
    have := grouping.mem_items member inGroup
    simpa [places] using this
  set restricted := restrictTo block form group with restrictedIs
  have restrictedAtomic : restricted.Atomic block.toBlock := by
    intro component inComponents
    obtain ⟨place, inGroup, rfl⟩ := List.mem_map.mp inComponents
    exact atomic _ (placeValue_mem (groupInside place inGroup))
  have renamedRestricted : restrictTo block (form.renameOuter relabel) group = restricted.renameOuter relabel := by
    simp only [restrictTo, restrictedIs, Prenex.renameOuter, List.map_map, Prenex.mk.injEq, true_and]
    exact List.map_congr_left fun place _ => placeValue_map_rename _ _ _
  simp only [Function.comp_apply]
  unfold entryOf
  rw [renamedRestricted, ← normal_renameOuter_normal fresh restrictFresh restrictedAtomic injective]
  have normalAtomic := normal_atomic fresh restrictFresh restrictedAtomic
  have normalUsed := used_normal fresh restrictFresh _ restrictedAtomic
  rw [← canonicalOf_toPattern (renameOuter_atomic normalAtomic _) (renameOuter_used normalUsed _), ← rename_toPattern]
  set canonical := Prenex.toPattern block.toBlock (normal block restricted) with canonicalIs
  have canonicalFixed : canonicalOf block canonical = canonical := by
    rw [canonicalIs, canonicalOf_toPattern normalAtomic normalUsed, normal_normal fresh restrictFresh restrictedAtomic]
  have partIs : ∀ argument, partOf block block.replicate argument = canonicalOf block argument := by
    intro argument
    unfold partOf
    rw [if_neg restrictFresh, if_neg multisetFresh]
  by_cases replicated : isReplicated block canonical = true
  · rw [bang_of_replicated replicated]
    have renamedAtom := replicated_atomic fresh restrictFresh (by rw [isReplicated_rename]; exact replicated)
      (component := rename relabel canonical)
    rw [canonicalOf_atom renamedAtom, bang_of_replicated (by rw [isReplicated_recanon, isReplicated_rename]; exact replicated)]
  · have notReplicated := Bool.eq_false_iff.mpr replicated
    rw [bang_of_not_replicated notReplicated, rename_apply, List.map_cons, List.map_nil, recanon_apply,
      List.map_cons, List.map_nil, partIs]
    refine bang_of_not_replicated ?_
    have shape := (below_all fresh restrictFresh (size canonical + 1)).shape canonical (Nat.lt_succ_self _) relabel
      injective
    rw [shape, canonicalFixed]
    exact notReplicated

/-- **A block of replicated molecules renamed outside reads as the replicated molecules of the renamed block.** -/
theorem normal_replicatedOf_renameOuter {form : Prenex} (atomic : form.Atomic block.toBlock) {relabel : Nat → Nat}
    (injective : Function.Injective relabel) :
    normal block ⟨0, replicatedOf block (canonicalOf block) (form.renameOuter relabel)⟩ =
      normal block ((Prenex.mk 0 (replicatedOf block (canonicalOf block) form)).renameOuter relabel) := by
  rw [replicatedOf_renameOuter multisetFresh fresh restrictFresh atomic injective]
  set entries := replicatedOf block (canonicalOf block) form with entriesIs
  have entriesReplicated : ∀ entry ∈ entries, isReplicated block entry = true := fun entry member =>
    replicatedOf_replicated entry member
  have renamedIs : (Prenex.mk 0 entries).renameOuter relabel = ⟨0, entries.map (rename relabel)⟩ := by
    simp only [Prenex.renameOuter, Prenex.mk.injEq, true_and]
    rw [liftIndex_zero]
  rw [renamedIs]
  symm
  refine normal_similar_all fresh restrictFresh ⟨rfl, [], _, List.Perm.refl _, ?_, List.Perm.refl _⟩ ?_ ?_
  · show List.Forall₂ (AlikeR block) ((entries.map (rename relabel)).map (rename (Prenex.permute 0 []))) _
    have identity : Prenex.permute 0 [] = id := permute_range 0
    rw [identity, show rename id = (id : Pattern → Pattern) from funext rename_id, List.map_id]
    show List.Forall₂ (AlikeR block) (entries.map (rename relabel))
      (entries.map fun entry => recanon block (rename relabel entry))
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun entry _ => alike_recanon_all fresh restrictFresh _
  · intro component member
    obtain ⟨entry, inEntries, rfl⟩ := List.mem_map.mp member
    exact replicated_atomic fresh restrictFresh (by rw [isReplicated_rename]; exact entriesReplicated entry inEntries)
  · intro component member
    obtain ⟨entry, inEntries, rfl⟩ := List.mem_map.mp member
    exact replicated_atomic fresh restrictFresh (by
      rw [isReplicated_recanon, isReplicated_rename]
      exact entriesReplicated entry inEntries)

/-- **The replicated molecules of canonical replications side by side are those replications.** -/
theorem mem_replicatedOf_replications {components : List Pattern}
    (replicated : ∀ component ∈ components, isReplicated block component = true)
    (canonical : ∀ component ∈ components, recanon block component = component) (pattern : Pattern) :
    pattern ∈ replicatedOf block (canonicalOf block) ⟨0, components⟩ ↔ pattern ∈ components := by
  have atomic : (Prenex.mk 0 components).Atomic block.toBlock := fun component member =>
    replicated_atomic fresh restrictFresh (replicated component member)
  rw [mem_replicatedOf_iff multisetFresh fresh restrictFresh atomic]
  have keysNil : ∀ place, keysAt block ⟨0, components⟩ place = [] := by
    intro place
    simp [keysAt, usedRestrictions]
  constructor
  · rintro ⟨place, inPlaces, rfl⟩
    have below : place < components.length := by simpa [places] using inPlaces
    rw [classIn_of_keys_nil (places_nodup _) inPlaces (keysNil place)]
    have valueIs : placeValue block components place = components[place] := List.getD_eq_getElem _ _ below
    have member := List.getElem_mem below
    unfold entryOf restrictTo
    simp only [List.map_cons, List.map_nil, valueIs]
    have atom := atomic _ member
    have canonicalIs : Prenex.toPattern block.toBlock (normal block ⟨0, [components[place]]⟩) =
        canonicalOf block components[place] := by
      unfold canonicalOf
      rw [atom]
      rfl
    rw [canonicalIs, canonicalOf_atom atom, canonical _ member, bang_of_replicated (replicated _ member)]
    exact member
  · intro member
    obtain ⟨place, below, rfl⟩ := List.getElem_of_mem member
    have inPlaces : place ∈ places (Prenex.mk 0 components) := by simp [places, below]
    refine ⟨place, inPlaces, ?_⟩
    rw [classIn_of_keys_nil (places_nodup _) inPlaces (keysNil place)]
    have valueIs : placeValue block components place = components[place] := List.getD_eq_getElem _ _ below
    unfold entryOf restrictTo
    simp only [List.map_cons, List.map_nil, valueIs]
    have atom := atomic _ member
    have canonicalIs : Prenex.toPattern block.toBlock (normal block ⟨0, [components[place]]⟩) =
        canonicalOf block components[place] := by
      unfold canonicalOf
      rw [atom]
      rfl
    rw [canonicalIs, canonicalOf_atom atom, canonical _ member, bang_of_replicated (replicated _ member)]

end Molecules

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
