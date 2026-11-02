import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationExposure

/-!
# Aligning canonical forms of blocks

Three facts that let canonical forms of blocks be compared in a larger frame:

- **A renaming of the outside injective on the names a block uses** reads a canonical block as it reads the block
  (`normal_renameOuter_normal_on`): only the names a block uses matter, and there the renaming agrees with an
  injective one.
- **Closing names keeps equal canonical forms equal** (`normal_add_congr`): a block reads the names it closes only
  through its canonical form.
- **The block of a copy group has the canonical form of the replicated argument** (`normal_groupBlock`), the
  group's own restrictions innermost and the block's others next, as the copy test reads it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)

variable {block : ReplicationBlock}

/-! ## Renaming the outside on the names a block uses -/

section Rename

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **A renaming of the outside injective on the names a block uses past its restrictions** reads the canonical block
as it reads the block. -/
theorem normal_renameOuter_normal_on {form : Prenex} (atomic : form.Atomic block.toBlock) {relabel : Nat → Nat}
    (injectiveOn : ∀ first second, form.FreePast first → form.FreePast second → relabel first = relabel second →
      first = second) :
    normal block ((normal block form).renameOuter relabel) = normal block (form.renameOuter relabel) := by
  classical
  obtain ⟨bound, bounded⟩ := exists_bound_of_list (fun pattern bound => ∀ index, FreeIn index pattern → index < bound)
    (fun _ _ _ le holds index free => lt_of_lt_of_le (holds index free) le) form.components
    fun pattern _ => exists_freeBound pattern
  have inside : ∀ index, form.FreePast index → index < bound := by
    rintro index ⟨component, member, free⟩
    have := bounded component member _ free
    omega
  obtain ⟨relabel', injective, agrees'⟩ := exists_injective_agree relabel bound form.FreePast
    fun first second _ firstIn _ secondIn same => injectiveOn first second firstIn secondIn same
  have agrees : ∀ index, form.FreePast index → relabel' index = relabel index := fun index past =>
    agrees' index (inside index past) past
  have renamedSame : ∀ form' : Prenex, (∀ index, form'.FreePast index → form.FreePast index) →
      form'.renameOuter relabel = form'.renameOuter relabel' := by
    intro form' freeImplies
    obtain ⟨count, components⟩ := form'
    simp only [Prenex.renameOuter, Prenex.mk.injEq, true_and]
    refine List.map_congr_left fun component member => rename_congr component fun index free => ?_
    simp only [liftIndex]
    split_ifs with low
    · rfl
    · have past : (Prenex.mk count components).FreePast (index - count) :=
        ⟨component, member, by rw [show index - count + count = index by omega]; exact free⟩
      rw [agrees _ (freeImplies _ past)]
  have normalAtomic := normal_atomic fresh restrictFresh atomic
  rw [renamedSame _ fun index past => (freePast_normal_all fresh restrictFresh atomic index).mp past,
    renamedSame _ fun _ past => past]
  exact normal_renameOuter_normal fresh restrictFresh atomic injective

/-! ## Closing names around blocks -/

/-- **One more restriction around a block** is closing the first name outside it. -/
theorem normal_succ {count : Nat} {components : List Pattern} (atomic : (Prenex.mk count components).Atomic block.toBlock) :
    normal block ⟨count + 1, components⟩ = normal block (Prenex.mk count components).close := by
  cases used : components.any (mentions count) with
  | true =>
      rw [close_of_used used]
      rfl
  | false =>
      rw [close_of_unused used]
      have notCount : ∀ index ∈ usedOf ⟨count + 1, components⟩, index < count := by
        intro index member
        obtain ⟨inside, mentionedAny⟩ := List.mem_filter.mp member
        have below : index < count + 1 := List.mem_range.mp inside
        by_contra notBelow
        have same : index = count := by omega
        subst same
        rw [mentionedAny] at used
        exact absurd used (by decide)
      refine (normal_rename_used fresh restrictFresh (count := count + 1) atomic ?_ ?_ ?_).symm
      · intro first inFirst second inSecond same
        have firstBelow := notCount first inFirst
        have secondBelow := notCount second inSecond
        simpa [dropIndex, firstBelow, secondBelow] using same
      · intro index member
        have below := notCount index member
        simp only [dropIndex, if_pos below]
        exact below
      · intro index
        simp only [dropIndex]
        rw [if_neg (by omega)]
        omega

/-- **Closing names around a block reads it only through its canonical form.** -/
theorem normal_add_normal {form : Prenex} (atomic : form.Atomic block.toBlock) : ∀ extra : Nat,
    normal block ⟨form.count + extra, form.components⟩ =
      normal block ⟨(normal block form).count + extra, (normal block form).components⟩
  | 0 => (normal_normal fresh restrictFresh atomic).symm
  | extra + 1 => by
      have normalAtomic := normal_atomic fresh restrictFresh atomic
      have extendedAtomic : (Prenex.mk (form.count + extra) form.components).Atomic block.toBlock := atomic
      have normalExtendedAtomic :
          (Prenex.mk ((normal block form).count + extra) (normal block form).components).Atomic block.toBlock :=
        normalAtomic
      calc normal block ⟨form.count + (extra + 1), form.components⟩
          = normal block (Prenex.mk (form.count + extra) form.components).close :=
            normal_succ fresh restrictFresh extendedAtomic
        _ = normal block (normal block ⟨form.count + extra, form.components⟩).close :=
            (normal_close_normal fresh restrictFresh extendedAtomic).symm
        _ = normal block (normal block ⟨(normal block form).count + extra, (normal block form).components⟩).close := by
            rw [normal_add_normal atomic extra]
        _ = normal block (Prenex.mk ((normal block form).count + extra) (normal block form).components).close :=
            normal_close_normal fresh restrictFresh normalExtendedAtomic
        _ = normal block ⟨(normal block form).count + (extra + 1), (normal block form).components⟩ :=
            (normal_succ fresh restrictFresh normalExtendedAtomic).symm

/-- **Blocks with one canonical form keep one when names outside them are closed.** -/
theorem normal_add_congr {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock) (same : normal block first = normal block second) (extra : Nat) :
    normal block ⟨first.count + extra, first.components⟩ = normal block ⟨second.count + extra, second.components⟩ := by
  rw [normal_add_normal fresh restrictFresh firstAtomic, normal_add_normal fresh restrictFresh secondAtomic, same]

end Rename

/-! ## The block of a copy group -/

/-- **The restrictions a group owns**: those it uses that its replicated component does not. -/
def ownOf (block : ReplicationBlock) (form : Prenex) (p : Nat) (group : Finset Nat) : List Nat :=
  restrictionsOf (allowedFor form.count (placeValue block form.components p)) form.count
    (placeValue block form.components) (group.sort (· ≤ ·))

/-- **The block of a copy group**: its components, its own restrictions innermost in their order, the block's other
restrictions next in theirs, the names outside past them. -/
def groupBlock (block : ReplicationBlock) (form : Prenex) (p : Nat) (group : Finset Nat) : Prenex :=
  copyBlock form.count (ownOf block form p group) ((group.sort (· ≤ ·)).map (placeValue block form.components))

section CopyBlock

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **The block of a copy group has the canonical form of the replicated argument**, the argument read with the
block's other restrictions in their order and the names outside past them. -/
theorem normal_groupBlock {form : Prenex} (atomic : form.Atomic block.toBlock) {live : Finset Nat}
    (inside : live ⊆ (places form).toFinset) {p : Nat} {group : Finset Nat}
    (isCopy : (blockSystem block form).IsCopy live p group) :
    normal block (groupBlock block form p group) =
      normal block (decompose block.toBlock (rename (Prenex.groupIndex form.count
        (outsideOf form.count (ownOf block form p group))) (argumentOf? (placeValue block form.components p)))) := by
  have test : CopyTest block (canonicalOf block) form.count (placeValue block form.components p)
      (asGroup (allowedFor form.count (placeValue block form.components p)) form.count
        (placeValue block form.components) (group.sort (· ≤ ·))) := isCopy.isCopy
  obtain ⟨same, -, -, -⟩ := test
  rw [copyOf_eq_copyBlock] at same
  have groupInside : ∀ place ∈ group, place < form.components.length := fun place member => by
    have := inside (Finset.mem_erase.mp (isCopy.isGroup.subset member)).2
    simpa [places] using this
  have copyAtomic : (groupBlock block form p group).Atomic block.toBlock := by
    intro component member
    simp only [groupBlock, copyBlock, List.map_map, List.mem_map] at member
    obtain ⟨place, inSorted, rfl⟩ := member
    exact atomic_rename (atomic _ (placeValue_mem (groupInside place ((Finset.mem_sort _).mp inSorted)))) _
  have copyUsed : (groupBlock block form p group).Used := copyBlock_used
  have blockIs : copyBlock form.count (asGroup (allowedFor form.count (placeValue block form.components p)) form.count
      (placeValue block form.components) (group.sort (· ≤ ·))).restrictions
      (asGroup (allowedFor form.count (placeValue block form.components p)) form.count
        (placeValue block form.components) (group.sort (· ≤ ·))).components = groupBlock block form p group := rfl
  have restrictionsIs : (asGroup (allowedFor form.count (placeValue block form.components p)) form.count
      (placeValue block form.components) (group.sort (· ≤ ·))).restrictions = ownOf block form p group := rfl
  rw [blockIs, restrictionsIs, canonicalOf_toPattern copyAtomic copyUsed] at same
  unfold canonicalOf at same
  exact toPattern_injective (normal_atomic fresh restrictFresh copyAtomic)
    (normal_atomic fresh restrictFresh (decompose_atomic _)) same

end CopyBlock

/-! ## Blocks inside blocks -/

section Inside

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

omit fresh restrictFresh in
/-- A block inside a block is a block beside the outer block's components, closed by its restrictions. -/
theorem unfoldWith_eq_closed (form copy : Prenex) :
    form.unfoldWith copy = ⟨((Prenex.mk 0 form.components).par copy).count + form.count,
      ((Prenex.mk 0 form.components).par copy).components⟩ := by
  obtain ⟨count, components⟩ := form
  obtain ⟨copies, copyComponents⟩ := copy
  simp only [Prenex.unfoldWith, Prenex.par, Nat.zero_add, Prenex.mk.injEq, true_and]
  congr 1
  conv_lhs => rw [← List.map_id copyComponents]
  refine List.map_congr_left fun component _ => ?_
  exact (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero _ _).symm

/-- **A block inside a block is read through its canonical form.** -/
theorem normal_unfoldWith_normal {form copy : Prenex} (formAtomic : form.Atomic block.toBlock)
    (copyAtomic : copy.Atomic block.toBlock) :
    normal block (form.unfoldWith (normal block copy)) = normal block (form.unfoldWith copy) := by
  have outerAtomic : (Prenex.mk 0 form.components).Atomic block.toBlock := formAtomic
  rw [unfoldWith_eq_closed, unfoldWith_eq_closed]
  have inner := normal_par_normal_right fresh restrictFresh outerAtomic copyAtomic
  exact normal_add_congr fresh restrictFresh (par_atomic outerAtomic (normal_atomic fresh restrictFresh copyAtomic))
    (par_atomic outerAtomic copyAtomic) inner form.count

/-- **Blocks inside a block with one canonical form give one canonical form.** -/
theorem normal_unfoldWith_congr {form first second : Prenex} (formAtomic : form.Atomic block.toBlock)
    (firstAtomic : first.Atomic block.toBlock) (secondAtomic : second.Atomic block.toBlock)
    (same : normal block first = normal block second) :
    normal block (form.unfoldWith first) = normal block (form.unfoldWith second) := by
  rw [← normal_unfoldWith_normal fresh restrictFresh formAtomic firstAtomic, same,
    normal_unfoldWith_normal fresh restrictFresh formAtomic secondAtomic]

/-- **An alignment for contexts of components carries to contexts that are blocks**: a block inside the block reads
as it reads, renamed outside, inside the aligned block. Its own restrictions are read as names past every name used,
moved back and closed again. -/
theorem align_inside {count unfolded : Nat} {others rest : List Pattern} {relabel : Nat → Nat}
    {attached : Nat → Prop}
    (othersAtomic : ∀ component ∈ others, decompose block.toBlock component = Prenex.atom component)
    (restAtomic : ∀ component ∈ rest, decompose block.toBlock component = Prenex.atom component)
    (outer : ∀ index, relabel (count + index) = unfolded + index)
    (below : ∀ index < count, attached index → relabel index < unfolded)
    (aligned : ∀ context : List Pattern, (∀ component ∈ context, decompose block.toBlock component = Prenex.atom component) →
      (∀ component ∈ context, ∀ index < count, mentions index component = true → attached index) →
      normal block ⟨count, others ++ context⟩ = normal block ⟨unfolded, rest ++ context.map (rename relabel)⟩)
    {copy : Prenex} (copyAtomic : copy.Atomic block.toBlock)
    (copyAttached : ∀ component ∈ copy.components, ∀ index < count,
      mentions (copy.count + index) component = true → attached index) :
    normal block ((Prenex.mk count others).unfoldWith copy) =
      normal block ((Prenex.mk unfolded rest).unfoldWith (copy.renameOuter relabel)) := by
  classical
  obtain ⟨copies, copyComponents⟩ := copy
  simp only at copyAtomic copyAttached
  -- a bound past every name used
  obtain ⟨bound, bounded⟩ := exists_bound_of_list (fun pattern bound => ∀ index, FreeIn index pattern → index < bound)
    (fun _ _ _ le holds index free => lt_of_lt_of_le (holds index free) le)
    (others ++ rest ++ copyComponents) fun pattern _ => exists_freeBound pattern
  have boundOthers : ∀ component ∈ others, ∀ index, FreeIn index component → index < bound :=
    fun component member => bounded component (by simp [member])
  have boundRest : ∀ component ∈ rest, ∀ index, FreeIn index component → index < bound :=
    fun component member => bounded component (by simp [member])
  have boundCopy : ∀ component ∈ copyComponents, ∀ index, FreeIn index component → index < bound :=
    fun component member => bounded component (by simp [member])
  -- the copy's own restrictions as names past every name used
  set high : Nat → Nat := fun index => if index < copies then count + bound + index else index - copies with highIs
  set close : Nat → Nat := fun index =>
    if index < bound then copies + index else if index < bound + copies then index - bound else index with closeIs
  have closeInjective : Function.Injective close := by
    intro first second same
    simp only [closeIs] at same
    split_ifs at same <;> omega
  set context := copyComponents.map (rename high) with contextIs
  have contextAtomic : ∀ component ∈ context, decompose block.toBlock component = Prenex.atom component := by
    intro component member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    exact atomic_rename (copyAtomic original inOriginal) high
  have contextAttached : ∀ component ∈ context, ∀ index < count, mentions index component = true → attached index := by
    intro component member index below' mentioned
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    rw [mentions_iff, freeIn_rename] at mentioned
    obtain ⟨name, free, maps⟩ := mentioned
    simp only [highIs] at maps
    split_ifs at maps with own
    · omega
    · refine copyAttached original inOriginal index below' ?_
      rw [mentions_iff, show copies + index = name by omega]
      exact free
  have alignedContext := aligned context contextAtomic contextAttached
  have atomicAppend : ∀ first second : List Pattern,
      (∀ component ∈ first, decompose block.toBlock component = Prenex.atom component) →
      (∀ component ∈ second, decompose block.toBlock component = Prenex.atom component) →
      ∀ component ∈ first ++ second, decompose block.toBlock component = Prenex.atom component := by
    intro first second firstAtomic secondAtomic component member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact firstAtomic component inFirst
    · exact secondAtomic component inSecond
  have firstAtomic : (Prenex.mk count (others ++ context)).Atomic block.toBlock :=
    atomicAppend _ _ othersAtomic contextAtomic
  have secondAtomic : (Prenex.mk unfolded (rest ++ context.map (rename relabel))).Atomic block.toBlock := by
    refine atomicAppend _ _ restAtomic fun component member => ?_
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    exact atomic_rename (contextAtomic original inOriginal) relabel
  -- moved first and closed again
  have movedEq : normal block ((Prenex.mk count (others ++ context)).renameOuter close) =
      normal block ((Prenex.mk unfolded (rest ++ context.map (rename relabel))).renameOuter close) := by
    rw [← normal_renameOuter_normal fresh restrictFresh firstAtomic closeInjective, alignedContext,
      normal_renameOuter_normal fresh restrictFresh secondAtomic closeInjective]
  have closedEq := normal_add_congr fresh restrictFresh (renameOuter_atomic firstAtomic close)
    (renameOuter_atomic secondAtomic close) movedEq copies
  -- the copy's restrictions innermost again
  set swapFirst : Nat → Nat := fun index =>
    if index < count then copies + index else if index < count + copies then index - count else index with swapFirstIs
  set swapSecond : Nat → Nat := fun index =>
    if index < unfolded then copies + index else if index < unfolded + copies then index - unfolded else index
    with swapSecondIs
  have swapAtomicFirst : (Prenex.mk (count + copies)
      ((Prenex.mk count (others ++ context)).renameOuter close).components).Atomic block.toBlock :=
    renameOuter_atomic firstAtomic close
  have swapAtomicSecond : (Prenex.mk (unfolded + copies)
      ((Prenex.mk unfolded (rest ++ context.map (rename relabel))).renameOuter close).components).Atomic
        block.toBlock :=
    renameOuter_atomic secondAtomic close
  have firstComponents : ((Prenex.mk count (others ++ context)).renameOuter close).components.map
      (rename swapFirst) = ((Prenex.mk count others).unfoldWith ⟨copies, copyComponents⟩).components := by
    simp only [Prenex.unfoldWith, Prenex.renameOuter, List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun component member => ?_
      simp only [Function.comp_apply, rename_comp, liftBVars_eq_rename]
      apply rename_congr
      intro index free
      have := boundOthers component member index free
      simp only [Function.comp_apply, swapFirstIs, liftIndex, closeIs, shiftAbove, Nat.not_lt_zero, if_false]
      split_ifs <;> omega
    · rw [contextIs, List.map_map]
      conv_rhs => rw [← List.map_id copyComponents]
      refine List.map_congr_left fun component member => ?_
      simp only [Function.comp_apply, rename_comp]
      have identity : rename (swapFirst ∘ liftIndex count close ∘ high) component = rename id component := by
        apply rename_congr
        intro index free
        have := boundCopy component member index free
        simp only [Function.comp_apply, swapFirstIs, liftIndex, closeIs, highIs, id]
        split_ifs <;> omega
      rw [identity, rename_id]
      rfl
  have firstSwapped : normal block ⟨count + copies,
      ((Prenex.mk count (others ++ context)).renameOuter close).components⟩ =
      normal block ((Prenex.mk count others).unfoldWith ⟨copies, copyComponents⟩) := by
    rw [← normal_rename_used fresh restrictFresh (count' := copies + count) (relabel := swapFirst) swapAtomicFirst
      (fun a inA b inB same => by
        have aBelow : a < count + copies := List.mem_range.mp (List.mem_filter.mp inA).1
        have bBelow : b < count + copies := List.mem_range.mp (List.mem_filter.mp inB).1
        simp only [swapFirstIs] at same
        split_ifs at same <;> omega)
      (fun index member => by
        have below' : index < count + copies := List.mem_range.mp (List.mem_filter.mp member).1
        simp only [swapFirstIs]
        split_ifs <;> omega)
      (fun index => by
        simp only [swapFirstIs]
        split_ifs <;> omega), firstComponents]
    rfl
  have secondComponents : ((Prenex.mk unfolded (rest ++ context.map (rename relabel))).renameOuter close).components.map
      (rename swapSecond) =
      ((Prenex.mk unfolded rest).unfoldWith ((Prenex.mk copies copyComponents).renameOuter relabel)).components := by
    simp only [Prenex.unfoldWith, Prenex.renameOuter, List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun component member => ?_
      simp only [Function.comp_apply, rename_comp, liftBVars_eq_rename]
      apply rename_congr
      intro index free
      have := boundRest component member index free
      simp only [Function.comp_apply, swapSecondIs, liftIndex, closeIs, shiftAbove, Nat.not_lt_zero, if_false]
      split_ifs <;> omega
    · rw [contextIs, List.map_map]
      refine List.map_congr_left fun component member => ?_
      simp only [Function.comp_apply, rename_comp]
      apply rename_congr
      intro index free
      have := boundCopy component member index free
      simp only [Function.comp_apply, highIs, liftIndex]
      by_cases own : index < copies
      · rw [if_pos own, show count + bound + index = count + (bound + index) by omega, outer]
        simp only [swapSecondIs, closeIs]
        split_ifs <;> omega
      · rw [if_neg own, if_neg own]
        by_cases inside : index - copies < count
        · have small := below (index - copies) inside (copyAttached component member (index - copies) inside (by
            rw [mentions_iff, show copies + (index - copies) = index by omega]
            exact free))
          simp only [swapSecondIs]
          split_ifs
          omega
        · rw [show index - copies = count + (index - copies - count) by omega, outer]
          simp only [swapSecondIs, closeIs]
          split_ifs <;> omega
  have secondSwapped : normal block ⟨unfolded + copies,
      ((Prenex.mk unfolded (rest ++ context.map (rename relabel))).renameOuter close).components⟩ =
      normal block ((Prenex.mk unfolded rest).unfoldWith ((Prenex.mk copies copyComponents).renameOuter relabel)) := by
    rw [← normal_rename_used fresh restrictFresh (count' := copies + unfolded) (relabel := swapSecond)
      swapAtomicSecond
      (fun a inA b inB same => by
        have aBelow : a < unfolded + copies := List.mem_range.mp (List.mem_filter.mp inA).1
        have bBelow : b < unfolded + copies := List.mem_range.mp (List.mem_filter.mp inB).1
        simp only [swapSecondIs] at same
        split_ifs at same <;> omega)
      (fun index member => by
        have below' : index < unfolded + copies := List.mem_range.mp (List.mem_filter.mp member).1
        simp only [swapSecondIs]
        split_ifs <;> omega)
      (fun index => by
        simp only [swapSecondIs]
        split_ifs <;> omega), secondComponents]
    rfl
  rw [← firstSwapped, ← secondSwapped]
  exact closedEq

end Inside

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
