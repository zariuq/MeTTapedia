import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationStep

/-!
# Canonical forms keep free names

A copy group uses outside its block only names its replicated component uses (`freeIn_of_copy`): the copy test
equates their canonical forms, and canonical forms of lighter patterns keep free names. So absorbing copy groups
keeps every name the block uses past its restrictions (`absorbs_freeIn`), as do dropping unused restrictions
(`freePast_prune`) and reading the components again under an order (`freePast_reading`). Hence a canonical form
uses exactly the names of the pattern it reads (`freeIn_canonicalOf`), every restriction of a canonical block is
used (`used_normal`), and a canonical form decomposes into its canonical block (`decompose_canonicalOf`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_apply freeIn_lambda freeIn_multiLambda freeIn_collection)

variable {block : ReplicationBlock}

/-! ## At every size -/

/-- **The laws of every block of atoms**, and its copy test blind to orders. -/
theorem lawful_all (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {form : Prenex} (atomic : form.Atomic block.toBlock) :
    (blockSystem block form).Laws (places form).toFinset ∧ BlindOn block (canonicalOf block) form.count form.components :=
  (bundle_all fresh restrictFresh (form.mass + 1)).lawful form (Nat.lt_succ_self _) atomic

/-- **Canonical forms are read alike at every size.** -/
theorem below_all (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    (bound : Nat) : Below block bound :=
  (bundle_all fresh restrictFresh bound).below

/-- **Canonical blocks are blocks of atoms.** -/
theorem atomic_normal (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    (pattern : Pattern) : (normal block (decompose block.toBlock pattern)).Atomic block.toBlock :=
  (bundle_all fresh restrictFresh (size pattern + 1)).atomic pattern (Nat.lt_succ_self _)

/-- **A canonical form uses exactly the free names of the pattern it reads.** -/
theorem freeIn_canonicalOf (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    (pattern : Pattern) (index : Nat) : FreeIn index (canonicalOf block pattern) ↔ FreeIn index pattern := by
  suffices below : ∀ bound, ∀ pattern, size pattern < bound → ∀ index,
      FreeIn index (canonicalOf block pattern) ↔ FreeIn index pattern from
    below _ pattern (Nat.lt_succ_self _) index
  intro bound
  induction bound with
  | zero => exact fun _ small => absurd small (Nat.not_lt_zero _)
  | succ bound recurse =>
      intro pattern small index
      have heavy : (decompose block.toBlock pattern).mass ≤ bound :=
        (mass_decompose (block := block.toBlock) pattern).trans (by omega)
      have blind := (lawful_all fresh restrictFresh (decompose_atomic (base := block.toBlock) pattern)).2
      unfold canonicalOf
      rw [freeIn_toPattern, freeIn_decompose (block := block.toBlock) pattern index]
      exact freePast_normal heavy blind recurse index

/-! ## Canonical blocks use their restrictions -/

/-- **A pruned block uses every restriction it keeps.** -/
theorem used_prune (form : Prenex) : form.prune.Used := by
  rw [prune_eq]
  intro position below
  simp only at below
  have nodup : (usedOf form).Nodup := List.nodup_range.filter _
  have placed : (usedOf form).idxOf (usedOf form)[position] = position := nodup.idxOf_getElem _ below
  have member : (usedOf form)[position] ∈ usedOf form := List.getElem_mem below
  generalize (usedOf form)[position] = element at placed member
  simp only [usedOf, List.mem_filter, List.mem_range, List.any_eq_true] at member
  obtain ⟨inRange, component, inComponents, mentioned⟩ := member
  refine ⟨_, List.mem_map_of_mem inComponents, ?_⟩
  rw [mentions_iff, freeIn_rename]
  refine ⟨element, (mentions_iff _ _).mp mentioned, ?_⟩
  rw [groupIndex_below inRange]
  exact placed

/-- **A canonical block uses every restriction it keeps.** -/
theorem used_normal (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    (form : Prenex) (atomic : form.Atomic block.toBlock) : (normal block form).Used := by
  have blind := (lawful_all fresh restrictFresh atomic).2
  obtain ⟨final, _, _, absorbed⟩ := absorb_places blind
  have keptUsed := used_prune (Prenex.mk form.count (final.map (placeValue block form.components)))
  rw [normal_eq_reading, absorbed]
  generalize (Prenex.mk form.count (final.map (placeValue block form.components))).prune = kept at keptUsed ⊢
  obtain ⟨count, components⟩ := kept
  obtain ⟨order, inOrders, leastIs⟩ := least_reading_mem (block := block) (Prenex.mk count components)
  have isOrder : IsOrder count order := readingOrders_isOrder inOrders
  have reordered := used_permute keptUsed isOrder
  intro restriction below
  simp only at below
  obtain ⟨component, member, mentioned⟩ := reordered restriction below
  obtain ⟨original, inKept, rfl⟩ := List.mem_map.mp member
  refine ⟨_, ?_, (mentions_iff _ _).mpr ((freeIn_recanon (fun pattern _ index =>
    freeIn_canonicalOf fresh restrictFresh pattern index) _).mpr ((mentions_iff _ _).mp mentioned))⟩
  simp only
  rw [leastIs]
  exact mem_reading_iff.mpr ⟨original, inKept, rfl⟩

/-- **A canonical form decomposes into its canonical block.** -/
theorem decompose_canonicalOf (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) (pattern : Pattern) :
    decompose block.toBlock (canonicalOf block pattern) = normal block (decompose block.toBlock pattern) :=
  decompose_toPattern (atomic_normal fresh restrictFresh pattern)
    (used_normal fresh restrictFresh _ (decompose_atomic (base := block.toBlock) pattern))

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
