import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.AbsorbSystem
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSimilar
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationCanonSound

/-!
# The canonical form of a block, by its copies

A block's components, by their places, form an absorption system for the canonical form (`blockSystem`); the height
of a replicated component is the size of its argument's canonical form. Three laws of the copy predicate hold by the
copy test itself: a copy mentions what its replicated component mentions, a lone replication is never a copy (its
canonical form is a replication), and a replication inside a copy has a smaller canonical argument
(`blockLaws`). The fourth, that absorbing a copy inside a group keeps the group a copy or not, is what the canonical
form must give on lighter patterns.

Under the laws, normalizing a block keeps exactly the places outside every copy group (`normal_copies`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {block : ReplicationBlock}

/-- **The absorption system of a block** for the canonical form: a replicated component is as high as its
argument's canonical form is large. -/
def blockSystem (block : ReplicationBlock) (form : Prenex) : CopyGroups.System Nat :=
  absorptionSystem block (canonicalOf block) form.count form.components
    (fun place => size (canonicalOf block (argumentOf? (placeValue block form.components place))))

/-- The places of a block's components. -/
def places (form : Prenex) : List Nat := List.range form.components.length

theorem places_nodup (form : Prenex) : (places form).Nodup := List.nodup_range

theorem places_inRange (form : Prenex) : ∀ place ∈ places form, place < form.components.length :=
  fun _ member => List.mem_range.mp member

/-- A block is its places read as components. -/
theorem places_map (form : Prenex) :
    (⟨form.count, (places form).map (placeValue block form.components)⟩ : Prenex) = form := by
  obtain ⟨count, components⟩ := form
  simp only [places, Prenex.mk.injEq, true_and]
  apply List.ext_getElem
  · simp
  · intro index inside _
    simp only [List.getElem_map, List.getElem_range, placeValue]
    exact List.getD_eq_getElem _ _ (by simpa using inside)

/-- **The canonical form of a single replicated component is a replication.** -/
theorem canonicalOf_replication (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) (argument : Pattern) :
    isReplicated block (canonicalOf block (.apply block.replicate [argument])) = true := by
  have isAtom : decompose block.toBlock (.apply block.replicate [argument]) =
      Prenex.atom (.apply block.replicate [argument]) := by
    apply decompose_atom
    · intro equal
      simp only [Pattern.apply.injEq] at equal
      exact absurd equal.2 (by simp)
    · intro binder body equal
      simp only [Pattern.apply.injEq] at equal
      exact restrictFresh equal.1
    · intro elements equal
      cases equal
    · intro label argument' equal
      simp only [Pattern.apply.injEq, List.cons.injEq, and_true] at equal
      rw [← equal.1]
      exact fresh
  have noCopy : ∀ canonical, absorbOnce block canonical ⟨0, [.apply block.replicate [argument]]⟩ = none := by
    intro canonical
    unfold absorbOnce
    simp [groupsThrough]
  have absorbed : absorb block (canonicalOf block) (Prenex.atom (.apply block.replicate [argument])) =
      Prenex.atom (.apply block.replicate [argument]) := by
    unfold absorb
    simp only [Prenex.atom, List.length_singleton, absorbRounds, noCopy, prune_zero]
  have identity : Prenex.permute 0 [] = id := permute_range 0
  unfold canonicalOf
  rw [normal_eq_reading, isAtom, absorbed]
  simp only [readingsR, Prenex.atom, readingOrders_zero, List.map_cons, List.map_nil, identity, rename_id,
    least, List.foldl_nil]
  have sorted : sortComponents [recanon block (.apply block.replicate [argument])] =
      [recanon block (.apply block.replicate [argument])] := rfl
  have single : dedupReplicated block [recanon block (.apply block.replicate [argument])] =
      [recanon block (.apply block.replicate [argument])] := by
    simp [dedupReplicated]
  simp only [sorted, single, Prenex.toPattern, Prenex.restricts, Prenex.body]
  unfold recanon
  rw [isReplicated_recanonWith]
  simp [isReplicated]

theorem mem_mentions {form : Prenex} {place restriction : Nat} :
    restriction ∈ (blockSystem block form).mentions place ↔
      restriction < form.count ∧ mentions restriction (placeValue block form.components place) = true := by
  simp [blockSystem, absorptionSystem, mem_usedRestrictions]

/-- The groups' components read in the order of their places. -/
theorem mem_sorted_components {form : Prenex} {allowed : List Nat} {group : Finset Nat} {member : Pattern} :
    member ∈ (asGroup allowed form.count (placeValue block form.components) (group.sort (· ≤ ·))).components ↔
      ∃ place ∈ group, placeValue block form.components place = member := by
  simp [asGroup]

/-- **The laws of a block's system**: three by the copy test, the fourth given. -/
theorem blockSystem_laws (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    (form : Prenex)
    (inner : ∀ live ⊆ (places form).toFinset, ∀ p group q outer, (blockSystem block form).IsCopy live p group →
      q ∈ live → (blockSystem block form).replicated q → (blockSystem block form).IsGroup live q outer → q ≠ p →
      group ⊆ outer → p ∈ outer →
      ((blockSystem block form).copy outer q ↔ (blockSystem block form).copy (outer \ group) q)) :
    (blockSystem block form).Laws (places form).toFinset := by
  refine ⟨?_, ?_, ?_, inner⟩
  · intro group _ p _ _ _ copied restriction mentioned
    obtain ⟨below, mentionedHere⟩ := mem_mentions.mp mentioned
    obtain ⟨member, inComponents, mentionedThere⟩ := copied.2.2.2 restriction below mentionedHere
    obtain ⟨place, inGroup, rfl⟩ := mem_sorted_components.mp inComponents
    exact ⟨place, inGroup, mem_mentions.mpr ⟨below, mentionedThere⟩⟩
  · intro q _ p _ _ qReplicated _ within copied
    have restrictionsEmpty : restrictionsOf (allowedFor form.count (placeValue block form.components p)) form.count
        (placeValue block form.components) (({q} : Finset Nat).sort (· ≤ ·)) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro restriction listed
      obtain ⟨item, inItem, keyed⟩ := mem_restrictionsOf.mp listed
      simp only [Finset.sort_singleton, List.mem_singleton] at inItem
      subst inItem
      unfold throughKeys at keyed
      obtain ⟨used, allowed⟩ := List.mem_filter.mp keyed
      obtain ⟨below, mentionedQ⟩ := mem_usedRestrictions.mp used
      have mentionedP := mem_mentions.mp (within (mem_mentions.mpr ⟨below, mentionedQ⟩))
      simp only [List.contains_iff_mem, allowedFor, List.mem_filter, List.mem_range, Bool.not_eq_true'] at allowed
      rw [mentionedP.2] at allowed
      cases allowed.2
    have notReplicated := copied.2.1
    obtain ⟨argument, isReplication⟩ := replicated_shape qReplicated
    have copyIs : copyOf block.toBlock form.count (asGroup (allowedFor form.count (placeValue block form.components p))
        form.count (placeValue block form.components) (({q} : Finset Nat).sort (· ≤ ·))) =
        .apply block.replicate [rename (Prenex.permute form.count (splitOrder form.count (outsideOf form.count [])
          [])) argument] := by
      unfold copyOf asGroup
      rw [restrictionsEmpty]
      simp only [Finset.sort_singleton, List.map_cons, List.map_nil, List.length_nil, Prenex.toPattern,
        Prenex.restricts, Prenex.body, isReplication, rename_apply]
    rw [copyIs, canonicalOf_replication fresh restrictFresh] at notReplicated
    cases notReplicated
  · intro group _ p _ _ q _ copied inGroup qReplicated
    exact copied.2.2.1 _ (mem_sorted_components.mpr ⟨q, inGroup, rfl⟩) qReplicated

/-- **Normalizing a block keeps the places outside every copy group**, under the laws of its system and a copy
test blind to the order of a group's places. -/
theorem normal_copies {form : Prenex} (laws : (blockSystem block form).Laws (places form).toFinset)
    (blind : BlindOn block (canonicalOf block) form.count form.components) :
    ∃ final : List Nat, final.Nodup ∧
      final.toFinset = (places form).toFinset \ (blockSystem block form).copies (places form).toFinset ∧
      normal block form = ⟨((Prenex.mk form.count (final.map (placeValue block form.components))).prune).count,
        least (readingsR block (Prenex.mk form.count (final.map (placeValue block form.components))).prune)⟩ := by
  obtain ⟨final, nodup, finalIs, absorbed⟩ := absorb_copies (height := fun place => size (canonicalOf block
    (argumentOf? (placeValue block form.components place)))) blind laws (places_nodup form) (places_inRange form)
  refine ⟨final, nodup, finalIs, ?_⟩
  rw [normal_eq_reading]
  conv_lhs => rw [← places_map (block := block) form]
  rw [absorbed]

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
