import Mettapedia.InformationTheory.RelationStoreEliasFano
import Mettapedia.InformationTheory.RelationStoreKolmogorov
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPlainComplexity
import Mettapedia.GSLT.Equations.OccurrenceRuns
import Mathlib.Data.Fin.Embedding

/-! # What a quotient posting actually has to encode

Knowing the ordered class tape is side information. If raw spelling is
also observable, each position still has to select an element of its class
fibre. In a fixed-width format the product of the fibre sizes gives an
exact capacity criterion. A shortest-program lower bound holds for some
such tapes even for an arbitrary fixed auxiliary condition.

Position lists are a separate problem. An Elias–Fano block stream preserves
the original increasing order at its checked bit budget. Bitmap and run
layouts fit other families. None of these bounds prices a live allocator,
a rank/select directory, or arbitrary equation edits.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.PostingInformation

open InformationTheory.RelationStoreFloors KolmogorovComplexity
open scoped BigOperators

variable {I S C : Type*}

abbrev FibreTape (q : S → C) (observed : I → C) :=
  (i : I) → {s : S // q s = observed i}

/-- The raw tape really is the family of independent fibres once the order
and the quotient tape are given (no distinctness constraint on raw labels). -/
def splitTape (q : S → C) (observed : I → C) :
    {raw : I → S // q ∘ raw = observed} ≃ FibreTape q observed where
  toFun raw := fun i => ⟨raw.val i, congrFun raw.property i⟩
  invFun residues := ⟨fun i => (residues i).val, funext fun i => (residues i).property⟩
  left_inv raw := Subtype.ext (funext fun _ => rfl)
  right_inv residues := funext fun i => Subtype.ext (by rfl)

section Capacity

variable (q : S → C) (observed : I → C)
variable [Fintype I] [DecidableEq I] [∀ i, Fintype {s : S // q s = observed i}]

theorem card_fibreTape :
    Fintype.card (FibreTape q observed) = ∏ i, Fintype.card {s : S // q s = observed i} :=
  Fintype.card_pi

/-- Exact worst-case bit width, with the fibre dictionaries fixed. The
upper bound is a finite ranking, not a claim about the speed of ranking. -/
theorem width_iff (bits : Nat) :
    Nonempty (FibreTape q observed ↪ Fin (2 ^ bits)) ↔
      (∏ i, Fintype.card {s : S // q s = observed i}) ≤ 2 ^ bits := by
  rw [← card_fibreTape q observed]
  constructor
  · rintro ⟨encode⟩
    simpa using Fintype.card_le_of_embedding encode
  · intro fits
    exact ⟨(Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb fits)⟩

/-- For a fixed description machine and *the same* auxiliary condition on
all candidates, some spelling tape needs at least this many bits even in
plain conditional program complexity. It does not rule out special tapes
whose observed order has a much shorter description. -/
theorem some_fibre_incompressible (encode : FibreTape q observed → BinString)
    (inj : Function.Injective encode) (side : BinString) (bits : Nat)
    (capacity : 2 ^ bits ≤ ∏ i, Fintype.card {s : S // q s = observed i}) :
    ∃ raw, bits ≤ canonicalPlainConditionalComplexity (encode raw) side := by
  classical
  let U := universalConditionalAlgorithm
  let candidates := (Finset.univ : Finset (FibreTape q observed)).image encode
  let decode := throughAlgorithm (fun p => U p side) some
  have many : 2 ^ bits ≤ candidates.card := by
    unfold candidates
    rw [Finset.card_image_of_injective _ inj, Finset.card_univ, card_fibreTape]
    exact capacity
  have short := card_describedBelow_lt (σ := Bool) decode (by simp) candidates bits
  by_contra contradict
  have all : candidates ⊆ candidates.filter (DescribedBelow decode bits) := by
    intro v member
    have displayed : ∃ raw, encode raw = v := by simpa [candidates] using member
    obtain ⟨raw, rfl⟩ := displayed
    have low : canonicalPlainConditionalComplexity (encode raw) side < bits :=
      Nat.lt_of_not_ge fun enough => contradict ⟨raw, enough⟩
    obtain ⟨program, gives, width⟩ := exists_program_of_plainConditionalComplexity U side (encode raw)
      (canonicalPlainConditional_hasProgram side (encode raw))
    exact Finset.mem_filter.mpr ⟨member, program, throughAlgorithm_of_mem gives,
      width.trans_lt low⟩
  have tooFew : (candidates.filter (DescribedBelow decode bits)).card < 2 ^ bits := by
    simpa using short
  exact (Nat.not_lt_of_ge (many.trans (Finset.card_le_card all))) tooFew

end Capacity

namespace Position

open OccurrenceRuns

private theorem efBlock_mem_iff (low : Nat) (ids : Finset Nat) (j x : Nat) :
    x ∈ efBlock low ids j ↔ x ∈ ids ∧ x / 2 ^ low = j := by
  simp [efBlock]

/-- Elias–Fano decodes a sorted sequence, not just its underlying set.
If two equal payloads have distinct position IDs, decoding keeps both. -/
theorem ef_ordered (low blocks : Nat) (ids : List Nat) (order : ids.SortedLT)
    (inRange : ∀ x ∈ ids, x < blocks * 2 ^ low) :
    efDecodeFrom low 0 (efEncode low blocks ids.toFinset).1
      (efEncode low blocks ids.toFinset).2 = ids := by
  have h := efDecodeFrom_blocks low ids.toFinset blocks 0 []
  rw [List.append_nil, ← List.range_eq_range'] at h
  simp only [efEncode]
  rw [h]
  let recovered := (List.range blocks).flatMap (efBlock low ids.toFinset)
  have increasing : recovered.SortedLT := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_flatMap]
    constructor
    · intro j _
      have h₁ := (Finset.pairwise_sort (ids.toFinset.filter fun x => x / 2 ^ low = j)
        (· ≤ ·)).sortedLE
      exact (h₁.sortedLT_of_nodup (Finset.sort_nodup _ _)).pairwise
    · apply (List.pairwise_lt_range (n := blocks)).imp
      intro i j lt x hx y hy
      have hxi := (efBlock_mem_iff low ids.toFinset i x).1 hx
      have hyj := (efBlock_mem_iff low ids.toFinset j y).1 hy
      exact lt_of_not_ge fun no => (not_le_of_gt lt)
        (hxi.2 ▸ hyj.2 ▸ Nat.div_le_div_right no)
  apply List.Perm.eq_of_sortedLE increasing.sortedLE order.sortedLE
  apply (List.perm_ext_iff_of_nodup increasing.nodup order.nodup).2
  intro x
  simp only [recovered, List.mem_flatMap, List.mem_range, efBlock_mem_iff, List.mem_toFinset]
  constructor
  · rintro ⟨_, _, found, _⟩
    exact found
  · intro found
    have pos : 0 < (2 : Nat) ^ low := Nat.two_pow_pos low
    exact ⟨x / 2 ^ low, (Nat.div_lt_iff_lt_mul pos).2 (inRange x found), found, rfl⟩

end Position

end Mettapedia.GSLT.Equations.PostingInformation
