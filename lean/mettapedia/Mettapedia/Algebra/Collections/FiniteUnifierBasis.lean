import Mathlib.Data.Finset.Max
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Lean.Elab.Tactic.Omega

/-!
# Stable finite bases under a decidable generality preorder

Strictly subsumed candidates are removed. Equivalent candidates are tied by
their original indices, retaining the first. The result preserves coverage,
has no two distinct comparable entries and is a subsequence of the original
enumeration. Deciding the concrete generality relation remains an explicit
input to this generic finite selector.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.FiniteUnifierBasis

universe u
variable {α : Type u}

def Dominates (items : List α) (covers : α → α → Prop) (better worse : Fin items.length) : Prop :=
  covers (items.get better) (items.get worse) ∧
    (¬ covers (items.get worse) (items.get better) ∨ better.val < worse.val)

instance (items : List α) (covers : α → α → Prop) [DecidableRel covers]
    (better worse : Fin items.length) : Decidable (Dominates items covers better worse) := by
  unfold Dominates
  infer_instance

def retained (items : List α) (covers : α → α → Prop) [DecidableRel covers] : Finset (Fin items.length) :=
  Finset.univ.filter fun index => ¬ ∃ other, Dominates items covers other index

def indices (items : List α) (covers : α → α → Prop) [DecidableRel covers] : List (Fin items.length) :=
  (List.finRange items.length).filter fun index => index ∈ retained items covers

def select (items : List α) (covers : α → α → Prop) [DecidableRel covers] : List α :=
  (indices items covers).map items.get

def below (items : List α) (covers : α → α → Prop) [DecidableRel covers]
    (index : Fin items.length) : Finset (Fin items.length) :=
  Finset.univ.filter fun other => covers (items.get index) (items.get other)

def score (items : List α) (covers : α → α → Prop) [DecidableRel covers]
    (index : Fin items.length) : Nat :=
  (items.length + 1) * (below items covers index).card + (items.length - index.val)

variable (items : List α) (covers : α → α → Prop) [DecidableRel covers]
variable (reflexive : ∀ a, covers a a)
variable (transitive : ∀ {a b c}, covers a b → covers b c → covers a c)

include transitive in
theorem below_mono {first second : Fin items.length}
    (general : covers (items.get first) (items.get second)) :
    below items covers second ⊆ below items covers first := by
  intro index member
  simp only [below, Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
  exact transitive general member

include reflexive transitive in
theorem strict_rank {first second : Fin items.length}
    (general : covers (items.get first) (items.get second))
    (strict : ¬ covers (items.get second) (items.get first)) :
    (below items covers second).card < (below items covers first).card := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (below_mono items covers transitive general)).mpr
  refine ⟨first, ?_, ?_⟩
  · simp only [below, Finset.mem_filter, Finset.mem_univ, true_and]
    exact reflexive _
  · simpa only [below, Finset.mem_filter, Finset.mem_univ, true_and] using strict

include reflexive transitive in
theorem dominates_increases {first second : Fin items.length}
    (dominates : Dominates items covers first second) :
    score items covers second < score items covers first := by
  obtain ⟨general, strictOrEarlier⟩ := dominates
  rcases strictOrEarlier with strict | earlier
  · have ranks := strict_rank items covers reflexive transitive general strict
    have scaled := Nat.mul_le_mul_left (items.length + 1) (Nat.succ_le_of_lt ranks)
    unfold score
    rw [Nat.mul_succ] at scaled
    have bounded : items.length - second.val ≤ items.length := Nat.sub_le _ _
    omega
  · have ranks := Finset.card_le_card (below_mono items covers transitive general)
    have scaled := Nat.mul_le_mul_left (items.length + 1) ranks
    have inside := second.isLt
    unfold score
    omega

theorem mem_retained (index : Fin items.length) :
    index ∈ retained items covers ↔ ¬ ∃ other, Dominates items covers other index := by
  simp only [retained, Finset.mem_filter, Finset.mem_univ, true_and]

include reflexive transitive in
/-- Every input candidate is covered by an actually retained index. -/
theorem exists_retained (index : Fin items.length) :
    ∃ other ∈ retained items covers, covers (items.get other) (items.get index) := by
  let upper := Finset.univ.filter fun other : Fin items.length => covers (items.get other) (items.get index)
  have nonempty : upper.Nonempty := ⟨index, by simp [upper, reflexive]⟩
  obtain ⟨best, member, maximal⟩ := Finset.exists_max_image upper (score items covers) nonempty
  have bestCovers : covers (items.get best) (items.get index) := (Finset.mem_filter.mp member).2
  refine ⟨best, (mem_retained items covers best).mpr ?_, bestCovers⟩
  rintro ⟨other, dominates⟩
  have inUpper : other ∈ upper :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, transitive dominates.1 bestCovers⟩
  have bounded := maximal other inUpper
  have increases := dominates_increases items covers reflexive transitive dominates
  omega

/-- Different retained indices are incomparable, including equivalence. -/
theorem incomparable {first second : Fin items.length}
    (firstKept : first ∈ retained items covers) (secondKept : second ∈ retained items covers)
    (different : first ≠ second) : ¬ covers (items.get first) (items.get second) := by
  intro general
  have firstMax := (mem_retained items covers first).mp firstKept
  have secondMax := (mem_retained items covers second).mp secondKept
  by_cases back : covers (items.get second) (items.get first)
  · have unequal : first.val ≠ second.val := fun same => different (Fin.ext same)
    by_cases earlier : first.val < second.val
    · exact secondMax ⟨first, general, Or.inr earlier⟩
    · exact firstMax ⟨second, back, Or.inr (by omega)⟩
  · exact secondMax ⟨first, general, Or.inl back⟩

theorem indices_sublist : (indices items covers).Sublist (List.finRange items.length) := List.filter_sublist

theorem mem_indices (index : Fin items.length) :
    index ∈ indices items covers ↔ index ∈ retained items covers := by
  simp [indices, List.mem_finRange]

theorem selected_from_input {value : α} (member : value ∈ select items covers) : value ∈ items := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact List.get_mem _ _

include reflexive transitive in
theorem covers_input {value : α} (member : value ∈ items) :
    ∃ chosen ∈ select items covers, covers chosen value := by
  obtain ⟨index, rfl⟩ := List.get_of_mem member
  obtain ⟨chosen, kept, general⟩ := exists_retained items covers reflexive transitive index
  exact ⟨items.get chosen, List.mem_map.mpr ⟨chosen, (mem_indices items covers chosen).mpr kept, rfl⟩, general⟩

theorem no_subsumed_distinct {first second : α} (left : first ∈ select items covers)
    (right : second ∈ select items covers) (general : covers first second) : first = second := by
  obtain ⟨firstIndex, firstKept, rfl⟩ := List.mem_map.mp left
  obtain ⟨secondIndex, secondKept, rfl⟩ := List.mem_map.mp right
  by_cases same : firstIndex = secondIndex
  · rw [same]
  · exact False.elim (incomparable items covers ((mem_indices items covers _).mp firstKept)
      ((mem_indices items covers _).mp secondKept) same general)

include reflexive in
theorem selected_nodup : (select items covers).Nodup := by
  apply ((List.nodup_finRange items.length).filter _).map_on
  intro first firstKept second secondKept same
  by_contra different
  apply incomparable items covers ((mem_indices items covers _).mp firstKept)
    ((mem_indices items covers _).mp secondKept) different
  rw [same]
  exact reflexive _

namespace Controls

theorem stable_equivalent_representatives :
    select [2, 1, 2, 3] (Eq : Nat → Nat → Prop) = [2, 1, 3] ∧
      (indices [2, 1, 2, 3] (Eq : Nat → Nat → Prop)).map Fin.val = [0, 1, 3] := by decide

theorem genuinely_more_general_replaces_a_candidate :
    select [3, 1, 2, 1] (fun first second : Nat => first ≤ second) = [1] ∧
      (indices [3, 1, 2, 1] (fun first second : Nat => first ≤ second)).map Fin.val = [1] := by decide

theorem incomparable_candidates_are_not_merged :
    select [0, 1] (Eq : Nat → Nat → Prop) = [0, 1] := by decide

end Controls

end Mettapedia.Algebra.Collections.FiniteUnifierBasis
