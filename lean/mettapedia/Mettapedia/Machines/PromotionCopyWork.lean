import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Copy work between major collections

Both policies are charged for the same sequence of survivor sets at minor
collection boundaries. A semispace policy copies every survivor each time.
A promotion policy copies a survivor into a stable older region on its first
visit. Identities are not recycled in this epoch. The model charges copies,
not root scans, tracing, promotion-policy overhead, or space retained until
a major collection. It applies only after the separate lifetime and trace
obligations have been met.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PromotionCopyWork

variable {Address : Type*} [DecidableEq Address]

def distinctSurvivors : List (Finset Address) → Finset Address
  | [] => ∅
  | live :: rest => live ∪ distinctSurvivors rest

def copyWeight (charge : Address → Nat) (cells : Finset Address) : Nat :=
  ∑ a ∈ cells, charge a

def semispaceWork (charge : Address → Nat) : List (Finset Address) → Nat
  | [] => 0
  | live :: rest => copyWeight charge live + semispaceWork charge rest

def promotionWork (charge : Address → Nat) (old : Finset Address) :
    List (Finset Address) → Nat
  | [] => 0
  | live :: rest =>
      copyWeight charge (live \ old) + promotionWork charge (old ∪ live) rest

def recopyWork (charge : Address → Nat) (old : Finset Address) :
    List (Finset Address) → Nat
  | [] => 0
  | live :: rest =>
      copyWeight charge (live ∩ old) + recopyWork charge (old ∪ live) rest

private theorem copyWeight_union (charge : Address → Nat) (x y : Finset Address)
    (disjoint : Disjoint x y) :
    copyWeight charge (x ∪ y) = copyWeight charge x + copyWeight charge y :=
  Finset.sum_union disjoint

/-- Copying each newly surviving identity at most once pays exactly for
the union, with identities already old at entry charged nothing. -/
theorem promotionWork_eq_distinct (charge : Address → Nat) (old : Finset Address)
    (visits : List (Finset Address)) :
    promotionWork charge old visits = copyWeight charge (distinctSurvivors visits \ old) := by
  induction visits generalizing old with
  | nil => simp [promotionWork, distinctSurvivors, copyWeight]
  | cons live rest ih =>
      rw [promotionWork, ih, distinctSurvivors, ← copyWeight_union]
      · congr 1
        ext a
        simp only [Finset.mem_union, Finset.mem_sdiff]
        tauto
      · apply Finset.disjoint_left.mpr
        simp only [Finset.mem_sdiff, Finset.mem_union]
        tauto

/-- Recopying previously promoted cells is precisely the additional charge.
This is not an assertion about the cost of running the two collectors. -/
theorem semispaceWork_eq_promotion_add_recopy (charge : Address → Nat)
    (old : Finset Address) (visits : List (Finset Address)) :
    semispaceWork charge visits =
      promotionWork charge old visits + recopyWork charge old visits := by
  induction visits generalizing old with
  | nil => simp [semispaceWork, promotionWork, recopyWork]
  | cons live rest ih =>
      have union : (live \ old) ∪ (live ∩ old) = live := by
        ext a
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
        tauto
      have disjoint : Disjoint (live \ old) (live ∩ old) := by
        apply Finset.disjoint_left.mpr
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      have split := (copyWeight_union charge _ _ disjoint).symm
      rw [union] at split
      simp only [semispaceWork, promotionWork, recopyWork, ih (old ∪ live)]
      omega

theorem promotionWork_le_semispaceWork (charge : Address → Nat)
    (old : Finset Address) (visits : List (Finset Address)) :
    promotionWork charge old visits ≤ semispaceWork charge visits := by
  rw [semispaceWork_eq_promotion_add_recopy charge old visits]
  omega

/-- In the class of plans that must copy each new surviving identity
somewhere in the epoch, promotion attains the weighted lower bound.
The proposed plan's footprint is independent of the visitation schedule. -/
theorem promotionWork_minimal (charge : Address → Nat) (old plan : Finset Address)
    (visits : List (Finset Address)) (covers : distinctSurvivors visits ⊆ old ∪ plan) :
    promotionWork charge old visits ≤ copyWeight charge plan := by
  rw [promotionWork_eq_distinct]
  apply Finset.sum_le_sum_of_subset
  intro a member
  obtain ⟨alive, fresh⟩ := Finset.mem_sdiff.mp member
  rcases Finset.mem_union.mp (covers alive) with already | planned
  · exact (fresh already).elim
  · exact planned

private theorem distinctSurvivors_append (first second : List (Finset Address)) :
    distinctSurvivors (first ++ second) = distinctSurvivors first ∪ distinctSurvivors second := by
  induction first with
  | nil => simp [distinctSurvivors]
  | cons head rest ih => simp [distinctSurvivors, ih, Finset.union_assoc]

omit [DecidableEq Address] in
private theorem semispaceWork_append (charge : Address → Nat)
    (first second : List (Finset Address)) :
    semispaceWork charge (first ++ second) = semispaceWork charge first + semispaceWork charge second := by
  induction first with
  | nil => simp [semispaceWork]
  | cons head rest ih => simp [semispaceWork, ih, Nat.add_assoc]

/-- A workload family, not a claim about any particular safe-point policy:
one new cell survives at each successive collection. -/
def growingResult : Nat → List (Finset Nat)
  | 0 => []
  | n + 1 => growingResult n ++ [Finset.range (n + 1)]

theorem distinctSurvivors_growingResult (n : Nat) :
    distinctSurvivors (growingResult n) = Finset.range n := by
  induction n with
  | zero => simp [growingResult, distinctSurvivors]
  | succ n ih =>
      rw [growingResult, distinctSurvivors_append, ih]
      simp only [distinctSurvivors, Finset.union_empty]
      exact Finset.union_eq_right.mpr (Finset.range_mono (Nat.le_succ n))

/-- Linear versus triangular copy counts, on the same survival trace.
Doubling the semispace count avoids any rounding in the statement. -/
theorem growingResult_cost (n : Nat) :
    promotionWork (fun _ => 1) ∅ (growingResult n) = n ∧
      2 * semispaceWork (fun _ => 1) (growingResult n) = n * (n + 1) := by
  constructor
  · simp [promotionWork_eq_distinct, distinctSurvivors_growingResult, copyWeight]
  · induction n with
    | zero => simp [growingResult, semispaceWork]
    | succ n ih =>
        rw [growingResult, semispaceWork_append]
        simp only [semispaceWork, copyWeight, Finset.sum_const, Finset.card_range,
          smul_eq_mul, Nat.mul_one, Nat.add_zero]
        nlinarith only [ih]

namespace Controls

theorem a_single_fresh_visit_needs_the_same_copy :
    promotionWork (fun _ => 1) (∅ : Finset Nat) [{3, 4}] =
      semispaceWork (fun _ => 1) [{3, 4}] := by decide

theorem repeated_survivors_are_an_actual_extra_cost :
    promotionWork (fun _ => 1) (∅ : Finset Nat) (growingResult 8) = 8 ∧
      semispaceWork (fun _ => 1) (growingResult 8) = 36 := by decide

end Controls
end Mettapedia.Machines.PromotionCopyWork
