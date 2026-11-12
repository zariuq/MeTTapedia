import Mettapedia.Machines.TIsa.CellEffects

/-!
# Source-grade payments as ordinary resource transitions

An admitted grade is a positive 32-bit quantity. The allowance and running
receipt are 64-bit words. Successful payment increases the receipt without
wrapping; insufficient allowance preserves it. An invalid entry receipt has
a separate result. Source compilation chooses the payment points and grades.

Paid and exhausted transitions use the existing point, allowance and receipt
cells. The finite-profile theorem gives realization and reflection for these
semantic recipes. C admission, native emission and whole-program cost laws
require their own refinement proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Funding

structure Grade where
  units : BitVec 32
  positive : units ≠ 0#32

def Grade.of? (units : BitVec 32) : Option Grade :=
  if positive : units = 0#32 then none else some ⟨units, positive⟩

theorem Grade.of?_isSome_iff (units : BitVec 32) :
    (Grade.of? units).isSome = true ↔ units ≠ 0#32 := by
  unfold Grade.of?
  split <;> simp_all

def Grade.word (grade : Grade) : Word := grade.units.zeroExtend 64

theorem Grade.word_toNat (grade : Grade) : grade.word.toNat = grade.units.toNat := by
  have bound : grade.units.toNat < 2 ^ 64 := lt_of_lt_of_le grade.units.isLt (by decide)
  simp only [Grade.word, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt bound

theorem Grade.positive_toNat (grade : Grade) : 0 < grade.units.toNat := by
  have nonzero : grade.units.toNat ≠ 0 := by
    intro zero
    apply grade.positive
    exact BitVec.eq_of_toNat_eq zero
  omega

inductive Result where
  | invalidReceipt
  | exhausted
  | paid (receipt : Word)
  deriving DecidableEq, Repr

def available (budget receipt : Word) (grade : Grade) : Bool :=
  decide (receipt.toNat + grade.units.toNat ≤ budget.toNat)

def charge (budget receipt : Word) (grade : Grade) : Result :=
  if budget.toNat < receipt.toNat then .invalidReceipt
  else if available budget receipt grade then .paid (receipt + grade.word)
  else .exhausted

theorem available_iff (budget receipt : Word) (grade : Grade) :
    available budget receipt grade = true ↔ receipt.toNat + grade.units.toNat ≤ budget.toNat := by
  simp [available]

theorem invalid_iff (budget receipt : Word) (grade : Grade) :
    charge budget receipt grade = .invalidReceipt ↔ budget.toNat < receipt.toNat := by
  unfold charge
  split <;> simp_all
  split <;> simp_all

theorem paid_iff (budget receipt following : Word) (grade : Grade) :
    charge budget receipt grade = .paid following ↔
      receipt.toNat + grade.units.toNat ≤ budget.toNat ∧ following = receipt + grade.word := by
  by_cases invalid : budget.toNat < receipt.toNat
  · constructor
    · intro paid
      simp [charge, invalid] at paid
    · rintro ⟨fits, _⟩
      omega
  · by_cases fits : receipt.toNat + grade.units.toNat ≤ budget.toNat
    · have executed : charge budget receipt grade = .paid (receipt + grade.word) := by
        simp [charge, invalid, available, fits]
      rw [executed]
      constructor
      · intro paid
        exact ⟨fits, (Result.paid.inj paid).symm⟩
      · rintro ⟨_, rfl⟩
        rfl
    · simp [charge, invalid, available, fits]

theorem exhausted_iff (budget receipt : Word) (grade : Grade) :
    charge budget receipt grade = .exhausted ↔
      receipt.toNat ≤ budget.toNat ∧ budget.toNat < receipt.toNat + grade.units.toNat := by
  unfold charge
  split <;> simp_all [available_iff]

theorem paid_no_wrap (budget receipt following : Word) (grade : Grade)
    (paid : charge budget receipt grade = .paid following) :
    following.toNat = receipt.toNat + grade.units.toNat ∧ following.toNat ≤ budget.toNat := by
  obtain ⟨fits, rfl⟩ := (paid_iff budget receipt following grade).mp paid
  have bound : receipt.toNat + grade.units.toNat < 2 ^ 64 := lt_of_le_of_lt fits budget.isLt
  have same : (receipt + grade.word).toNat = receipt.toNat + grade.units.toNat := by
    rw [BitVec.toNat_add, grade.word_toNat, Nat.mod_eq_of_lt bound]
  rw [same]
  exact ⟨rfl, fits⟩

theorem available_sub_iff (budget receipt : Word) (grade : Grade)
    (valid : receipt.toNat ≤ budget.toNat) :
    available budget receipt grade = true ↔ grade.word.toNat ≤ (budget - receipt).toNat := by
  rw [BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def] using valid), grade.word_toNat,
    available_iff]
  omega

theorem paid_monotone (small large receipt following : Word) (grade : Grade)
    (larger : small.toNat ≤ large.toNat)
    (paid : charge small receipt grade = .paid following) :
    charge large receipt grade = .paid following := by
  obtain ⟨fits, same⟩ := (paid_iff small receipt following grade).mp paid
  exact (paid_iff large receipt following grade).mpr ⟨fits.trans larger, same⟩

theorem zero_allowance (grade : Grade) : charge (0#64) (0#64) grade = .exhausted := by
  apply (exhausted_iff _ _ _).mpr
  constructor
  · decide
  · simpa only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add] using grade.positive_toNat

theorem maximal_allowance (receipt : Word) (grade : Grade)
    (fits : receipt.toNat + grade.units.toNat < 2 ^ 64) :
    charge (0xffffffffffffffff#64) receipt grade = .paid (receipt + grade.word) := by
  apply (paid_iff _ _ _ _).mpr
  exact ⟨by change receipt.toNat + grade.units.toNat ≤ 18446744073709551615; omega, rfl⟩

open Cells CellEffects

universe u
variable {Key : Type u} [DecidableEq Key]

structure Gate (Key : Type u) where
  point : Key
  atPoint : Word
  nextPoint : Word
  exhaustedPoint : Word
  budget : Key
  receipt : Key
  grade : Grade

def Gate.check (gate : Gate Key) : Bool := decide ([gate.point, gate.budget, gate.receipt].Nodup)

def Gate.paidRecipe (gate : Gate Key) : Recipe Key where
  inputs := [gate.point, gate.budget, gate.receipt]
  outputs := [gate.point, gate.receipt]
  guard := fun inputs outputs => match inputs, outputs with
    | [point, budget, receipt], [next, following] =>
        gate.check && point == gate.atPoint && next == gate.nextPoint &&
          available budget receipt gate.grade && following == receipt + gate.grade.word
    | _, _ => false

def Gate.exhaustedRecipe (gate : Gate Key) : Recipe Key where
  inputs := [gate.point, gate.budget, gate.receipt]
  outputs := [gate.point]
  guard := fun inputs outputs => match inputs, outputs with
    | [point, budget, receipt], [next] =>
        gate.check && point == gate.atPoint && next == gate.exhaustedPoint &&
          decide (receipt.toNat ≤ budget.toNat ∧ budget.toNat < receipt.toNat + gate.grade.units.toNat)
    | _, _ => false

theorem Gate.paid_guard_iff (gate : Gate Key) (before after : Key → Word) :
    gate.paidRecipe.guard (gate.paidRecipe.inputs.map before) (gate.paidRecipe.outputs.map after) = true ↔
      gate.check = true ∧ before gate.point = gate.atPoint ∧ after gate.point = gate.nextPoint ∧
      charge (before gate.budget) (before gate.receipt) gate.grade = .paid (after gate.receipt) := by
  simp only [paidRecipe, List.map_cons, List.map_nil, Bool.and_eq_true, beq_iff_eq,
    available_iff, paid_iff]
  tauto

theorem Gate.exhausted_guard_iff (gate : Gate Key) (before after : Key → Word) :
    gate.exhaustedRecipe.guard (gate.exhaustedRecipe.inputs.map before) (gate.exhaustedRecipe.outputs.map after) = true ↔
      gate.check = true ∧ before gate.point = gate.atPoint ∧ after gate.point = gate.exhaustedPoint ∧
      charge (before gate.budget) (before gate.receipt) gate.grade = .exhausted := by
  simp only [exhaustedRecipe, List.map_cons, List.map_nil, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, exhausted_iff]
  tauto

theorem Gate.exhausted_keeps_receipt (gate : Gate Key) (checked : gate.check = true) :
    gate.receipt ∈ gate.exhaustedRecipe.reads := by
  have distinct : [gate.point, gate.budget, gate.receipt].Nodup := of_decide_eq_true checked
  have apart : gate.receipt ≠ gate.point :=
    Ne.symm ((List.pairwise_cons.mp distinct).1 gate.receipt (by simp))
  simp [Recipe.reads, Recipe.writes, exhaustedRecipe, apart]

def Gate.recipes (gate : Gate Key) : List (Recipe Key) := [gate.paidRecipe, gate.exhaustedRecipe]

theorem Gate.profile_rewrite_iff (gate : Gate Key) (keys : Finset Key)
    (before : Key → Word) (result : Multiset (Cell Key)) :
    (CellEffects.profile gate.recipes).theory.rewrites (encode keys before) result ↔
      (∃ after : Key → Word, gate.paidRecipe.support ⊆ keys ∧ gate.check = true ∧
        before gate.point = gate.atPoint ∧ after gate.point = gate.nextPoint ∧
        charge (before gate.budget) (before gate.receipt) gate.grade = .paid (after gate.receipt) ∧
        result = encode keys (overwrite gate.paidRecipe.writes before after)) ∨
      (∃ after : Key → Word, gate.exhaustedRecipe.support ⊆ keys ∧ gate.check = true ∧
        before gate.point = gate.atPoint ∧ after gate.point = gate.exhaustedPoint ∧
        charge (before gate.budget) (before gate.receipt) gate.grade = .exhausted ∧
        result = encode keys (overwrite gate.exhaustedRecipe.writes before after)) := by
  rw [CellEffects.profile_rewrite_iff]
  constructor
  · rintro ⟨recipe, member, after, included, guarded, same⟩
    simp only [recipes, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · left
      obtain ⟨checked, atPoint, nextPoint, paid⟩ := (gate.paid_guard_iff before after).mp guarded
      exact ⟨after, included, checked, atPoint, nextPoint, paid, same⟩
    · right
      obtain ⟨checked, atPoint, nextPoint, exhausted⟩ := (gate.exhausted_guard_iff before after).mp guarded
      exact ⟨after, included, checked, atPoint, nextPoint, exhausted, same⟩
  · rintro (⟨after, included, checked, atPoint, nextPoint, paid, same⟩ |
      ⟨after, included, checked, atPoint, nextPoint, exhausted, same⟩)
    · exact ⟨gate.paidRecipe, by simp [recipes], after, included,
        (gate.paid_guard_iff before after).mpr ⟨checked, atPoint, nextPoint, paid⟩, same⟩
    · exact ⟨gate.exhaustedRecipe, by simp [recipes], after, included,
        (gate.exhausted_guard_iff before after).mpr ⟨checked, atPoint, nextPoint, exhausted⟩, same⟩

namespace Controls

private def three : Grade := ⟨3, by decide⟩
private def one : Grade := ⟨1, by decide⟩

example : Grade.of? 0 = none := rfl
example : (Grade.of? 3).isSome = true := by decide
example : charge 10 7 three = .paid 10 := by decide
example : charge 9 7 three = .exhausted := by decide
example : charge 9 10 one = .invalidReceipt := by decide
example : charge 0 0 one = .exhausted := zero_allowance one
example : charge 0xffffffffffffffff 0xffffffffffffffff one = .exhausted := by decide

private def gate : Gate Nat := ⟨0, 1, 2, 3, 1, 2, three⟩
example : gate.paidRecipe.guard [1, 10, 7] [2, 10] = true := by decide
example : gate.paidRecipe.guard [1, 9, 7] [2, 10] = false := by decide
example : gate.exhaustedRecipe.guard [1, 9, 7] [3] = true := by decide
example : gate.exhaustedRecipe.guard [1, 9, 10] [3] = false := by decide

end Controls
end Mettapedia.Machines.TIsa.Funding

#print axioms Mettapedia.Machines.TIsa.Funding.paid_no_wrap
#print axioms Mettapedia.Machines.TIsa.Funding.available_sub_iff
#print axioms Mettapedia.Machines.TIsa.Funding.Gate.paid_guard_iff
#print axioms Mettapedia.Machines.TIsa.Funding.Gate.exhausted_keeps_receipt
#print axioms Mettapedia.Machines.TIsa.Funding.Gate.profile_rewrite_iff
