import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Stable slots in a retained foreign region

The native region has one persistent root reference. Variable slots are paths
through a radix-32 tree, rather than saved references into a temporary foreign
frame. This module proves that recursive path updates implement an independently
specified flat store, preserve other slots, and inspect exactly one node per
address digit. The bounded ordinal codec is injective: neighbouring radix blocks
cannot alias. A one-digit address has an explicit aliasing counterexample.
Leaf contents can designate shared solver variables. Noninterference here is
about replacing an addressed slot, not binding a shared logical variable.

The cost is a count of slot-node visits, not solver work, allocation, or wall
time. Leaf values are abstract; attributed-variable graphs, their sharing and
cycles are supplied by SWI and qualified by the native lifecycle gate. This is
not a proof of foreign-frame allocation or of the C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.ForeignRegionSlots

inductive Address : Nat → Type where
  | nil : Address 0
  | cons {depth : Nat} (digit : Fin 32) (tail : Address depth) : Address (depth + 1)
  deriving DecidableEq

inductive Slots (Value : Type) : Nat → Type where
  | leaf (value : Option Value) : Slots Value 0
  | branch {depth : Nat} (children : Fin 32 → Slots Value depth) : Slots Value (depth + 1)

variable {Value : Type} {depth : Nat}

def read : {depth : Nat} → Slots Value depth → Address depth → Option Value
  | 0, .leaf value, .nil => value
  | _ + 1, .branch children, .cons digit tail => read (children digit) tail

def write : {depth : Nat} → Slots Value depth → Address depth → Option Value → Slots Value depth
  | 0, .leaf _, .nil, value => .leaf value
  | _ + 1, .branch children, .cons digit tail, value =>
      .branch (Function.update children digit (write (children digit) tail value))

def empty : (depth : Nat) → Slots Value depth
  | 0 => .leaf none
  | depth + 1 => .branch (fun _ => empty depth)

theorem read_empty (address : Address depth) : read (empty depth : Slots Value depth) address = none := by
  induction address with
  | nil => rfl
  | cons digit tail ih => exact ih

theorem read_write (slots : Slots Value depth) (target query : Address depth)
    (value : Option Value) :
    read (write slots target value) query = if query = target then value else read slots query := by
  induction slots with
  | leaf previous => cases target; cases query; rfl
  | branch children ih =>
      cases target with
      | cons digit tail =>
        cases query with
        | cons other rest =>
          by_cases same : other = digit
          · subst other
            simpa [read, write] using ih digit tail rest
          · simp [read, write, same]

/-- The flat specification updates an address directly; the realization walks
and rebuilds only its tree path. -/
theorem write_realizes_flat_update (slots : Slots Value depth) (target : Address depth)
    (value : Option Value) :
    read (write slots target value) = Function.update (read slots) target value := by
  funext query
  simpa [Function.update_apply] using read_write slots target query value

theorem read_write_same (slots : Slots Value depth) (target : Address depth)
    (value : Option Value) : read (write slots target value) target = value := by
  simp [read_write]

theorem read_write_other (slots : Slots Value depth) (target query : Address depth)
    (different : query ≠ target) (value : Option Value) :
    read (write slots target value) query = read slots query := by
  simp [read_write, different]

def readWithCost : {depth : Nat} → Slots Value depth → Address depth → Option Value × Nat
  | 0, .leaf value, .nil => (value, 0)
  | _ + 1, .branch children, .cons digit tail =>
      let result := readWithCost (children digit) tail
      (result.1, result.2 + 1)

theorem readWithCost_exact (slots : Slots Value depth) (address : Address depth) :
    readWithCost slots address = (read slots address, depth) := by
  induction slots with
  | leaf value => cases address; rfl
  | branch children ih =>
      cases address with
      | cons digit tail => simp [readWithCost, read, ih]

def encode : (depth : Nat) → Nat → Address depth
  | 0, _ => .nil
  | depth + 1, index =>
      .cons ⟨(index / 32 ^ depth) % 32, Nat.mod_lt _ (by decide)⟩
        (encode depth (index % 32 ^ depth))

def ordinal : {depth : Nat} → Address depth → Nat
  | 0, .nil => 0
  | depth + 1, .cons digit tail => digit.val * 32 ^ depth + ordinal tail

theorem ordinal_encode (index : Nat) (bound : index < 32 ^ depth) :
    ordinal (encode depth index) = index := by
  induction depth generalizing index with
  | zero =>
      simp only [pow_zero] at bound
      have same : index = 0 := by omega
      subst index
      rfl
  | succ depth ih =>
      have positive : 0 < 32 ^ depth := by positivity
      have high : index / 32 ^ depth < 32 := by
        apply (Nat.div_lt_iff_lt_mul positive).mpr
        simpa [pow_succ, Nat.mul_comm] using bound
      have low : index % 32 ^ depth < 32 ^ depth := Nat.mod_lt _ positive
      simp only [encode, ordinal, Nat.mod_eq_of_lt high, ih _ low]
      simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div index (32 ^ depth)

theorem encode_injective_bounded (left right : Nat)
    (leftBound : left < 32 ^ depth) (rightBound : right < 32 ^ depth)
    (same : encode depth left = encode depth right) : left = right := by
  have equality := congrArg ordinal same
  simpa [ordinal_encode left leftBound, ordinal_encode right rightBound] using equality

/-- Several native operations inspect fixed-depth addresses. Their addressing
cost depends on the number of demanded slots, not the retained network size. -/
def visits (slots : Slots Value depth) (addresses : List (Address depth)) : Nat :=
  (addresses.map (fun address => (readWithCost slots address).2)).sum

theorem visits_exact (slots : Slots Value depth) (addresses : List (Address depth)) :
    visits slots addresses = addresses.length * depth := by
  induction addresses with
  | nil => simp [visits]
  | cons address rest ih =>
      simp [visits, readWithCost_exact, Nat.add_mul, Nat.add_comm] at *

example : encode 3 0 ≠ encode 3 1024 := by decide
example : encode 2 0 ≠ encode 2 32 := by decide

/-- Truncating the address to a single digit aliases two distinct live slots. -/
example : 0 % 32 = 32 % 32 ∧ encode 2 0 ≠ encode 2 32 := by decide

example : read (write (empty 2 : Slots Nat 2) (encode 2 32) (some 7))
    (encode 2 32) = some 7 := by simp [read_write_same]

example : read (write (empty 2 : Slots Nat 2) (encode 2 32) (some 7))
    (encode 2 0) = none := by
  rw [read_write_other _ _ _ (by decide), read_empty]

end Mettapedia.Machines.IncrementalConformance.ForeignRegionSlots
