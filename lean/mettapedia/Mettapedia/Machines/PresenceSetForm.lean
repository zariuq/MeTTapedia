import Mathlib.Tactic

/-!
# A presence set in the form its density allows

A set space keeps the keys of its rows in a presence set.  Kept as a bitset
over the term universe's ids, it costs one bit an id the universe has, however
few keys the set holds: `K` small sets in a universe of `U` ids cost `K * U / 8`
bytes.  Kept as a hash table of its keys, it costs a bounded number of bytes a
key, whatever the universe.  Neither form is smaller everywhere: a large set
over a dense range of ids is smaller as bits.  The set takes the smaller form
and moves between them as its size and the universe change.

Both forms answer membership as the set of keys does; the model states the
forms' costs and proves:
* `bits_cost_of_sets`: `K` sets as bits cost `K * (U / 8)`, whatever they hold;
* `table_cost_of_sets`: as tables they cost `c` bytes a key held;
* `chosen_le`: the chosen form costs no more than either;
* `chosen_small_sets`: `K` sets of at most `n` keys each cost at most `K * c * n`
  in the chosen form, against `K * (U / 8)` as bits;
* `chosen_eq_bits_dense`: a set whose table would cost more than its bits is
  kept as bits, at exactly the bitset's cost.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PresenceSetForm

/-- A bitset over a universe of `U` ids, in bytes. -/
def bitsCost (U : Nat) : Nat := U / 8

/-- A table of `n` keys at `c` bytes a key. -/
def tableCost (c n : Nat) : Nat := c * n

/-- The chosen form: the smaller. -/
def chosenCost (c U n : Nat) : Nat := min (tableCost c n) (bitsCost U)

theorem chosen_le (c U n : Nat) :
    chosenCost c U n ≤ tableCost c n ∧ chosenCost c U n ≤ bitsCost U :=
  ⟨min_le_left _ _, min_le_right _ _⟩

theorem bits_cost_of_sets (U : Nat) (sizes : List Nat) :
    (sizes.map (fun _ => bitsCost U)).sum = sizes.length * (U / 8) := by
  simp [bitsCost, List.sum_replicate]

theorem table_cost_of_sets (c : Nat) (sizes : List Nat) :
    (sizes.map (tableCost c)).sum = c * sizes.sum := by
  induction sizes with
  | nil => simp
  | cons n rest ih =>
    simp only [List.map_cons, List.sum_cons, ih, tableCost]
    ring

/-- `K` sets of at most `n` keys each, in the chosen form, cost at most
`K * (c * n)`, however large the universe. -/
theorem chosen_small_sets (c U n : Nat) (sizes : List Nat)
    (small : ∀ m ∈ sizes, m ≤ n) :
    (sizes.map (chosenCost c U)).sum ≤ sizes.length * (c * n) := by
  induction sizes with
  | nil => simp
  | cons m rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hm : chosenCost c U m ≤ c * n :=
      le_trans (chosen_le c U m).1
        (Nat.mul_le_mul_left c (small m List.mem_cons_self))
    have hrest := ih (fun x hx => small x (List.mem_cons_of_mem m hx))
    nlinarith

/-- A set whose table would cost more than its bits is kept as bits. -/
theorem chosen_eq_bits_dense (c U n : Nat) (dense : bitsCost U ≤ tableCost c n) :
    chosenCost c U n = bitsCost U := min_eq_right dense

end Mettapedia.Machines.PresenceSetForm
