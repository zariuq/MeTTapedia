import Mettapedia.SetTheory.Surreal.Addition
import Mettapedia.SetTheory.Ordinal.NaturalSum
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Tactic.Abel

/-!
# The measure for the simultaneous induction

Everything outstanding about surreal addition runs through one induction, which
proves two statements together:

```
Mono a b c :  a < b  →  add a c < add b c
Sep  x y   :  Separated (leftSum x y) (rightSum x y)
```

They are mutually dependent. `Sep x y` needs `add l y < add r y` for `l` a left
and `r` a right option of `x`, which is `Mono l r y`; and `Mono a b c` needs
`Sep b c` in order to know that `add l c` really is an option of `add b c`.

The whole difficulty is a measure that falls on every call. This file supplies
one and proves all five decreases, with no hypotheses left over.

## Three measures that do not work, and why

Writing `bx` for `birthday x`:

* **Maximum** fails on `Mono a b c → Mono a l c` with `bl < bb`: when `ba ≥ bb`
  both maxima are `ba` and nothing moves.
* **The natural sum of birthdays** fails on `Sep x y → Mono l r y`, which would
  need `bl ⊕ br < bx`. Two options of a number born on day `2` can both be born
  on day `1`, and `1 ⊕ 1 = 2`. Measured, not assumed: `nadd_measure_fails` in
  `Ordinal/NaturalSum.lean`'s controls.
* **Ordinary ordinal addition** is not strictly monotone on the left at all:
  `0 + ω = 1 + ω` (`NaturalSumControls.ordinal_add_not_strict_left`).

A fourth candidate almost works, and recording why it does not is what points
at the one that does. Weighing a number by `ω ^ bx` and combining with the
natural sum makes every obligation a single ordinal comparison, because
`ω`-powers are additively principal. But discharging `Sep → Mono` then needs

```
naturalAdd (ω ^ a) (ω ^ b) < ω ^ c        for a < c and b < c
```

whose standard proof goes through Cantor normal form, which this development
does not have. Raising to `ω` was a way of buying one property: *replacing one
thing by two strictly smaller things must lower the measure.*

## What works: order the birthdays as a multiset

That property is the definition of the Dershowitz–Manna order, so take it
directly instead of buying it. A number contributes its birthday, and an
obligation contributes the multiset of birthdays it mentions:

```
tripleMeasure a b c = {ba, bb, bc}
pairMeasure  x y   = {bx, by}
```

`Multiset.IsDershowitzMannaLT M N` holds when `M` is `N` with some elements
replaced by finitely many strictly smaller ones; it is well founded over any
well-founded order (`Multiset.wellFounded_isDershowitzMannaLT`), and `Ordinal`
is one. Each of the five decreases is then an instance of that definition:

* `tripleMeasure_lt_of_second`, `tripleMeasure_lt_of_first` — replace one birthday
  by a smaller one;
* `pairMeasure_lt_tripleMeasure_right`, `pairMeasure_lt_tripleMeasure_left` — drop a
  birthday, which is replacing it by nothing;
* `tripleMeasure_lt_pairMeasure` — **replace `bx` by the two option birthdays `bl`
  and `br`**, which is the case this order exists for, and the one that every
  ordinal-valued candidate failed.

No hypotheses, no ordinal lemma, no lexicographic tag.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open Multiset

/-! ## The two measures -/

/-- The birthdays of three numbers, as a multiset. This is the measure of the
monotonicity obligation `Mono a b c`, and later of the associativity obligation
at `(x, y, z)` — both recurse by replacing one of three numbers with younger
ones, so they take the same order. -/
noncomputable def tripleMeasure (a b c : Surreal) : Multiset Ordinal.{0} :=
  {birthday a} + {birthday b} + {birthday c}

/-- The birthdays of two numbers: the measure of a separation obligation
`Sep x y`. -/
noncomputable def pairMeasure (x y : Surreal) : Multiset Ordinal.{0} :=
  {birthday x} + {birthday y}

/-! ## The five decreases -/

/-- **`Mono a b c → Mono a l c`** for `l` an option of `b`: one birthday is
replaced by a smaller one. -/
theorem tripleMeasure_lt_of_second {a b c l : Surreal}
    (h : birthday l < birthday b) :
    IsDershowitzMannaLT (tripleMeasure a l c) (tripleMeasure a b c) := by
  refine ⟨{birthday a} + {birthday c}, {birthday l}, {birthday b}, by simp, ?_, ?_, ?_⟩
  · simp only [tripleMeasure]; abel
  · simp only [tripleMeasure]; abel
  · intro y hy
    rw [Multiset.mem_singleton] at hy
    exact ⟨birthday b, Multiset.mem_singleton_self _, hy ▸ h⟩

/-- **`Mono a b c → Mono r b c`** for `r` an option of `a`. -/
theorem tripleMeasure_lt_of_first {a b c r : Surreal}
    (h : birthday r < birthday a) :
    IsDershowitzMannaLT (tripleMeasure r b c) (tripleMeasure a b c) := by
  refine ⟨{birthday b} + {birthday c}, {birthday r}, {birthday a}, by simp, ?_, ?_, ?_⟩
  · simp only [tripleMeasure]; abel
  · simp only [tripleMeasure]; abel
  · intro y hy
    rw [Multiset.mem_singleton] at hy
    exact ⟨birthday a, Multiset.mem_singleton_self _, hy ▸ h⟩

/-- **Replacing the third entry by a younger number.**  Monotonicity never
touches its third argument, but associativity recurses in all three slots, so
it needs this one too. -/
theorem tripleMeasure_lt_of_third {a b c w : Surreal}
    (h : birthday w < birthday c) :
    IsDershowitzMannaLT (tripleMeasure a b w) (tripleMeasure a b c) := by
  refine ⟨{birthday a} + {birthday b}, {birthday w}, {birthday c}, by simp, ?_, ?_, ?_⟩
  · simp only [tripleMeasure]
  · simp only [tripleMeasure]
  · intro y hy
    rw [Multiset.mem_singleton] at hy
    exact ⟨birthday c, Multiset.mem_singleton_self _, hy ▸ h⟩

/-- **`Mono a b c → Sep b c`**: a birthday is dropped, which is replacing it by
nothing at all. -/
theorem pairMeasure_lt_tripleMeasure_right (a b c : Surreal) :
    IsDershowitzMannaLT (pairMeasure b c) (tripleMeasure a b c) := by
  refine ⟨{birthday b} + {birthday c}, 0, {birthday a}, by simp, ?_, ?_, ?_⟩
  · simp only [pairMeasure]; abel
  · simp only [tripleMeasure]; abel
  · intro y hy
    exact absurd hy (by simp)

/-- **`Mono a b c → Sep a c`.** -/
theorem pairMeasure_lt_tripleMeasure_left (a b c : Surreal) :
    IsDershowitzMannaLT (pairMeasure a c) (tripleMeasure a b c) := by
  refine ⟨{birthday a} + {birthday c}, 0, {birthday b}, by simp, ?_, ?_, ?_⟩
  · simp only [pairMeasure]; abel
  · simp only [tripleMeasure]; abel
  · intro y hy
    exact absurd hy (by simp)

/-- **`Sep x y → Mono l r y`** for `l` and `r` options of `x`: the single
birthday `bx` is replaced by the two smaller birthdays `bl` and `br`.

This is the step every ordinal-valued candidate failed, and it is exactly the
case the Dershowitz–Manna order is designed for. It needs nothing about
ordinal arithmetic — only that both options are younger than `x`. -/
theorem tripleMeasure_lt_pairMeasure {x y l r : Surreal}
    (hl : birthday l < birthday x) (hr : birthday r < birthday x) :
    IsDershowitzMannaLT (tripleMeasure l r y) (pairMeasure x y) := by
  refine ⟨{birthday y}, {birthday l} + {birthday r}, {birthday x}, by simp, ?_, ?_, ?_⟩
  · simp only [tripleMeasure]; abel
  · simp only [pairMeasure]; abel
  · intro z hz
    refine ⟨birthday x, Multiset.mem_singleton_self _, ?_⟩
    rcases Multiset.mem_add.mp hz with hz' | hz'
    · rw [Multiset.mem_singleton] at hz'; exact hz' ▸ hl
    · rw [Multiset.mem_singleton] at hz'; exact hz' ▸ hr

/-! ## The order is well founded -/

/-- **So the induction terminates.**  Ordinals are well founded, hence so are
multisets of ordinals under this order. -/
theorem measure_wellFounded :
    WellFounded (IsDershowitzMannaLT (α := Ordinal.{0})) :=
  Multiset.wellFounded_isDershowitzMannaLT

/-! ## Option birthdays are smaller -/

theorem birthday_lt_of_mem_leftOptions {x l : Surreal} (h : l ∈ leftOptions x) :
    birthday l < birthday x := h.2

theorem birthday_lt_of_mem_rightOptions {x r : Surreal} (h : r ∈ rightOptions x) :
    birthday r < birthday x := h.2

/-- The form the induction actually calls: both options of `x`, at once. -/
theorem tripleMeasure_lt_pairMeasure_of_mem {x y l r : Surreal}
    (hl : l ∈ leftOptions x) (hr : r ∈ rightOptions x) :
    IsDershowitzMannaLT (tripleMeasure l r y) (pairMeasure x y) :=
  tripleMeasure_lt_pairMeasure hl.2 hr.2

/-! ## The second summand

A sum is symmetric, so the induction meets each shape twice — once with the
options coming from the left summand, once from the right. These are the
mirrored decreases. -/

theorem pairMeasure_comm (x y : Surreal) : pairMeasure x y = pairMeasure y x := by
  simp only [pairMeasure]; abel

/-- **`Sep x y → Mono l r x`** for `l` and `r` options of the *second*
summand. -/
theorem tripleMeasure_lt_pairMeasure_right {x y l r : Surreal}
    (hl : birthday l < birthday y) (hr : birthday r < birthday y) :
    IsDershowitzMannaLT (tripleMeasure l r x) (pairMeasure x y) := by
  rw [pairMeasure_comm]
  exact tripleMeasure_lt_pairMeasure hl hr

/-- **`Sep x y → Sep u y`** for `u` an option of `x`: the cross cases of the
separation argument recurse into a separation, not a monotonicity. -/
theorem pairMeasure_lt_pairMeasure_left {x y u : Surreal}
    (h : birthday u < birthday x) :
    IsDershowitzMannaLT (pairMeasure u y) (pairMeasure x y) := by
  refine ⟨{birthday y}, {birthday u}, {birthday x}, by simp, ?_, ?_, ?_⟩
  · simp only [pairMeasure]; abel
  · simp only [pairMeasure]; abel
  · intro z hz
    rw [Multiset.mem_singleton] at hz
    exact ⟨birthday x, Multiset.mem_singleton_self _, hz ▸ h⟩

/-- **`Sep x y → Sep x v`** for `v` an option of `y`. -/
theorem pairMeasure_lt_pairMeasure_right {x y v : Surreal}
    (h : birthday v < birthday y) :
    IsDershowitzMannaLT (pairMeasure x v) (pairMeasure x y) := by
  refine ⟨{birthday x}, {birthday v}, {birthday y}, by simp, ?_, ?_, ?_⟩
  · simp only [pairMeasure]
  · simp only [pairMeasure]
  · intro z hz
    rw [Multiset.mem_singleton] at hz
    exact ⟨birthday y, Multiset.mem_singleton_self _, hz ▸ h⟩

/-! ## Controls -/

namespace AdditionMeasureControls

open Mettapedia.SetTheory.OrdinalArithmetic

/-- The maximum measure really does stall where claimed. -/
theorem max_measure_stalls : ((1 : Ordinal) ⊔ 0) = ((1 : Ordinal) ⊔ 1) := by simp

/-- And the plain natural sum of birthdays really does stall: two options born
on day `1` already reach the parent's day `2`. -/
theorem birthday_sum_stalls : ¬ (naturalAdd (1 : Ordinal.{0}) 1 < 1 + 1) :=
  NaturalSumControls.nadd_measure_fails

/-- The `Sep → Mono` step *grows* the multiset while lowering it in the order,
which is why cardinality could never have been the measure — and why an
ordinal-valued measure had to buy the property this order gives away. -/
theorem sep_to_mono_grows (x y l r : Surreal) :
    Multiset.card (tripleMeasure l r y) = Multiset.card (pairMeasure x y) + 1 := by
  simp [tripleMeasure, pairMeasure]

/-- **The order is not vacuous in the direction that matters**: one element
really can be replaced by *two* strictly smaller ones and still go down. This
is the `Sep → Mono` shape in miniature, and it is what no ordinal-valued
measure gave for free. -/
theorem two_below_one :
    IsDershowitzMannaLT ({0, 0} : Multiset Ordinal.{0}) ({1} : Multiset Ordinal.{0}) := by
  refine ⟨0, {0, 0}, {1}, by simp, by simp, by simp, ?_⟩
  intro y hy
  refine ⟨1, Multiset.mem_singleton_self _, ?_⟩
  rcases Multiset.mem_cons.mp hy with h | h
  · subst h; exact zero_lt_one
  · rw [Multiset.mem_singleton] at h; subst h; exact zero_lt_one

/-- **And it is not degenerate**: the reverse replacement, by something
*larger*, is not a decrease. Without this the order could be trivial. -/
theorem not_larger_below :
    ¬ IsDershowitzMannaLT ({1} : Multiset Ordinal.{0}) ({0, 0} : Multiset Ordinal.{0}) :=
  measure_wellFounded.asymmetric _ _ two_below_one

end AdditionMeasureControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.tripleMeasure_lt_of_second
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.tripleMeasure_lt_of_first
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.pairMeasure_lt_tripleMeasure_right
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.pairMeasure_lt_tripleMeasure_left
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.tripleMeasure_lt_pairMeasure
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.measure_wellFounded
