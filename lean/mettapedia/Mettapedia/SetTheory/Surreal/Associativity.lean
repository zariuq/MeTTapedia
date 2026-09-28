import Mettapedia.SetTheory.Surreal.AdditiveInverse

/-!
# Associativity

`(x + y) + z = x + (y + z)`, by induction on the multiset of the three
birthdays.

## The obstacle, and the bridge over it

Both sides are cuts, so `IsCut.eq_of_between` reduces the identity to showing
that each side separates the other's option families. Doing that means knowing
what the options of `(x + y) + z` are — and here the recursion does *not* hand
them over. `add` is defined against the **canonical** options of its arguments,
every younger number on the correct side, so the left options of `(x + y) + z`
are `w + z` for `w` any number younger than and below `x + y`. They are not the
four Conway forms.

The bridge is cofinality. `x + y` is the cut of `leftSum x y`, so by
`IsCut.left_cofinal` every canonical left option `w` of `x + y` is dominated by
some `l ∈ leftSum x y` — that is, by an honest `xᴸ + y` or `x + yᴸ`. Weak
monotonicity then lifts `w + z ≤ l + z`, and `l + z` is a Conway form the
induction hypothesis can rewrite:

```
w + z  ≤  (xᴸ + y) + z  =  xᴸ + (y + z)  <  x + (y + z)
w + z  ≤  (x + yᴸ) + z  =  x + (yᴸ + z)  <  x + (y + z)
```

The first ends at a *left option* of `x + (y + z)`; the second ends by
monotonicity applied twice. The remaining left option, `(x + y) + zᴸ`, rewrites
directly.

So associativity needs cofinality, weak monotonicity and strict monotonicity —
all of which are now available — and nothing else.

## The measure

The induction hypothesis is used at `(xᴸ, y, z)`, `(x, yᴸ, z)` and `(x, y, zᴸ)`
and their right-hand mirrors: each replaces exactly one of the three numbers by
a younger one, which is a decrease of `tripleMeasure` in the Dershowitz–Manna
order. It is the same order the separation induction ran on, for the same
reason.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open Multiset

/-- **Addition is associative.** -/
theorem add_assoc' (x y z : Surreal) :
    add (add x y) z = add x (add y z) := by
  refine (InvImage.wf
      (fun t : Surreal × Surreal × Surreal => tripleMeasure t.1 t.2.1 t.2.2)
      measure_wellFounded).induction
    (C := fun t : Surreal × Surreal × Surreal =>
      add (add t.1 t.2.1) t.2.2 = add t.1 (add t.2.1 t.2.2)) (x, y, z) ?_
  clear x y z
  rintro ⟨x, y, z⟩ ih
  simp only at ih ⊢
  have hA : IsCut (leftSum (add x y) z) (rightSum (add x y) z) (add (add x y) z) :=
    isCut_add' (add x y) z
  have hB : IsCut (leftSum x (add y z)) (rightSum x (add y z)) (add x (add y z)) :=
    isCut_add' x (add y z)
  refine hA.eq_of_between hB ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · -- Every left option of `(x + y) + z` is below `x + (y + z)`.
    intro p hp
    rcases mem_leftSum_cases hp with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · obtain ⟨l, hl, hwl⟩ := (isCut_add' x y).left_cofinal hw
      refine lt_of_le_of_lt (add_le_add_right hwl z) ?_
      rcases mem_leftSum_cases hl with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · rw [ih (u, y, z) (tripleMeasure_lt_of_first hu.2)]
        exact hB.left _ (add_mem_leftSum_left hu)
      · rw [ih (x, u, z) (tripleMeasure_lt_of_second hu.2)]
        exact add_lt_add_left (add_lt_add_right hu.1 z) x
    · rw [ih (x, y, w) (tripleMeasure_lt_of_third hw.2)]
      exact add_lt_add_left (add_lt_add_left hw.1 y) x
  · -- Every right option of `(x + y) + z` is above `x + (y + z)`.
    intro p hp
    rcases mem_rightSum_cases hp with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · obtain ⟨r, hr, hrw⟩ := (isCut_add' x y).right_coinitial hw
      refine lt_of_lt_of_le ?_ (add_le_add_right hrw z)
      rcases mem_rightSum_cases hr with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · rw [ih (v, y, z) (tripleMeasure_lt_of_first hv.2)]
        exact hB.right _ (add_mem_rightSum_left hv)
      · rw [ih (x, v, z) (tripleMeasure_lt_of_second hv.2)]
        exact add_lt_add_left (add_lt_add_right hv.1 z) x
    · rw [ih (x, y, w) (tripleMeasure_lt_of_third hw.2)]
      exact add_lt_add_left (add_lt_add_left hw.1 y) x
  · -- Every left option of `x + (y + z)` is below `(x + y) + z`.
    intro p hp
    rcases mem_leftSum_cases hp with ⟨u, hu, rfl⟩ | ⟨w, hw, rfl⟩
    · rw [← ih (u, y, z) (tripleMeasure_lt_of_first hu.2)]
      exact add_lt_add_right (add_lt_add_right hu.1 y) z
    · obtain ⟨l, hl, hwl⟩ := (isCut_add' y z).left_cofinal hw
      refine lt_of_le_of_lt (add_le_add_left hwl x) ?_
      rcases mem_leftSum_cases hl with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · rw [← ih (x, u, z) (tripleMeasure_lt_of_second hu.2)]
        exact add_lt_add_right (add_lt_add_left hu.1 x) z
      · rw [← ih (x, y, u) (tripleMeasure_lt_of_third hu.2)]
        exact add_lt_add_left hu.1 (add x y)
  · -- Every right option of `x + (y + z)` is above `(x + y) + z`.
    intro p hp
    rcases mem_rightSum_cases hp with ⟨v, hv, rfl⟩ | ⟨w, hw, rfl⟩
    · rw [← ih (v, y, z) (tripleMeasure_lt_of_first hv.2)]
      exact add_lt_add_right (add_lt_add_right hv.1 y) z
    · obtain ⟨r, hr, hrw⟩ := (isCut_add' y z).right_coinitial hw
      refine lt_of_lt_of_le ?_ (add_le_add_left hrw x)
      rcases mem_rightSum_cases hr with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · rw [← ih (x, v, z) (tripleMeasure_lt_of_second hv.2)]
        exact add_lt_add_right (add_lt_add_left hv.1 x) z
      · rw [← ih (x, y, v) (tripleMeasure_lt_of_third hv.2)]
        exact add_lt_add_left hv.1 (add x y)

/-! ## The laws that follow -/

theorem add_left_comm' (x y z : Surreal) :
    add x (add y z) = add y (add x z) := by
  rw [← add_assoc', ← add_assoc', add_comm' x y]

theorem add_right_comm' (x y z : Surreal) :
    add (add x y) z = add (add x z) y := by
  rw [add_assoc', add_assoc', add_comm' y z]

/-- **Cancelling an inverse on the right.** -/
theorem add_neg_cancel_right (x y : Surreal) : add (add x y) (-y) = x := by
  rw [add_assoc', add_neg_self, add_zero']

theorem add_neg_cancel_left (x y : Surreal) : add (-x) (add x y) = y := by
  rw [← add_assoc', neg_add_self, zero_add']

theorem sub_add_cancel (x y : Surreal) : add (sub x y) y = x := by
  rw [sub, add_assoc', neg_add_self, add_zero']

theorem add_sub_cancel (x y : Surreal) : sub (add x y) y = x :=
  add_neg_cancel_right x y

/-- **Negation reverses a sum.** -/
theorem neg_add' (x y : Surreal) : -(add x y) = add (-x) (-y) := neg_add x y

/-! ## Controls -/

namespace AssociativityControls

/-- Associativity at three numbers that are genuinely distinct, rather than at
`0` where it would follow from the unit laws alone. -/
theorem assoc_half_one_zero :
    add (add (mk (dyadicPre 1)) (ofNat 1)) 0
      = add (mk (dyadicPre 1)) (add (ofNat 1) 0) :=
  add_assoc' _ _ _

/-- **Negative control**: associativity does not make addition commute with
*itself* in the wrong slot — regrouping is an equality, but reordering
distinct summands changes which sum is which only when they differ, and here
`1/2 + 1 ≠ 1/2 + 1/2`. -/
theorem regroup_not_collapse :
    add (mk (dyadicPre 1)) (ofNat 1) ≠ add (mk (dyadicPre 1)) (mk (dyadicPre 1)) := by
  intro h
  have : ofNat 1 = mk (dyadicPre 1) := add_left_cancel h
  refine absurd this (ne_of_gt ?_)
  rw [← dyadic_zero_eq_one]
  exact dyadic_anti 0

/-- The cancellation laws are exercised where the cancelled term is not `0`. -/
theorem cancel_half : add (add (ofNat 1) (mk (dyadicPre 1))) (-(mk (dyadicPre 1)))
    = ofNat 1 :=
  add_neg_cancel_right _ _

end AssociativityControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.add_assoc'
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.add_neg_cancel_right
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.sub_add_cancel
