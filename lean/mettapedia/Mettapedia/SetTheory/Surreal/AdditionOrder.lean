import Mettapedia.SetTheory.Surreal.AdditionMeasure

/-!
# Separation and order compatibility, proved together

This discharges the obligation `Addition.lean` left open. `add_eq_cut` there
says the sum is Conway's cut *wherever its option families are separated*; here
they are shown to be separated always, so the recursion is the cut everywhere
and never the junk branch.

Separation and strict monotonicity have to be proved at the same time, because
each needs the other, and `AdditionMeasure.lean` supplies the order that makes
the mutual recursion terminate. The two statements are packaged as one
inductive `Obligation` so that a single well-founded induction serves both.

## The shape of the argument

**Separation** of `x + y` means every left option beats no right option, and
there are four combinations. Two of them mix the summands:

```
xᴸ + y  <  x + yᴿ        xᴸ ∈ L(x),  yᴿ ∈ R(y)
x + yᴸ  <  xᴿ + y        yᴸ ∈ L(y),  xᴿ ∈ R(x)
```

These need **no monotonicity at all**, which is the observation that makes the
whole induction go through. The number `xᴸ + yᴿ` is at once a *right* option of
`xᴸ + y` and a *left* option of `x + yᴿ`, so it sits between them:

```
xᴸ + y  <  xᴸ + yᴿ  <  x + yᴿ
```

and each of those two steps is just "a number is strictly inside its own cut",
available from the separation of the smaller pairs `(xᴸ, y)` and `(x, yᴿ)`.

The other two combinations keep one summand fixed:

```
xᴸ + y < xᴿ + y        x + yᴸ < x + yᴿ
```

and those are exactly monotonicity, at arguments both of which are younger than
the fixed summand — the one case the multiset order was chosen for.

**Monotonicity** `a < b → a + c < b + c` runs the other way. From
`exists_option_between`, either some left option of `b` is at least `a`, or some
right option of `a` is at most `b`; in the first case

```
a + c  ≤  bᴸ + c  <  b + c
```

where the strict step is `b + c` being inside its own cut — separation at
`(b, c)` — and the weak step is monotonicity at `(a, bᴸ, c)`, which has replaced
`b` by something younger. The second case is the mirror image.

Every recursive call is one of the five decreases proved in
`AdditionMeasure.lean`, and there are no others.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open Multiset

/-! ## Options of a sum

The four ways a number can be an option of `x + y`, in both directions. -/

theorem add_mem_leftSum_left {x y u : Surreal} (hu : u ∈ leftOptions x) :
    add u y ∈ leftSum x y :=
  Set.mem_union_left _ (Set.mem_range_self (⟨u, hu⟩ : leftOptions x))

theorem add_mem_leftSum_right {x y u : Surreal} (hu : u ∈ leftOptions y) :
    add x u ∈ leftSum x y :=
  Set.mem_union_right _ (Set.mem_range_self (⟨u, hu⟩ : leftOptions y))

theorem add_mem_rightSum_left {x y v : Surreal} (hv : v ∈ rightOptions x) :
    add v y ∈ rightSum x y :=
  Set.mem_union_left _ (Set.mem_range_self (⟨v, hv⟩ : rightOptions x))

theorem add_mem_rightSum_right {x y v : Surreal} (hv : v ∈ rightOptions y) :
    add x v ∈ rightSum x y :=
  Set.mem_union_right _ (Set.mem_range_self (⟨v, hv⟩ : rightOptions y))

theorem mem_leftSum_cases {x y z : Surreal} (hz : z ∈ leftSum x y) :
    (∃ u ∈ leftOptions x, z = add u y) ∨ (∃ u ∈ leftOptions y, z = add x u) := by
  simp only [leftSum, Set.mem_union, Set.mem_range, Subtype.exists] at hz
  rcases hz with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
  · exact Or.inl ⟨u, hu, rfl⟩
  · exact Or.inr ⟨u, hu, rfl⟩

theorem mem_rightSum_cases {x y z : Surreal} (hz : z ∈ rightSum x y) :
    (∃ v ∈ rightOptions x, z = add v y) ∨ (∃ v ∈ rightOptions y, z = add x v) := by
  simp only [rightSum, Set.mem_union, Set.mem_range, Subtype.exists] at hz
  rcases hz with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · exact Or.inl ⟨v, hv, rfl⟩
  · exact Or.inr ⟨v, hv, rfl⟩

/-! ## Reaching across a strict inequality

The step that replaces Conway's game-level case analysis. Between any two
numbers there is always a *younger* witness on one side or the other, because
otherwise each would be a separator for the other's cut and they would have to
coincide. -/

/-- **From `a < b`, either `b` has a left option at least `a`, or `a` has a
right option at most `b`.**

Without it, monotonicity would have nowhere to recurse: `a` and `b` are
unrelated in age, so neither is an option of the other in general. -/
theorem exists_option_between {a b : Surreal} (hab : a < b) :
    (∃ l ∈ leftOptions b, a ≤ l) ∨ (∃ r ∈ rightOptions a, r ≤ b) := by
  by_contra hcon
  have hLb : ∀ z ∈ leftOptions b, z < a := by
    intro z hz
    by_contra hz'
    exact hcon (Or.inl ⟨z, hz, not_lt.mp hz'⟩)
  have hRa : ∀ z ∈ rightOptions a, b < z := by
    intro z hz
    by_contra hz'
    exact hcon (Or.inr ⟨z, hz, not_lt.mp hz'⟩)
  have hba : birthday a ≤ birthday b :=
    birthday_le_of_between (fun z hz => hz.1.trans hab) hRa
  have heq : a = b :=
    eq_of_between_of_birthday_le hLb (fun z hz => hab.trans hz.1) hba
  exact absurd heq (ne_of_lt hab)

/-! ## The two statements, as one -/

/-- One obligation of the simultaneous induction: either a monotonicity step or
a separation step. -/
inductive Obligation : Type 1
  | mono (a b c : Surreal) : Obligation
  | sep (x y : Surreal) : Obligation

/-- Its position in the well-founded order. -/
noncomputable def Obligation.measure : Obligation → Multiset Ordinal.{0}
  | .mono a b c => tripleMeasure a b c
  | .sep x y => pairMeasure x y

/-- What the obligation asserts. -/
def Obligation.holds : Obligation → Prop
  | .mono a b c => a < b → add a c < add b c
  | .sep x y => Separated (leftSum x y) (rightSum x y)

/-- **The simultaneous induction.**  Every obligation holds. -/
theorem obligation_holds (o : Obligation) : o.holds := by
  refine (InvImage.wf Obligation.measure measure_wellFounded).induction o ?_
  clear o
  rintro (⟨a, b, c⟩ | ⟨x, y⟩) ih
  · -- Monotonicity at `(a, b, c)`.
    intro hab
    rcases exists_option_between hab with ⟨l, hl, hal⟩ | ⟨r, hr, hrb⟩
    · -- `a ≤ bᴸ`, so step up through `bᴸ + c`, which is a left option of `b + c`.
      have hsep : Separated (leftSum b c) (rightSum b c) :=
        ih (.sep b c) (pairMeasure_lt_tripleMeasure_right a b c)
      have hstrict : add l c < add b c :=
        (isCut_add b c hsep).left _ (add_mem_leftSum_left hl)
      rcases eq_or_lt_of_le hal with rfl | hlt
      · exact hstrict
      · exact lt_trans (ih (.mono a l c) (tripleMeasure_lt_of_second hl.2) hlt) hstrict
    · -- `aᴿ ≤ b`, so step up through `aᴿ + c`, a right option of `a + c`.
      have hsep : Separated (leftSum a c) (rightSum a c) :=
        ih (.sep a c) (pairMeasure_lt_tripleMeasure_left a b c)
      have hstrict : add a c < add r c :=
        (isCut_add a c hsep).right _ (add_mem_rightSum_left hr)
      rcases eq_or_lt_of_le hrb with rfl | hlt
      · exact hstrict
      · exact lt_trans hstrict (ih (.mono r b c) (tripleMeasure_lt_of_first hr.2) hlt)
  · -- Separation at `(x, y)`.
    intro p hp q hq
    rcases mem_leftSum_cases hp with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;>
      rcases mem_rightSum_cases hq with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · -- `xᴸ + y < xᴿ + y`: monotonicity, both arguments younger than `x`.
      exact ih (.mono u v y) (tripleMeasure_lt_pairMeasure hu.2 hv.2)
        (hu.1.trans hv.1)
    · -- `xᴸ + y < x + yᴿ`: bridged by `xᴸ + yᴿ`, no monotonicity.
      have h₁ : add u y < add u v :=
        (isCut_add u y (ih (.sep u y) (pairMeasure_lt_pairMeasure_left hu.2))).right _
          (add_mem_rightSum_right hv)
      have h₂ : add u v < add x v :=
        (isCut_add x v (ih (.sep x v) (pairMeasure_lt_pairMeasure_right hv.2))).left _
          (add_mem_leftSum_left hu)
      exact h₁.trans h₂
    · -- `x + yᴸ < xᴿ + y`: bridged by `xᴿ + yᴸ`.
      have h₁ : add x u < add v u :=
        (isCut_add x u (ih (.sep x u) (pairMeasure_lt_pairMeasure_right hu.2))).right _
          (add_mem_rightSum_left hv)
      have h₂ : add v u < add v y :=
        (isCut_add v y (ih (.sep v y) (pairMeasure_lt_pairMeasure_left hv.2))).left _
          (add_mem_leftSum_right hu)
      exact h₁.trans h₂
    · -- `x + yᴸ < x + yᴿ`: monotonicity in the second summand.
      rw [add_comm' x u, add_comm' x v]
      exact ih (.mono u v x) (tripleMeasure_lt_pairMeasure_right hu.2 hv.2)
        (hu.1.trans hv.1)

/-! ## What the induction gives -/

/-- **The sum's option families are always separated.**  This is the obligation
`Addition.lean` left open. -/
theorem separated_sum (x y : Surreal) : Separated (leftSum x y) (rightSum x y) :=
  obligation_holds (.sep x y)

/-- **So the sum really is Conway's cut**, for every pair, with no side
condition. -/
theorem add_eq_cut' (x y : Surreal) :
    add x y = cut (leftSum x y) (rightSum x y) (separated_sum x y)
      (bddAbove_sum_options x y) :=
  add_eq_cut x y (separated_sum x y)

/-- And it is the simplest number strictly between its options. -/
theorem isCut_add' (x y : Surreal) : IsCut (leftSum x y) (rightSum x y) (add x y) :=
  isCut_add x y (separated_sum x y)

/-- **Strict monotonicity in the first summand.** -/
theorem add_lt_add_right {a b : Surreal} (h : a < b) (c : Surreal) :
    add a c < add b c :=
  obligation_holds (.mono a b c) h

/-- **Strict monotonicity in the second summand.** -/
theorem add_lt_add_left {a b : Surreal} (h : a < b) (c : Surreal) :
    add c a < add c b := by
  rw [add_comm' c a, add_comm' c b]
  exact add_lt_add_right h c

/-! ## The order laws that follow at once -/

theorem add_lt_add_right_iff {a b c : Surreal} : add a c < add b c ↔ a < b := by
  refine ⟨fun h => ?_, fun h => add_lt_add_right h c⟩
  by_contra hcon
  rcases lt_or_eq_of_le (not_lt.mp hcon) with hlt | rfl
  · exact absurd (h.trans (add_lt_add_right hlt c)) (lt_irrefl _)
  · exact absurd h (lt_irrefl _)

theorem add_lt_add_left_iff {a b c : Surreal} : add c a < add c b ↔ a < b := by
  rw [add_comm' c a, add_comm' c b]; exact add_lt_add_right_iff

theorem add_le_add_right {a b : Surreal} (h : a ≤ b) (c : Surreal) :
    add a c ≤ add b c := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · exact le_of_lt (add_lt_add_right hlt c)
  · exact le_refl _

theorem add_le_add_left {a b : Surreal} (h : a ≤ b) (c : Surreal) :
    add c a ≤ add c b := by
  rw [add_comm' c a, add_comm' c b]; exact add_le_add_right h c

theorem add_le_add_right_iff {a b c : Surreal} : add a c ≤ add b c ↔ a ≤ b := by
  refine ⟨fun h => ?_, fun h => add_le_add_right h c⟩
  by_contra hcon
  exact absurd (add_lt_add_right (not_le.mp hcon) c) (not_lt.mpr h)

theorem add_le_add_left_iff {a b c : Surreal} : add c a ≤ add c b ↔ a ≤ b := by
  rw [add_comm' c a, add_comm' c b]; exact add_le_add_right_iff

/-- **Cancellation on the right**, a consequence of strictness rather than of
an inverse — the inverse is a later obligation. -/
theorem add_right_cancel {a b c : Surreal} (h : add a c = add b c) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (ne_of_lt (add_lt_add_right hlt c))
  · exact heq
  · exact absurd h.symm (ne_of_lt (add_lt_add_right hgt c))

theorem add_left_cancel {a b c : Surreal} (h : add c a = add c b) : a = b := by
  rw [add_comm' c a, add_comm' c b] at h
  exact add_right_cancel h

theorem add_right_injective (c : Surreal) : Function.Injective (fun a => add a c) :=
  fun _ _ h => add_right_cancel h

/-! ## Controls -/

namespace AdditionOrderControls

/-- The reaching lemma is not vacuous at a pair where neither number is an
option of the other: `0 < 1/2` is witnessed on the left, since `0` is itself a
left option of `1/2`. -/
theorem reach_zero_half :
    (∃ l ∈ leftOptions (mk (dyadicPre 1)), (0 : Surreal) ≤ l) ∨
      (∃ r ∈ rightOptions (0 : Surreal), r ≤ mk (dyadicPre 1)) :=
  exists_option_between (dyadic_pos 1)

/-- And at `1/2 < 1` the witness has to be the *right*-hand one. `1` is younger
than `1/2`, so `1/2` is not a left option of `1` however close it is; it is `1`
that is a right option of `1/2`. This is the case that rules out the naive
"take a left option of the larger" reading, and the reason the lemma is a
disjunction at all. -/
theorem reach_half_one_is_on_the_right :
    mk (dyadicPre 1) ∉ leftOptions (mk (dyadicPre 0)) ∧
      mk (dyadicPre 0) ∈ rightOptions (mk (dyadicPre 1)) := by
  refine ⟨?_, CutControls.one_mem_rightOptions_half⟩
  rintro ⟨-, hb⟩
  rw [birthday_mk, birthday_mk, dyadicPre_length, dyadicPre_length,
    Nat.cast_zero, Nat.cast_one, zero_add] at hb
  exact absurd hb (not_lt.mpr (le_of_lt (lt_add_one 1)))

/-- Monotonicity is exercised where the summands genuinely differ. -/
theorem zero_add_lt_half_add : add 0 (0 : Surreal) < add (mk (dyadicPre 1)) 0 :=
  add_lt_add_right (dyadic_pos 1) 0

/-- **Negative control**: the strict order is not collapsed — equal summands do
not compare strictly. -/
theorem not_add_lt_self (x c : Surreal) : ¬ add x c < add x c := lt_irrefl _

/-- **Negative control**: monotonicity reflects as well as preserves, so a
false comparison is refused rather than manufactured. -/
theorem not_add_lt_of_not_lt :
    ¬ add (mk (dyadicPre 1)) 0 < add 0 0 := by
  rw [add_lt_add_right_iff]
  exact not_lt.mpr (le_of_lt (dyadic_pos 1))

end AdditionOrderControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.exists_option_between
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.obligation_holds
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.separated_sum
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.add_lt_add_right
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.add_right_cancel
