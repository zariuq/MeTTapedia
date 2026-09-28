import Mathlib.SetTheory.Ordinal.Family

/-!
# The natural sum of ordinals

Ordinal addition is strictly monotone in its right argument and **not** in its
left: `0 + ω = 1 + ω`. That is fatal for any recursion whose measure must fall
when *either* of two arguments is replaced by something smaller — which is the
situation in every simultaneous induction over several ordinals at once.

The natural (Hessenberg) sum repairs exactly that. It is defined by the
recursion

```
a ⊕ b = max ( sup_{a' < a} (a' ⊕ b) + 1 , sup_{b' < b} (a ⊕ b') + 1 )
```

and strict monotonicity in each argument is immediate from the definition:
replacing an argument by a smaller one produces a term that the supremum
already dominates, with a successor to spare.

Only what a recursion needs is proved here: the operation exists, it is
strictly monotone in each argument separately, and it is monotone in the weak
sense. Commutativity and associativity are true and are not needed, so they
are not claimed.

The suprema are legitimate because `Set.Iio a` is small, so upstream's
`Ordinal.le_iSup` and `Ordinal.iSup_le` apply.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OrdinalArithmetic

open Ordinal

universe u

/-- The natural (Hessenberg) sum: the least ordinal strictly above every
natural sum obtained by lowering one argument. -/
noncomputable def naturalAdd : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | a, b =>
      max (⨆ x : Set.Iio a, naturalAdd x.1 b + 1)
        (⨆ y : Set.Iio b, naturalAdd a y.1 + 1)
termination_by a b => (a, b)
decreasing_by
  · exact Prod.Lex.left _ _ x.2
  · exact Prod.Lex.right _ y.2

theorem naturalAdd_def (a b : Ordinal.{u}) :
    naturalAdd a b =
      max (⨆ x : Set.Iio a, naturalAdd x.1 b + 1)
        (⨆ y : Set.Iio b, naturalAdd a y.1 + 1) := by
  rw [naturalAdd]

/-! ## Strict monotonicity, the property the recursions need -/

/-- **Lowering the left argument strictly lowers the sum.** -/
theorem naturalAdd_lt_naturalAdd_left {a a' b : Ordinal.{u}} (h : a' < a) :
    naturalAdd a' b < naturalAdd a b := by
  have hmem : naturalAdd a' b + 1 ≤ ⨆ x : Set.Iio a, naturalAdd x.1 b + 1 :=
    Ordinal.le_iSup (fun x : Set.Iio a => naturalAdd x.1 b + 1) ⟨a', h⟩
  calc naturalAdd a' b
      < naturalAdd a' b + 1 := lt_add_one _
    _ ≤ ⨆ x : Set.Iio a, naturalAdd x.1 b + 1 := hmem
    _ ≤ naturalAdd a b := by rw [naturalAdd_def a b]; exact le_max_left _ _

/-- **And lowering the right argument.** -/
theorem naturalAdd_lt_naturalAdd_right {a b b' : Ordinal.{u}} (h : b' < b) :
    naturalAdd a b' < naturalAdd a b := by
  have hmem : naturalAdd a b' + 1 ≤ ⨆ y : Set.Iio b, naturalAdd a y.1 + 1 :=
    Ordinal.le_iSup (fun y : Set.Iio b => naturalAdd a y.1 + 1) ⟨b', h⟩
  calc naturalAdd a b'
      < naturalAdd a b' + 1 := lt_add_one _
    _ ≤ ⨆ y : Set.Iio b, naturalAdd a y.1 + 1 := hmem
    _ ≤ naturalAdd a b := by rw [naturalAdd_def a b]; exact le_max_right _ _

/-- Both at once: lowering either argument, or both, strictly lowers the sum
unless nothing moved. -/
theorem naturalAdd_lt_naturalAdd {a a' b b' : Ordinal.{u}} (ha : a' ≤ a) (hb : b' ≤ b)
    (hne : a' < a ∨ b' < b) : naturalAdd a' b' < naturalAdd a b := by
  rcases hne with h | h
  · rcases lt_or_eq_of_le hb with hb' | rfl
    · exact (naturalAdd_lt_naturalAdd_right hb').trans (naturalAdd_lt_naturalAdd_left h)
    · exact naturalAdd_lt_naturalAdd_left h
  · rcases lt_or_eq_of_le ha with ha' | rfl
    · exact (naturalAdd_lt_naturalAdd_left ha').trans (naturalAdd_lt_naturalAdd_right h)
    · exact naturalAdd_lt_naturalAdd_right h

theorem naturalAdd_le_naturalAdd_left {a a' b : Ordinal.{u}} (h : a' ≤ a) :
    naturalAdd a' b ≤ naturalAdd a b := by
  rcases lt_or_eq_of_le h with h' | rfl
  · exact le_of_lt (naturalAdd_lt_naturalAdd_left h')
  · exact le_refl _

theorem naturalAdd_le_naturalAdd_right {a b b' : Ordinal.{u}} (h : b' ≤ b) :
    naturalAdd a b' ≤ naturalAdd a b := by
  rcases lt_or_eq_of_le h with h' | rfl
  · exact le_of_lt (naturalAdd_lt_naturalAdd_right h')
  · exact le_refl _

/-! ## The unit, and the comparison a mixed-arity measure needs -/

/-- **`0 ⊕ b = b`.**  The left supremum is over an empty family and the right
one is the supremum of successors below `b`. -/
theorem naturalAdd_zero_left (b : Ordinal.{u}) : naturalAdd 0 b = b := by
  induction b using WellFoundedLT.induction with
  | _ b ih =>
    rw [naturalAdd_def]
    have h1 : (⨆ x : Set.Iio (0 : Ordinal.{u}), naturalAdd x.1 b + 1) = 0 := by
      apply le_antisymm _ zero_le
      exact Ordinal.iSup_le fun x => absurd x.2 (by simp)
    have h2 : (⨆ y : Set.Iio b, naturalAdd 0 y.1 + 1) = b := by
      apply le_antisymm
      · refine Ordinal.iSup_le fun y => ?_
        rw [ih y.1 y.2]
        exact Order.succ_le_of_lt y.2
      · by_contra hcon
        push Not at hcon
        have hlt := Ordinal.lt_iSup_add_one
          (fun y : Set.Iio b => naturalAdd 0 y.1) ⟨_, hcon⟩
        rw [ih _ hcon] at hlt
        exact absurd hlt (lt_irrefl _)
    rw [h1, h2, max_eq_right zero_le]

/-- `a ⊕ 0 = a`, the mirror of `naturalAdd_zero_left`. -/
theorem naturalAdd_zero_right (a : Ordinal.{u}) : naturalAdd a 0 = a := by
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    rw [naturalAdd_def]
    have h2 : (⨆ y : Set.Iio (0 : Ordinal.{u}), naturalAdd a y.1 + 1) = 0 := by
      apply le_antisymm _ zero_le
      exact Ordinal.iSup_le fun y => absurd y.2 (by simp)
    have h1 : (⨆ x : Set.Iio a, naturalAdd x.1 0 + 1) = a := by
      apply le_antisymm
      · refine Ordinal.iSup_le fun x => ?_
        rw [ih x.1 x.2]
        exact Order.succ_le_of_lt x.2
      · by_contra hcon
        push Not at hcon
        have hlt := Ordinal.lt_iSup_add_one
          (fun x : Set.Iio a => naturalAdd x.1 0) ⟨_, hcon⟩
        rw [ih _ hcon] at hlt
        exact absurd hlt (lt_irrefl _)
    rw [h1, h2, max_eq_left zero_le]

/-- **A summand never exceeds the natural sum.**  This is what lets a measure
over two arguments be compared with one over three. -/
theorem le_naturalAdd_left (a b : Ordinal.{u}) : b ≤ naturalAdd a b := by
  have h := naturalAdd_le_naturalAdd_left (a := a) (a' := 0) (b := b) zero_le
  rwa [naturalAdd_zero_left] at h

/-- **A positive first summand strictly increases the sum.** -/
theorem lt_naturalAdd_right {a : Ordinal.{u}} (b : Ordinal.{u}) (ha : 0 < a) :
    b < naturalAdd a b := by
  have h := naturalAdd_lt_naturalAdd_left (a := a) (a' := 0) (b := b) ha
  rwa [naturalAdd_zero_left] at h

/-- **A positive second summand strictly increases the sum.** -/
theorem lt_naturalAdd_left {b : Ordinal.{u}} (a : Ordinal.{u}) (hb : 0 < b) :
    a < naturalAdd a b := by
  have h := naturalAdd_lt_naturalAdd_right (a := a) (b := b) (b' := 0) hb
  rwa [naturalAdd_zero_right] at h

theorem le_naturalAdd_right (a b : Ordinal.{u}) : a ≤ naturalAdd a b := by
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    by_contra hcon
    push Not at hcon
    have h1 : naturalAdd (naturalAdd a b) b + 1
        ≤ ⨆ x : Set.Iio a, naturalAdd x.1 b + 1 :=
      Ordinal.le_iSup (fun x : Set.Iio a => naturalAdd x.1 b + 1) ⟨naturalAdd a b, hcon⟩
    have h2 : (⨆ x : Set.Iio a, naturalAdd x.1 b + 1) ≤ naturalAdd a b := by
      rw [naturalAdd_def a b]; exact le_max_left _ _
    have h3 : naturalAdd a b ≤ naturalAdd (naturalAdd a b) b := ih _ hcon
    have h4 : naturalAdd (naturalAdd a b) b < naturalAdd a b :=
      lt_of_lt_of_le (lt_add_one _) (le_trans h1 h2)
    exact absurd (lt_of_lt_of_le h4 h3) (lt_irrefl _)

/-! ## Controls -/

/-! ## Finiteness

The natural sum of two finite ordinals is finite. The recursion is over both
arguments at once, so the bound is proved by strong induction on the sum of the
two naturals rather than on either alone. -/

private theorem natCast_le_aux : ∀ (s m n : ℕ), m + n ≤ s →
    naturalAdd ((m : ℕ) : Ordinal.{u}) ((n : ℕ) : Ordinal.{u})
      ≤ (((m + n : ℕ)) : Ordinal.{u}) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro m n hmn
    rw [naturalAdd_def]
    refine max_le (Ordinal.iSup_le ?_) (Ordinal.iSup_le ?_)
    · rintro ⟨x, hx⟩
      have hxlt : x < ((m : ℕ) : Ordinal.{u}) := Set.mem_Iio.mp hx
      obtain ⟨p, rfl⟩ := Ordinal.lt_omega0.mp (lt_trans hxlt (Ordinal.natCast_lt_omega0 m))
      have hp : p < m := by exact_mod_cast hxlt
      have hrec := IH (p + n) (by omega) p n (le_refl _)
      refine le_trans (add_le_add hrec (le_refl 1)) ?_
      have hnat : (p + n + 1 : ℕ) ≤ (m + n : ℕ) := by omega
      calc (((p + n : ℕ)) : Ordinal.{u}) + 1
          = (((p + n + 1 : ℕ)) : Ordinal.{u}) := (Nat.cast_succ (p + n)).symm
        _ ≤ (((m + n : ℕ)) : Ordinal.{u}) := by exact_mod_cast hnat
    · rintro ⟨y, hy⟩
      have hylt : y < ((n : ℕ) : Ordinal.{u}) := Set.mem_Iio.mp hy
      obtain ⟨q, rfl⟩ := Ordinal.lt_omega0.mp (lt_trans hylt (Ordinal.natCast_lt_omega0 n))
      have hq : q < n := by exact_mod_cast hylt
      have hrec := IH (m + q) (by omega) m q (le_refl _)
      refine le_trans (add_le_add hrec (le_refl 1)) ?_
      have hnat : (m + q + 1 : ℕ) ≤ (m + n : ℕ) := by omega
      calc (((m + q : ℕ)) : Ordinal.{u}) + 1
          = (((m + q + 1 : ℕ)) : Ordinal.{u}) := (Nat.cast_succ (m + q)).symm
        _ ≤ (((m + n : ℕ)) : Ordinal.{u}) := by exact_mod_cast hnat

/-- **Adding one is adding one.**  The natural sum agrees with ordinal
addition when the right argument is `1`, which is what a step of the integer
recursion needs.

The lower bound is immediate from `lt_naturalAdd_left`; only the upper bound
needs the recursion, and there each term of the left supremum is
`naturalAdd x 1 + 1 ≤ (x + 1) + 1 ≤ a + 1`. -/
theorem naturalAdd_one_right (a : Ordinal.{u}) : naturalAdd a 1 = a + 1 := by
  refine le_antisymm ?_ (Order.add_one_le_of_lt (lt_naturalAdd_left a zero_lt_one))
  induction a using WellFoundedLT.induction with
  | ind a IH =>
    rw [naturalAdd_def]
    refine max_le (Ordinal.iSup_le ?_) (Ordinal.iSup_le ?_)
    · rintro ⟨x, hx⟩
      have hxa : x < a := Set.mem_Iio.mp hx
      exact le_trans (add_le_add (IH x hxa) (le_refl 1))
        (add_le_add (Order.add_one_le_of_lt hxa) (le_refl 1))
    · rintro ⟨y, hy⟩
      have hy1 : y = 0 := Order.lt_one_iff.mp (Set.mem_Iio.mp hy)
      subst hy1
      rw [naturalAdd_zero_right]

/-- **The natural sum of naturals is bounded by their sum.** -/
theorem naturalAdd_natCast_le (m n : ℕ) :
    naturalAdd ((m : ℕ) : Ordinal.{u}) ((n : ℕ) : Ordinal.{u})
      ≤ (((m + n : ℕ)) : Ordinal.{u}) :=
  natCast_le_aux (m + n) m n (le_refl _)

/-- **So finiteness is preserved**, which is what the birthday of a dyadic
needs: a finite birthday plus a finite birthday stays below `ω`. -/
theorem naturalAdd_lt_omega0 {a b : Ordinal.{u}} (ha : a < Ordinal.omega0)
    (hb : b < Ordinal.omega0) : naturalAdd a b < Ordinal.omega0 := by
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp ha
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hb
  exact lt_of_le_of_lt (naturalAdd_natCast_le m n) (Ordinal.natCast_lt_omega0 _)

namespace NaturalSumControls

/-- `0 ⊕ 0 = 0`: both suprema are over empty families. -/
theorem naturalAdd_zero_zero : naturalAdd 0 0 = 0 := by
  rw [naturalAdd_def]
  have h1 : (⨆ x : Set.Iio (0 : Ordinal), naturalAdd x.1 0 + 1) = 0 := by
    apply le_antisymm _ zero_le
    exact Ordinal.iSup_le fun x => absurd x.2 (by simp)
  have h2 : (⨆ y : Set.Iio (0 : Ordinal), naturalAdd 0 y.1 + 1) = 0 := by
    apply le_antisymm _ zero_le
    exact Ordinal.iSup_le fun y => absurd y.2 (by simp)
  rw [h1, h2, max_self]

/-- **This is exactly what ordinary ordinal addition fails to do.**  Ordinal
addition is constant in its left argument here, so it could never serve as the
measure. -/
theorem ordinal_add_not_strict_left : (0 : Ordinal) + Ordinal.omega0 = 1 + Ordinal.omega0 := by
  rw [zero_add, Ordinal.one_add_omega0]

/-- Whereas the natural sum does separate them. -/
theorem naturalAdd_strict_left_here :
    naturalAdd 0 Ordinal.omega0 < naturalAdd 1 Ordinal.omega0 :=
  naturalAdd_lt_naturalAdd_left zero_lt_one

/-- **And the natural sum of two ordinals is not enough on its own** as a
recursion measure over options: two options born on day `1` already reach the
parent's day `2`, because `1 ⊕ 1 = 2`.  This is why a measure over surreal
options raises to `ω` first. -/
theorem nadd_measure_fails : ¬ (naturalAdd (1 : Ordinal.{u}) 1 < 1 + 1) := by
  have h : (1 : Ordinal.{u}) < naturalAdd 1 1 := by
    have hlt := naturalAdd_lt_naturalAdd_left
      (a := (1 : Ordinal.{u})) (a' := 0) (b := 1) zero_lt_one
    rwa [naturalAdd_zero_left] at hlt
  exact not_lt.mpr (Order.add_one_le_iff.mpr h)

end NaturalSumControls

end Mettapedia.SetTheory.OrdinalArithmetic

#print axioms Mettapedia.SetTheory.OrdinalArithmetic.naturalAdd_lt_naturalAdd_left
#print axioms Mettapedia.SetTheory.OrdinalArithmetic.naturalAdd_lt_naturalAdd_right
#print axioms Mettapedia.SetTheory.OrdinalArithmetic.naturalAdd_lt_naturalAdd
#print axioms Mettapedia.SetTheory.OrdinalArithmetic.NaturalSumControls.naturalAdd_strict_left_here
