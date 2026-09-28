import Mettapedia.SetTheory.Surreal.IntegerArithmetic
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Numbers born by day `n` form a finite set

The dyadic characterisation needs the *greatest* left option and the *least*
right option of a number, not merely bounds on them. Those exist because the
numbers born by a finite day form a finite set: such a number is determined by
its sign at each position below its length, and there are finitely many
lengths and finitely many signs.

`BoundedBirthday.lean` proves the numbers born before an arbitrary ordinal are
`Small.{0}`, which is what the cut construction consumes. Smallness is not
enough here — a small linearly ordered set need not have a greatest element —
so this file proves the sharper statement available at finite days.

* `sigAt` — the sign function, descended to `Surreal`. It is well defined
  because agreement of sign functions *is* the equivalence on expansions.
* `finite_birthday_le` — `{x | birthday x ≤ n}` is finite.
* `exists_max_leftOptions`, `exists_min_rightOptions` — so the option families
  attain their bounds.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open PreSurreal

/-! ## The sign function on numbers -/

/-- There are three signs, so sign functions on a finite range form a finite
type.  This is what makes the day set finite. -/
instance instFintypeSign : Fintype Sign where
  elems := {Sign.neg, Sign.zero, Sign.pos}
  complete := by intro a; cases a <;> decide

/-- The sign at each position, as a function of the *number*.  Two expansions
denote the same number exactly when their sign functions agree, so this is
well defined with nothing to check. -/
noncomputable def sigAt : Surreal → Ordinal → Sign :=
  Quotient.lift PreSurreal.signAt (fun _ _ h => h)

@[simp] theorem sigAt_mk (p : PreSurreal) : sigAt (mk p) = p.signAt := rfl

theorem sigAt_injective : Function.Injective sigAt := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q => exact mk_eq_mk.mpr h

theorem sigAt_eq_zero_of_le {x : Surreal} {β : Ordinal} (h : birthday x ≤ β) :
    sigAt x β = Sign.zero := by
  induction x using Quotient.inductionOn with
  | h p => exact signAt_of_ge h

/-! ## Finiteness -/

/-- **The numbers born by day `n` form a finite set.** -/
theorem finite_birthday_le (n : ℕ) :
    Set.Finite {x : Surreal | birthday x ≤ (n : Ordinal)} := by
  classical
  have hfin : Finite ↥{x : Surreal | birthday x ≤ (n : Ordinal)} := by
    refine Finite.of_injective
      (fun x => (fun i : Fin n => sigAt x.1 ((i : ℕ) : Ordinal))) ?_
    intro x y h
    refine Subtype.ext (sigAt_injective ?_)
    funext β
    rcases lt_or_ge β ((n : ℕ) : Ordinal) with hβ | hβ
    · obtain ⟨i, rfl⟩ :=
        Ordinal.lt_omega0.mp (lt_trans hβ (Ordinal.natCast_lt_omega0 n))
      have hi : i < n := by exact_mod_cast hβ
      exact congrFun h ⟨i, hi⟩
    · rw [sigAt_eq_zero_of_le (le_trans x.2 hβ),
        sigAt_eq_zero_of_le (le_trans y.2 hβ)]
  exact Set.toFinite _

theorem finite_leftOptions {c : Surreal} (hfin : birthday c < Ordinal.omega0) :
    (leftOptions c).Finite := by
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hfin
  refine Set.Finite.subset (finite_birthday_le n) ?_
  intro z hz
  exact le_of_lt (hn ▸ hz.2)

theorem finite_rightOptions {c : Surreal} (hfin : birthday c < Ordinal.omega0) :
    (rightOptions c).Finite := by
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hfin
  refine Set.Finite.subset (finite_birthday_le n) ?_
  intro z hz
  exact le_of_lt (hn ▸ hz.2)

/-! ## Attainment -/

/-- **A nonempty left option family has a greatest element.** -/
theorem exists_max_leftOptions {c : Surreal} (hfin : birthday c < Ordinal.omega0)
    (hne : (leftOptions c).Nonempty) :
    ∃ a ∈ leftOptions c, ∀ u ∈ leftOptions c, u ≤ a :=
  Set.exists_max_image _ id (finite_leftOptions hfin) hne

/-- **And a nonempty right option family a least one.** -/
theorem exists_min_rightOptions {c : Surreal} (hfin : birthday c < Ordinal.omega0)
    (hne : (rightOptions c).Nonempty) :
    ∃ b ∈ rightOptions c, ∀ v ∈ rightOptions c, b ≤ v :=
  Set.exists_min_image _ id (finite_rightOptions hfin) hne

/-! ## The numbers with no options above -/

/-- **A number with no right options is a natural.**  Otherwise it would sit
strictly between `ofNat (birthday c)` and nothing, and `exists_earlier_between`
would produce a younger number above it. -/
theorem eq_ofNat_of_rightOptions_empty {c : Surreal} {n : ℕ}
    (hb : birthday c = (n : Ordinal)) (h : rightOptions c = ∅) :
    c = ofNat n := by
  have hle : c ≤ ofNat n := le_ofNat_of_birthday_le (le_of_eq hb)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hbe : birthday c = birthday (ofNat n) := by rw [hb, birthday_ofNat]
    obtain ⟨z, hz, hcz, hzn⟩ := exists_earlier_between hlt hbe
    have : z ∈ rightOptions c := ⟨hcz, by rw [hb, ← birthday_ofNat]; exact hz⟩
    rw [h] at this
    exact this.elim
  · exact heq

/-- Dually. -/
theorem eq_neg_ofNat_of_leftOptions_empty {c : Surreal} {n : ℕ}
    (hb : birthday c = (n : Ordinal)) (h : leftOptions c = ∅) :
    c = -(ofNat n) := by
  have hbn : birthday (-c) = (n : Ordinal) := by rwa [birthday_neg]
  have hr : rightOptions (-c) = ∅ := by
    rw [rightOptions_neg, h, Set.image_empty]
  have := eq_ofNat_of_rightOptions_empty hbn hr
  rw [← neg_neg' c, this]

/-! ## Controls -/

namespace FiniteDayControls

/-- Day zero really is a single point, so finiteness is not vacuous at the
bottom. -/
theorem day_zero : {x : Surreal | birthday x ≤ (0 : Ordinal)} = {0} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun h => birthday_eq_zero_iff.mp (le_antisymm h (by exact zero_le)),
    fun h => by rw [h]; exact le_of_eq rfl⟩

/-- The max is attained at a number with two left options, not only at one
with a single option. -/
theorem max_left_of_half :
    ∃ a ∈ leftOptions (mk (dyadicPre 1)), ∀ u ∈ leftOptions (mk (dyadicPre 1)), u ≤ a := by
  exact exists_max_leftOptions (birthday_ladder_lt_omega0 1)
    ⟨0, PositiveFloorControls.zero_mem_leftOptions_half⟩

/-- **Negative control**: the option families are not empty in general, so
attainment is a real statement. -/
theorem half_has_both :
    (leftOptions (mk (dyadicPre 1))).Nonempty ∧
      (rightOptions (mk (dyadicPre 1))).Nonempty :=
  ⟨⟨0, PositiveFloorControls.zero_mem_leftOptions_half⟩,
   ⟨mk (dyadicPre 0), CutControls.one_mem_rightOptions_half⟩⟩

end FiniteDayControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.finite_birthday_le
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.exists_max_leftOptions
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.eq_ofNat_of_rightOptions_empty
