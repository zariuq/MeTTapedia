import Mettapedia.SetTheory.Surreal.Simplicity
import Mettapedia.SetTheory.Surreal.Birthday

/-!
# Birthday, options, and the cut characterisation

Conway's presentation defines a surreal as a pair of families, `x = {L | R}`,
and every operation is a recursion on that shape.  The sign expansion is a
different presentation of the same numbers, so the two have to be connected
before any Conway recursion can be ported.  This file is that connection.

* `birthday` — the level, transported to `Surreal`.  It is well defined
  because `length_eq_of_signAt_eq` already proved that equivalent expansions
  have equal levels, so nothing new is assumed.
* `leftOptions` / `rightOptions` — following the source's `SNoL` and `SNoR`:
  the numbers **born strictly earlier** that lie below, respectively above.
* `birthday_le_of_between` — **a number is the simplest one in its own cut.**
  This is what makes `x = {L | R}` a definition rather than a description.
* `eq_of_between_of_birthday_le` — and it is the only one that simple, so the
  cut determines the number.

The first of those is short and general: if something strictly inside the cut
were born earlier, it would itself be one of the options it is required to beat.

The second is where the sign expansion earns its keep.  Two distinct numbers of
the *same* birthday, one below the other, must first differ at a position
inside both, so the signs there are `−` and `+` — and then
`prefixOf_between` hands over a number strictly between them, born earlier,
which is an option that the lower one fails to beat.  That is exactly the case
`Simplicity.lean` covers, and the reason it was worth isolating.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace PreSurreal

/-- **Between two numbers of equal level there is always a simpler one.**  The
first difference lies inside both, so the deciding signs are `−` and `+`, and
the common prefix is strictly between and strictly shorter. -/
theorem exists_simpler_between {b a : PreSurreal} (hba : Lt b a)
    (hlen : b.length = a.length) :
    ∃ c : PreSurreal, c.length < a.length ∧ Lt b c ∧ Lt c a := by
  classical
  have hne : b.signAt ≠ a.signAt := by
    intro h
    exact not_lt_self b (lt_of_lt_of_equiv hba (equiv_symm (h : Equiv b a)))
  obtain ⟨δ, hδne, hδmin⟩ := exists_least_diff hne
  have hδlt : δ < a.length := by
    by_contra hcon
    have hge : a.length ≤ δ := not_lt.mp hcon
    exact hδne ((signAt_of_ge (hlen ▸ hge)).trans (signAt_of_ge hge).symm)
  have hδltb : δ < b.length := hlen ▸ hδlt
  -- The signs at the first difference are both recorded, and `b` is the lower.
  have hlt : b.signAt δ < a.signAt δ := by
    rcases hba with ⟨β, hagree, hlt'⟩
    rcases lt_trichotomy β δ with h | rfl | h
    · exact absurd (hδmin β h) (ne_of_lt hlt')
    · exact hlt'
    · exact absurd (hagree δ h) hδne
  have hbneg : b.signAt δ = Sign.neg := by
    rcases hb : b.signAt δ with _ | _ | _
    · rfl
    · exact absurd (signAt_eq_zero_iff.mp hb) (not_le.mpr hδltb)
    · rcases ha : a.signAt δ with _ | _ | _ <;> rw [hb, ha] at hlt <;>
        exact absurd hlt (by decide)
  have hapos : a.signAt δ = Sign.pos := by
    rcases ha : a.signAt δ with _ | _ | _
    · rw [hbneg, ha] at hlt; exact absurd hlt (by decide)
    · exact absurd (signAt_eq_zero_iff.mp ha) (not_le.mpr hδlt)
    · rfl
  obtain ⟨h1, h2⟩ := prefixOf_between (x := b) (y := a) (β := δ)
    (fun γ hγ => hδmin γ hγ) hbneg hapos
  exact ⟨prefixOf b δ, by rw [prefixOf_length]; exact hδlt, h1, h2⟩

end PreSurreal

namespace Surreal

open PreSurreal

/-! ## Birthday -/

/-- **The level, as a function of the number.**  Well defined because
equivalent expansions have equal levels. -/
def birthday : Surreal → Ordinal :=
  Quotient.lift PreSurreal.length fun _ _ h => length_eq_of_signAt_eq h

@[simp] theorem birthday_mk (x : PreSurreal) : birthday (mk x) = x.length := rfl

/-! ## Options -/

/-- The numbers born strictly earlier that lie below — the source's `SNoL`. -/
def leftOptions (a : Surreal) : Set Surreal :=
  {z | z < a ∧ birthday z < birthday a}

/-- The numbers born strictly earlier that lie above — the source's `SNoR`. -/
def rightOptions (a : Surreal) : Set Surreal :=
  {z | a < z ∧ birthday z < birthday a}

theorem lt_of_mem_leftOptions {a z : Surreal} (h : z ∈ leftOptions a) : z < a := h.1
theorem lt_of_mem_rightOptions {a z : Surreal} (h : z ∈ rightOptions a) : a < z := h.1

/-- Every number lies strictly inside its own cut. -/
theorem self_between (a : Surreal) :
    (∀ z ∈ leftOptions a, z < a) ∧ (∀ z ∈ rightOptions a, a < z) :=
  ⟨fun _ h => h.1, fun _ h => h.1⟩

/-! ## The cut characterisation -/

/-- **A number is the simplest one in its own cut.**  Anything strictly above
every left option and strictly below every right option is born no earlier —
because if it were born earlier it would be one of those options, and would
have to beat itself. -/
theorem birthday_le_of_between {a b : Surreal}
    (hL : ∀ z ∈ leftOptions a, z < b) (hR : ∀ z ∈ rightOptions a, b < z) :
    birthday a ≤ birthday b := by
  by_contra hcon
  have hb : birthday b < birthday a := not_le.mp hcon
  rcases lt_trichotomy b a with h | rfl | h
  · exact absurd (hL b ⟨h, hb⟩) (lt_irrefl b)
  · exact absurd hb (lt_irrefl _)
  · exact absurd (hR b ⟨h, hb⟩) (lt_irrefl b)

/-- **And it is the only one that simple**, so the cut determines the number.
Here the sign expansion does the work: two distinct numbers of equal birthday,
one below the other, always have a simpler number between them, and that number
is an option the lower one fails to beat. -/
theorem eq_of_between_of_birthday_le {a b : Surreal}
    (hL : ∀ z ∈ leftOptions a, z < b) (hR : ∀ z ∈ rightOptions a, b < z)
    (hle : birthday b ≤ birthday a) : b = a := by
  have heq : birthday b = birthday a :=
    le_antisymm hle (birthday_le_of_between hL hR)
  by_contra hne
  rcases lt_trichotomy b a with h | h | h
  · -- `b < a` with equal birthdays: a simpler number sits between them.
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        obtain ⟨c, hclen, hyc, hcx⟩ := exists_simpler_between (b := y) (a := x) h heq
        exact absurd (hL (mk c) ⟨hcx, hclen⟩) (not_lt.mpr (le_of_lt hyc))
  · exact hne h
  · -- `a < b` with equal birthdays: symmetric, on the right.
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        obtain ⟨c, hclen, hxc, hcy⟩ :=
          exists_simpler_between (b := x) (a := y) h heq.symm
        exact absurd (hR (mk c) ⟨hxc, heq ▸ hclen⟩) (not_lt.mpr (le_of_lt hcy))

/-! ## Controls -/

namespace CutControls

/-- `0` has no options at all: nothing is born before it. -/
theorem zero_leftOptions_empty : leftOptions (0 : Surreal) = ∅ := by
  ext z
  simp only [leftOptions, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hb⟩
  exact absurd hb (by
    show ¬ birthday z < birthday (mk zeroPre)
    rw [birthday_mk]
    simp [zeroPre])

theorem zero_rightOptions_empty : rightOptions (0 : Surreal) = ∅ := by
  ext z
  simp only [rightOptions, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hb⟩
  exact absurd hb (by
    show ¬ birthday z < birthday (mk zeroPre)
    rw [birthday_mk]
    simp [zeroPre])

/-- **So `0 = { | }` is forced**: with both families empty, every number is
vacuously inside the cut, and `0` is the unique simplest such. -/
theorem zero_is_simplest (b : Surreal) : birthday (0 : Surreal) ≤ birthday b := by
  refine birthday_le_of_between (fun z hz => ?_) (fun z hz => ?_)
  · rw [zero_leftOptions_empty] at hz; simp at hz
  · rw [zero_rightOptions_empty] at hz; simp at hz

/-- The birthday condition is not decoration, and it is asymmetric.  `1/2` is
below `1`, but it is born *later*, so it is **not** a left option of `1` — -/
theorem half_not_mem_leftOptions_one :
    mk (dyadicPre 1) ∉ leftOptions (mk (dyadicPre 0)) := by
  rintro ⟨-, hb⟩
  rw [birthday_mk, birthday_mk, dyadicPre_length, dyadicPre_length,
    Nat.cast_zero, Nat.cast_one, zero_add] at hb
  exact absurd hb (not_lt.mpr (le_of_lt (lt_add_one 1)))

/-- — while `1` *is* a right option of `1/2`, since it is above and simpler. -/
theorem one_mem_rightOptions_half :
    mk (dyadicPre 0) ∈ rightOptions (mk (dyadicPre 1)) := by
  refine ⟨dyadic_anti 0, ?_⟩
  rw [birthday_mk, birthday_mk, dyadicPre_length, dyadicPre_length,
    Nat.cast_zero, Nat.cast_one, zero_add]
  exact lt_add_one 1

end CutControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.PreSurreal.exists_simpler_between
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_le_of_between
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.eq_of_between_of_birthday_le
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.CutControls.zero_is_simplest
