import Mettapedia.SetTheory.Surreal.CutConstruction

/-!
# Numbers born before a given day form a small family

The cut construction needs its option families to have bounded birthdays.

The usual development gets that from a *birthday* bound on the sum, of the form
`birthday (x + y) ≤ birthday x ⊕ birthday y`. That route is not available here,
and not only because the natural sum `⊕` is absent from this Mathlib pin —
`Mettapedia/SetTheory/Ordinal/NaturalSum.lean` supplies it. The obstruction is
circularity: deriving such a bound needs `IsCut.birthday_le_bound`, which
applies only once the sum is known to *be* the cut, which is what the bound was
wanted for. The natural sum is built for the simultaneous induction's measure,
which is a different job; it is not an alternative to this file.

Smallness avoids the circle entirely, because it never mentions the sum. An expansion born before `α`
is determined by a level below `α` together with its signs below `α`, and both
of those range over small types. So:

* `small_birthday_lt` — the numbers born before `α` form a `Small.{0}` family;
* `small_leftOptions`, `small_rightOptions` — in particular a number's own
  options do;
* `bddAbove_birthday_of_small` — and a small family has bounded birthdays,
  which is the hypothesis the cut actually consumes.

This is the boundedness obligation, discharged once and for all rather than
re-argued at each recursive call. Separation is a different obligation and is
not addressed here.

The circularity described above is a fact about *this position* in the
development, not a standing one. Once separation is proved — `AdditionOrder`'s
`separated_sum` — `isCut_add'` holds unconditionally, and the birthday bound
`birthday (x + y) ≤ birthday x ⊕ birthday y` follows; it is proved in
`AdditionBirthday.lean`. It could not have been used here, and it does not
replace smallness, which is what the cut construction itself consumes.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open PreSurreal

/-- An expansion assembled from a level below `α` and a sign pattern below
`α`.  Everything at or above `α` is irrelevant, because such a number's level
is below `α` and the padded signs there are the middle sign. -/
noncomputable def ofBoundedData (α : Ordinal)
    (d : (Set.Iio α) × ((Set.Iio α) → Bool)) : Surreal :=
  mk ⟨d.1.1, fun γ => if h : γ < α then d.2 ⟨γ, h⟩ else false⟩

/-- **Every number born before `α` arises from such data.** -/
theorem birthday_lt_subset_range (α : Ordinal) :
    {z : Surreal | birthday z < α} ⊆ Set.range (ofBoundedData α) := by
  intro z hz
  induction z using Quotient.inductionOn with
  | h p =>
      have hlen : p.length < α := hz
      refine ⟨(⟨p.length, hlen⟩, fun γ => p.sign γ.1), ?_⟩
      apply Quotient.sound
      funext γ
      by_cases hγ : γ < p.length
      · rw [signAt_of_lt (show γ < (⟨p.length, fun δ => if h : δ < α then p.sign δ else false⟩
            : PreSurreal).length from hγ), signAt_of_lt hγ]
        simp only [dif_pos (hγ.trans hlen)]
      · have hA : (⟨p.length, fun δ => if h : δ < α then p.sign δ else false⟩
            : PreSurreal).signAt γ = Sign.zero := signAt_of_ge (not_lt.mp hγ)
        have hB : p.signAt γ = Sign.zero := signAt_of_ge (not_lt.mp hγ)
        rw [hA, hB]

/-- **The numbers born before `α` form a small family.** -/
instance small_birthday_lt (α : Ordinal) : Small.{0} {z : Surreal | birthday z < α} :=
  small_subset (birthday_lt_subset_range α)

/-- A number's left options are born before it, hence form a small family. -/
instance small_leftOptions (x : Surreal) : Small.{0} (leftOptions x) :=
  small_subset (show leftOptions x ⊆ {z : Surreal | birthday z < birthday x} from
    fun _ hz => hz.2)

/-- And its right options. -/
instance small_rightOptions (x : Surreal) : Small.{0} (rightOptions x) :=
  small_subset (show rightOptions x ⊆ {z : Surreal | birthday z < birthday x} from
    fun _ hz => hz.2)

/-! ## Smallness gives the bound the cut consumes -/

/-- **A small family of numbers has bounded birthdays.** -/
theorem bddAbove_birthday_of_small (S : Set Surreal) [Small.{0} S] :
    BddAbove (birthday '' S) := by
  have : Small.{0} (birthday '' S) := small_image birthday S
  exact Ordinal.bddAbove_of_small

/-- The form the cut construction wants: two small families, one bound. -/
theorem bddAbove_birthday_union (L R : Set Surreal) [Small.{0} L] [Small.{0} R] :
    BddAbove (birthday '' (L ∪ R)) :=
  bddAbove_birthday_of_small (L ∪ R)

/-! ## Controls -/

namespace BoundedBirthdayControls

/-- The canonical families are small, which re-proves the existing bound by a
different route. -/
theorem canonical_bounded' (x : Surreal) :
    BddAbove (birthday '' (leftOptions x ∪ rightOptions x)) :=
  bddAbove_birthday_union _ _

/-- Smallness is genuinely about a *bound*: the family of all numbers is not
small, matching the existing negative control that it has no cut. -/
theorem all_not_bounded : ¬ BddAbove (birthday '' (Set.univ ∪ (∅ : Set Surreal))) :=
  CutConstructionControls.all_birthdays_not_bounded

/-- And the bound is not vacuous below `ω`: zero is born before it. -/
theorem zero_mem_birthday_lt : (0 : Surreal) ∈ {z : Surreal | birthday z < Ordinal.omega0} := by
  show birthday (0 : Surreal) < Ordinal.omega0
  show (0 : Ordinal) < Ordinal.omega0
  exact Ordinal.omega0_pos

end BoundedBirthdayControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_lt_subset_range
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.bddAbove_birthday_of_small
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.bddAbove_birthday_union
