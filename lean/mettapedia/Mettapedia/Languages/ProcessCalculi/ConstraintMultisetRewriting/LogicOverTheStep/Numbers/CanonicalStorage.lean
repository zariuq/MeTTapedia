import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Coherence

/-!
# Canonical storage: the value law met a second way, and why it is not coherence

**Canonical storage** (`canon`): a whole value is stored as an integer, any other value as a
fraction; storage is then a function of the value (`value_canon`, `canonical_eq_of_value`). On
canonically stored numbers (`Canonical`, `CStored`):

* **the storage lens and the value lens have the same types** (`indist_canonical_iff`,
  `concepts_canonical_iff`), and every observer family satisfies the value law
  (`canonical_valueLaw`). Off canonical storage this fails: the storage lens has strictly more
  types (`NumberLens.splitFive_control`), at the fraction `5`, which is not canonical
  (`fiveFrac_not_canonical`).

So the value law can be met in two ways: by admitting only operations that respect the value lens
(the exact division and the named quotient, `NumberLens.exactQuotient_respects`,
`NumberLens.quot_respects`), or by storing canonically, where every operation respects it
(`storedDiv_canonical_respects`).

**The second way is not enough for coherence.** On canonical storage the storage-dependent division
respects the value lens and still does not commute with the conversion from whole numbers to
rationals (`toFrac`, which stores a whole number as a fraction, as `5` becomes `5.0`):

* converting the dividend first gives `5/2`, dividing first gives `2` (`canonical_not_commutes`);
* the conversion leaves canonical storage (`toFrac_not_canonical`); storing its result canonically
  undoes it (`canon_toFrac`), and then the division of the rationals is not division: on canonical
  storage `5 / 2` is `2` (`canonDiv_five_two`), because on whole values it is the truncating
  quotient (`canonDiv_whole`), and no operation on values is both the truncating quotient on whole
  values and the division of the rationals (`no_value_operation_both`).

Either way the language with this `/` at the whole numbers and the rationals' division at the
rationals is incoherent (`Coherence.storageDiv_incoherent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.CanonicalStorage

open Set
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open Distinctions.ObserverConcepts Distinctions.NumberLens Tower

/-- **Canonical storage**: a whole value as an integer, any other value as a fraction. -/
def canon (q : ℚ) : Stored := if q.den = 1 then .int q.num else .frac q

theorem value_canon (q : ℚ) : value (canon q) = q := by
  unfold canon
  split_ifs with whole
  · exact Rat.coe_int_num_of_den_eq_one whole
  · rfl

/-- **Canonically stored.** -/
def Canonical (x : Stored) : Prop := canon (value x) = x

/-- The canonically stored numbers. -/
abbrev CStored := {x : Stored // Canonical x}

theorem canon_canonical (q : ℚ) : Canonical (canon q) := by
  unfold Canonical
  rw [value_canon]

/-- **On canonical storage, the value determines the number.** -/
theorem canonical_eq_of_value {x y : CStored} (same : value x.1 = value y.1) : x = y :=
  Subtype.ext (x.2.symm.trans (by rw [same]; exact y.2))

/-- The value lens on canonical numbers. -/
def valueLensC : Unit → CStored → ℚ := fun _ x => value x.1

/-- The storage lens on canonical numbers. -/
def storageLensC : Option Divisor → CStored → ℚ := fun i x => storageLens i x.1

/-- **On canonical numbers the storage lens sees exactly what the value lens sees.** -/
theorem indist_canonical_iff (x y : CStored) :
    Indist storageLensC x y ↔ Indist valueLensC x y := by
  constructor
  · intro same _
    exact same none
  · intro same _
    rw [canonical_eq_of_value (same ())]

/-- **So they have the same types.** -/
theorem concepts_canonical_iff (S : Set CStored) :
    IsConcept (Apart storageLensC) S ↔ IsConcept (Apart valueLensC) S := by
  rw [isConcept_iff_saturated, isConcept_iff_saturated]
  simp only [indist_canonical_iff]

/-- **Every observer family of canonical numbers satisfies the value law.** -/
theorem canonical_valueLaw {ι R : Type*} (read : ι → CStored → R) (x y : CStored)
    (same : value x.1 = value y.1) : Indist read x y := by
  rw [canonical_eq_of_value same]
  exact indist_refl y

/-- **Control: the fraction `5` is not canonical**; off canonical storage the storage lens splits it
from the integer `5` (`NumberLens.splitFive_control`). -/
theorem fiveFrac_not_canonical : ¬ Canonical fiveFrac := by
  intro canonical
  have whole : (value fiveFrac).den = 1 := by
    rw [value_fiveFrac]
    rfl
  unfold Canonical canon at canonical
  rw [if_pos whole] at canonical
  simp [fiveFrac] at canonical

/-- **The storage-dependent division respects the value lens on canonical storage.** -/
theorem storedDiv_canonical_respects :
    Respects (pairRead valueLensC valueLensC) valueLens
      (fun x : CStored × CStored => storedDiv x.1.1 x.2.1) := by
  rw [respects_pair_iff]
  intro a a' b b' first second _
  rw [canonical_eq_of_value (first ()), canonical_eq_of_value (second ())]

/-! ## Not coherence -/

/-- The canonical `5`. -/
theorem canon_five : canon 5 = .int 5 := by
  simp [canon]

/-- The canonical `2`. -/
theorem canon_two : canon 2 = .int 2 := by
  simp [canon]

theorem tdiv_five_two : Int.tdiv 5 2 = 2 := by decide

/-- **The storage-dependent division on canonical storage does not commute with the conversion from
whole numbers to rationals**: converting the dividend first gives `5/2`; dividing first gives `2`. -/
theorem canonical_not_commutes :
    value (storedDiv (toFrac (canon 5)) (canon 2)) = 5 / 2 ∧
      value (toFrac (storedDiv (canon 5) (canon 2))) = 2 := by
  rw [canon_five, canon_two]
  constructor
  · show ((5 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) = 5 / 2
    norm_num
  · show (((Int.tdiv 5 2 : ℤ)) : ℚ) = 2
    rw [tdiv_five_two]
    norm_num

/-- **The conversion leaves canonical storage.** -/
theorem toFrac_not_canonical : ¬ Canonical (toFrac (canon 5)) := by
  intro canonical
  rw [canon_five] at canonical
  unfold Canonical canon toFrac at canonical
  rw [if_pos (show (value (Stored.frac (value (Stored.int 5)))).den = 1 from rfl)] at canonical
  simp at canonical

/-- **Storing it canonically undoes it.** -/
theorem canon_toFrac (x : Stored) : canon (value (toFrac x)) = canon (value x) := rfl

/-- The storage-dependent division on canonical storage, as an operation on values. -/
def canonDiv (p q : ℚ) : ℚ := value (storedDiv (canon p) (canon q))

theorem canon_int (m : ℤ) : canon (m : ℚ) = .int m := by
  unfold canon
  rw [if_pos (Rat.den_intCast m), Rat.num_intCast]

/-- **On whole values it is the truncating quotient.** -/
theorem canonDiv_whole (m n : ℤ) : canonDiv m n = ((m.tdiv n : ℤ) : ℚ) := by
  unfold canonDiv
  rw [canon_int, canon_int]
  rfl

/-- **So on canonical storage `5 / 2` is `2`, not the division of the rationals.** -/
theorem canonDiv_five_two : canonDiv 5 2 = 2 ∧ canonDiv 5 2 ≠ 5 / 2 := by
  have whole : canonDiv 5 2 = 2 := by
    have := canonDiv_whole 5 2
    rw [tdiv_five_two] at this
    simpa using this
  refine ⟨whole, ?_⟩
  rw [whole]
  norm_num

/-- **No operation on values is both the truncating quotient on whole values and the division of
the rationals.** -/
theorem no_value_operation_both :
    ¬ ∃ g : ℚ → ℚ → ℚ, (∀ m n : ℤ, n ≠ 0 → g m n = ((m.tdiv n : ℤ) : ℚ)) ∧
      ∀ p q : ℚ, q ≠ 0 → g p q = p / q := by
  rintro ⟨g, whole, rational⟩
  have first := whole 5 2 (by decide)
  have second := rational 5 2 (by norm_num)
  rw [tdiv_five_two] at first
  push_cast at first
  rw [first] at second
  norm_num at second

#print axioms value_canon
#print axioms canon_canonical
#print axioms canonical_eq_of_value
#print axioms indist_canonical_iff
#print axioms concepts_canonical_iff
#print axioms canonical_valueLaw
#print axioms fiveFrac_not_canonical
#print axioms storedDiv_canonical_respects
#print axioms canonical_not_commutes
#print axioms toFrac_not_canonical
#print axioms canon_toFrac
#print axioms canonDiv_whole
#print axioms canonDiv_five_two
#print axioms no_value_operation_both

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.CanonicalStorage
