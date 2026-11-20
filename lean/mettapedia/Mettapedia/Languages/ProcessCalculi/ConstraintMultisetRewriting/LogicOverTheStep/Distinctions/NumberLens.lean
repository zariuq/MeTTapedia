import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.ObserverConcepts

/-!
# The number lens: one value, two storages

A stored number keeps its storage: an integer, or a fraction that may happen to be whole
(`Stored`). Its value is a rational (`value`). This module is a model of measured behaviour of a
MeTTa implementation's numbers, not of any implementation: an integer and a float of equal value
compare equal, and division truncates toward zero when both arguments are stored as integers and
divides exactly otherwise (`storedDiv`). Floats are modelled by exact fractions, which is faithful
on the values measured. Division by zero, an error for integers and an infinity for floats in the
measured behaviour, is outside the model: divisors are nonzero (`Divisor`).

Two observer families:

* **the value lens** (`valueLens`): one reading, the value. Its types are the classes closed under
  equality of value;
* **the storage lens** (`storageLens`): the value, and the value after dividing by each nonzero
  divisor with the storage-dependent division. The value lens is its subfamily.

Results.

* **One type, or two.** Under the value lens the stored integer `5` and the whole fraction `5` are
  in every type together (`five_same_concepts`, `fiveFrac_mem_conceptOf`); under the storage lens
  they are apart, and a type holds one and not the other (`apart_storage_five`, `splitFive_control`).
* **Which operations belong to the value lens** (`ObserverConcepts.pullback_isConcept_iff`): exact
  division does (`exactQuotient_respects`); the storage-dependent division does not
  (`storedQuotient_not_respects`); a named quotient defined on every whole value, however stored,
  does (`quot_respects`), and on integer storage it is the storage-dependent division
  (`quot_int`).
* **Strictly more types** (`value_concepts_storage`, `splitFive_control`): every type of the value
  lens is a type of the storage lens, and not conversely.
* **Exactly what the storage lens sees** (`indist_storage_iff`): two stored numbers are
  indistinguishable to it exactly when they have the same value and are stored the same way, or the
  value is zero. An integer and a fraction of the same nonzero value are split by dividing by twice
  the value (`int_frac_split`); the stored integer `0` and the fraction `0` are not split, since
  dividing zero gives zero however it is stored (`zero_not_split`).

**Soft** means that every admitted observer factors through the value, so the types are unions of
value classes and storage is invisible. **Strict** means that some admitted observer reads storage:
here the storage lens separates a stored integer from the fraction of the same value exactly when
that value is not zero, so converting the storage of a nonzero number changes its type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.NumberLens

open Set
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open ObserverConcepts

/-- **A stored number**: an integer, or a fraction that may happen to be whole. -/
inductive Stored
  | int (n : ℤ)
  | frac (q : ℚ)

/-- **Its value.** -/
def value : Stored → ℚ
  | .int n => n
  | .frac q => q

/-- A nonzero divisor. -/
abbrev Divisor := {d : Stored // value d ≠ 0}

/-- **Division that reads storage**: truncating toward zero when both arguments are stored as
integers, exact otherwise. -/
def storedDiv : Stored → Stored → Stored
  | .int a, .int b => .int (a.tdiv b)
  | .int a, .frac q => .frac ((a : ℚ) / q)
  | .frac p, .int b => .frac (p / (b : ℚ))
  | .frac p, .frac q => .frac (p / q)

/-- **Exact division**, by value. -/
def exactDiv (x y : Stored) : Stored := .frac (value x / value y)

/-- **The value lens**: one reading, the value. -/
def valueLens : Unit → Stored → ℚ := fun _ x => value x

/-- The value of a divisor. -/
def divisorLens : Unit → Divisor → ℚ := fun _ d => value d.1

/-- **The storage lens**: the value, and the value after the storage-dependent division by each
nonzero divisor. -/
def storageLens : Option Divisor → Stored → ℚ
  | none, x => value x
  | some d, x => value (storedDiv x d.1)

/-- The stored integer `5`. -/
def five : Stored := .int 5

/-- The whole fraction `5`. -/
def fiveFrac : Stored := .frac 5

/-- The divisor `2`, stored as an integer. -/
def two : Divisor := ⟨.int 2, by norm_num [value]⟩

theorem value_five : value five = 5 := by norm_num [five, value]

theorem value_fiveFrac : value fiveFrac = 5 := rfl

/-! ## One type, or two -/

/-- Under the value lens the two `5`s are indistinguishable. -/
theorem indist_value_five : Indist valueLens five fiveFrac :=
  fun _ => value_five.trans value_fiveFrac.symm

/-- **Under the value lens the stored integer `5` and the whole fraction `5` are in every type
together.** -/
theorem five_same_concepts (S : Set Stored) (concept : IsConcept (Apart valueLens) S) :
    five ∈ S ↔ fiveFrac ∈ S := by
  rw [isConcept_iff_saturated] at concept
  exact ⟨fun inS => concept five inS fiveFrac indist_value_five,
    fun inS => concept fiveFrac inS five (indist_symm indist_value_five)⟩

theorem fiveFrac_mem_conceptOf : fiveFrac ∈ conceptOf (Apart valueLens) five := by
  rw [conceptOf_eq]
  exact indist_value_five

theorem storedDiv_five_two : value (storedDiv five two.1) = 2 := by
  have truncated : Int.tdiv 5 2 = 2 := by decide
  show ((Int.tdiv 5 2 : ℤ) : ℚ) = 2
  rw [truncated]
  norm_num

theorem storedDiv_fiveFrac_two : value (storedDiv fiveFrac two.1) = 5 / 2 := by
  norm_num [storedDiv, fiveFrac, two, value]

/-- **Under the storage lens they are apart**: divided by the integer `2`, the stored integer `5`
gives `2` and the whole fraction `5` gives `5 / 2`. -/
theorem apart_storage_five : Apart storageLens five fiveFrac := by
  refine ⟨some two, ?_⟩
  show value (storedDiv five two.1) ≠ value (storedDiv fiveFrac two.1)
  rw [storedDiv_five_two, storedDiv_fiveFrac_two]
  norm_num

/-- The stored numbers that, divided by the integer `2`, give `2`. -/
def splitFive : Set Stored := {x | storageLens (some two) x = 2}

/-- **Control: a type of the storage lens that holds the stored integer `5` and not the whole
fraction `5`, and is no type of the value lens.** -/
theorem splitFive_control :
    IsConcept (Apart storageLens) splitFive ∧ five ∈ splitFive ∧ fiveFrac ∉ splitFive ∧
      ¬ IsConcept (Apart valueLens) splitFive := by
  have inside : five ∈ splitFive := storedDiv_five_two
  have outside : fiveFrac ∉ splitFive := by
    intro member
    have equal : value (storedDiv fiveFrac two.1) = 2 := member
    rw [storedDiv_fiveFrac_two] at equal
    norm_num at equal
  exact ⟨isConcept_fibre (some two) 2, inside, outside,
    fun concept => outside ((five_same_concepts splitFive concept).mp inside)⟩

/-- **Strictly more types**: every type of the value lens is a type of the storage lens. -/
theorem value_concepts_storage (S : Set Stored) (concept : IsConcept (Apart valueLens) S) :
    IsConcept (Apart storageLens) S :=
  isConcept_of_reindex (read := storageLens) (fun _ : Unit => none) concept

/-- **What the storage lens cannot see**: the stored integer `0` and the fraction `0`. -/
theorem zero_not_split : Indist storageLens (.int 0) (.frac 0) := by
  rintro (_ | ⟨d | q, _⟩) <;> simp [storageLens, storedDiv, value]

/-- Stored the same way: both integers, or both fractions. -/
def SameStorage : Stored → Stored → Prop
  | .int _, .int _ => True
  | .frac _, .frac _ => True
  | .int _, .frac _ => False
  | .frac _, .int _ => False

/-- A nonzero integer truncated by twice itself is zero. -/
theorem tdiv_double (a : ℤ) (nonzero : a ≠ 0) : a.tdiv (2 * a) = 0 := by
  apply Int.natAbs_eq_zero.mp
  rw [Int.natAbs_tdiv, Int.natAbs_mul]
  have positive : 0 < a.natAbs := Int.natAbs_pos.mpr nonzero
  show a.natAbs / ((2 : ℤ).natAbs * a.natAbs) = 0
  apply Nat.div_eq_of_lt
  have two : (2 : ℤ).natAbs = 2 := rfl
  rw [two]
  omega

/-- **An integer and a fraction of the same nonzero value are split**: divided by twice the value,
stored as an integer, the integer gives `0` and the fraction `1/2`. -/
theorem int_frac_split (a : ℤ) (q : ℚ) (same : (a : ℚ) = q) (nonzero : a ≠ 0) :
    Apart storageLens (.int a) (.frac q) := by
  have castNonzero : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr nonzero
  have doubleNonzero : (2 : ℚ) * a ≠ 0 := mul_ne_zero two_ne_zero castNonzero
  refine ⟨some ⟨.int (2 * a), ?_⟩, ?_⟩
  · show ((2 * a : ℤ) : ℚ) ≠ 0
    push_cast
    exact doubleNonzero
  · show ((a.tdiv (2 * a) : ℤ) : ℚ) ≠ q / ((2 * a : ℤ) : ℚ)
    rw [tdiv_double a nonzero, ← same]
    push_cast
    rw [show (a : ℚ) / (2 * a) = 1 / 2 by rw [div_eq_iff doubleNonzero]; ring]
    norm_num

/-- **Exactly what the storage lens sees**: two stored numbers are indistinguishable to it exactly
when they have the same value and are stored the same way, or the value is zero. -/
theorem indist_storage_iff (x y : Stored) :
    Indist storageLens x y ↔ value x = value y ∧ (SameStorage x y ∨ value x = 0) := by
  constructor
  · intro same
    have values : value x = value y := same none
    refine ⟨values, ?_⟩
    cases x with
    | int a =>
        cases y with
        | int b => exact Or.inl trivial
        | frac q =>
            by_cases zero : a = 0
            · right
              show (a : ℚ) = 0
              rw [zero, Int.cast_zero]
            · exact absurd same (apart_iff_not_indist.mp (int_frac_split a q values zero))
    | frac p =>
        cases y with
        | int b =>
            by_cases zero : b = 0
            · right
              show p = 0
              have : p = (b : ℚ) := values
              rw [this, zero, Int.cast_zero]
            · exact absurd (indist_symm same)
                (apart_iff_not_indist.mp (int_frac_split b p values.symm zero))
        | frac q => exact Or.inl trivial
  · rintro ⟨values, storage | zero⟩
    · cases x with
      | int a =>
          cases y with
          | int b =>
              have cast : (a : ℚ) = b := values
              have equal : a = b := by exact_mod_cast cast
              rw [equal]
              exact indist_refl _
          | frac q => exact (storage : False).elim
      | frac p =>
          cases y with
          | int b => exact (storage : False).elim
          | frac q =>
              have equal : p = q := values
              rw [equal]
              exact indist_refl _
    · cases x with
      | int a =>
          have cast : (a : ℚ) = 0 := zero
          have a0 : a = 0 := by exact_mod_cast cast
          cases y with
          | int b =>
              have castB : (a : ℚ) = b := values
              have equal : a = b := by exact_mod_cast castB
              rw [equal]
              exact indist_refl _
          | frac q =>
              have q0 : q = 0 := values.symm.trans zero
              rw [a0, q0]
              exact zero_not_split
      | frac p =>
          have p0 : p = 0 := zero
          cases y with
          | int b =>
              have castB : (b : ℚ) = 0 := values.symm.trans zero
              have b0 : b = 0 := by exact_mod_cast castB
              rw [p0, b0]
              exact indist_symm zero_not_split
          | frac q =>
              have equal : p = q := values
              rw [equal]
              exact indist_refl _

/-! ## Which operations belong to the value lens -/

/-- Exact division of a stored number by a nonzero divisor. -/
def exactQuotient (p : Stored × Divisor) : Stored := exactDiv p.1 p.2.1

/-- The storage-dependent division of a stored number by a nonzero divisor. -/
def storedQuotient (p : Stored × Divisor) : Stored := storedDiv p.1 p.2.1

/-- **Exact division belongs to the value lens.** -/
theorem exactQuotient_respects : Respects (pairRead valueLens divisorLens) valueLens exactQuotient := by
  rw [respects_pair_iff]
  intro a a' b b' first second _
  show value a / value b.1 = value a' / value b'.1
  rw [show value a = value a' from first (), show value b.1 = value b'.1 from second ()]

/-- **The storage-dependent division does not**: it splits the two `5`s. -/
theorem storedQuotient_not_respects :
    ¬ Respects (pairRead valueLens divisorLens) valueLens storedQuotient := by
  rw [respects_pair_iff]
  intro respects
  have equal : value (storedDiv five two.1) = value (storedDiv fiveFrac two.1) :=
    respects five fiveFrac two two indist_value_five (indist_refl two) ()
  rw [storedDiv_five_two, storedDiv_fiveFrac_two] at equal
  norm_num at equal

/-- The same two facts as pullbacks of types. -/
theorem quotients_pull_back :
    (∀ S, IsConcept (Apart valueLens) S →
        IsConcept (Apart (pairRead valueLens divisorLens)) (exactQuotient ⁻¹' S)) ∧
      ¬ (∀ S, IsConcept (Apart valueLens) S →
        IsConcept (Apart (pairRead valueLens divisorLens)) (storedQuotient ⁻¹' S)) :=
  ⟨(pullback_isConcept_iff _ _ _).mpr exactQuotient_respects,
    fun pulls => storedQuotient_not_respects ((pullback_isConcept_iff _ _ _).mp pulls)⟩

/-- A stored number with a whole value. -/
def IsWhole (x : Stored) : Prop := (value x).den = 1

/-- **Pairs of whole values**, the divisor nonzero, however they are stored. -/
abbrev WholePair := {p : Stored × Divisor // IsWhole p.1 ∧ IsWhole p.2.1}

/-- The value lens on whole pairs: the values of both components. -/
def wholeLens : Unit ⊕ Unit → WholePair → ℚ := fun i p => pairRead valueLens divisorLens i p.1

/-- **The named quotient**: truncating division of whole values, however they are stored. -/
def quot (p : WholePair) : Stored := .int ((value p.1.1).num.tdiv (value p.1.2.1).num)

/-- **The named quotient belongs to the value lens.** -/
theorem quot_respects : Respects wholeLens valueLens quot := by
  intro p q same _
  have first : value p.1.1 = value q.1.1 := same (.inl ())
  have second : value p.1.2.1 = value q.1.2.1 := same (.inr ())
  show value (quot p) = value (quot q)
  rw [quot, quot, first, second]

/-- On integer storage the named quotient is the storage-dependent division. -/
theorem quot_int (a b : ℤ) (nonzero : value (.int b) ≠ 0) :
    quot ⟨(.int a, ⟨.int b, nonzero⟩), rfl, rfl⟩ = storedDiv (.int a) (.int b) := by
  simp [quot, storedDiv, value]

/-- **It accepts both `5`s and gives one answer.** -/
theorem quot_five :
    quot ⟨(five, two), rfl, rfl⟩ = .int 2 ∧ quot ⟨(fiveFrac, two), rfl, rfl⟩ = .int 2 := by
  refine ⟨?_, ?_⟩ <;> simp [quot, five, fiveFrac, two, value]

#print axioms indist_value_five
#print axioms five_same_concepts
#print axioms fiveFrac_mem_conceptOf
#print axioms apart_storage_five
#print axioms splitFive_control
#print axioms value_concepts_storage
#print axioms zero_not_split
#print axioms tdiv_double
#print axioms int_frac_split
#print axioms indist_storage_iff
#print axioms exactQuotient_respects
#print axioms storedQuotient_not_respects
#print axioms quotients_pull_back
#print axioms quot_respects
#print axioms quot_int
#print axioms quot_five

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.NumberLens
