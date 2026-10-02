import Mettapedia.Computability.RegularLanguages.Regex
import Mathlib.Data.List.Range

/-!
# Grouping, optionality and repetition

Grouping, optionality and repetition elaborate into the existing regex
operations. Bounded repetition includes both bounds and denotes the empty
language when its bounds are reversed. Repetition counts accepted factors,
not characters: a nullable factor can contribute no characters.

A range of repetition counts is the lower bound's factors followed by at most
the difference, so the expression has one copy of the operand for each count
up to the upper bound.

The operation profile follows Dylon Edwards' capture-free regex GSLT contract
in F1R3FLY-io/mettail-rust, revision
`99885f467e42d52ef60ca0bb6076eb0fa25bfa0e`, including the shape of its
expansion of a range. The semantics below are independently proved in
Mathlib's algebra of languages. These constructors are not a parser.
-/

set_option autoImplicit false

open scoped Computability

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

/-- Capture-free grouping changes no regex operation or language. -/
def group (p : Regex α) : Regex α := p

/-- The operand or the empty word. -/
def optional (p : Regex α) : Regex α := 1 + p

/-- One or more factors accepted by the operand. -/
def positiveRepeat (p : Regex α) : Regex α := p * p.star

/-- Exactly `count` factors accepted by the operand. -/
def exactRepeat (p : Regex α) (count : Nat) : Regex α := p ^ count

/-- At most `count` factors accepted by the operand. -/
def atMostRepeat (p : Regex α) : Nat → Regex α
  | 0 => 1
  | count + 1 => 1 + p * atMostRepeat p count

/-- An inclusive range of repetition counts: the lower bound's factors, then
at most the difference. Reversed bounds denote the empty language. -/
def boundedRepeat (p : Regex α) (lower upper : Nat) : Regex α :=
  if lower ≤ upper then p ^ lower * atMostRepeat p (upper - lower) else 0

@[simp] theorem language_group (p : Regex α) : language (group p) = language p := rfl

@[simp] theorem language_optional (p : Regex α) :
    language (optional p) = 1 + language p := rfl

theorem mem_language_optional (p : Regex α) (w : List α) :
    w ∈ language (optional p) ↔ w = [] ∨ w ∈ language p := by
  rw [language_optional, Language.mem_add, Language.mem_one]

@[simp] theorem language_positiveRepeat (p : Regex α) :
    language (positiveRepeat p) = language p * (language p)∗ := rfl

theorem mem_language_positiveRepeat (p : Regex α) (w : List α) :
    w ∈ language (positiveRepeat p) ↔
      ∃ count, 0 < count ∧ w ∈ language p ^ count := by
  rw [language_positiveRepeat, Language.kstar_eq_iSup_pow, Language.mul_iSup]
  simp only [← pow_succ', Language.mem_iSup]
  constructor
  · rintro ⟨count, hw⟩
    exact ⟨count + 1, Nat.zero_lt_succ count, hw⟩
  · rintro ⟨count, hcount, hw⟩
    cases count with
    | zero => exact False.elim (Nat.lt_irrefl _ hcount)
    | succ count => exact ⟨count, hw⟩

@[simp] theorem language_exactRepeat (p : Regex α) (count : Nat) :
    language (exactRepeat p count) = language p ^ count := language_pow p count

theorem mem_language_exactRepeat (p : Regex α) (count : Nat) (w : List α) :
    w ∈ language (exactRepeat p count) ↔
      ∃ factors : List (List α), w = factors.flatten ∧ factors.length = count ∧
        ∀ factor ∈ factors, factor ∈ language p := by
  rw [language_exactRepeat, Language.mem_pow]

/-- At most `count` factors: some power of the operand's language up to
`count`. -/
theorem mem_language_atMostRepeat (p : Regex α) (count : Nat) (w : List α) :
    w ∈ language (atMostRepeat p count) ↔ ∃ used, used ≤ count ∧ w ∈ language p ^ used := by
  induction count generalizing w with
  | zero =>
      change w ∈ (1 : Language α) ↔ _
      constructor
      · intro empty
        exact ⟨0, le_rfl, by simpa using empty⟩
      · rintro ⟨used, bound, member⟩
        obtain rfl : used = 0 := Nat.le_zero.mp bound
        simpa using member
  | succ count ih =>
      change w ∈ (1 : Language α) + language p * language (atMostRepeat p count) ↔ _
      rw [Language.mem_add, Language.mem_one, Language.mem_mul]
      constructor
      · rintro (rfl | ⟨first, firstMember, rest, restMember, rfl⟩)
        · exact ⟨0, Nat.zero_le _, by simp⟩
        · obtain ⟨used, bound, member⟩ := (ih rest).mp restMember
          refine ⟨used + 1, Nat.succ_le_succ bound, ?_⟩
          rw [pow_succ']
          exact Language.mem_mul.mpr ⟨first, firstMember, rest, member, rfl⟩
      · rintro ⟨used, bound, member⟩
        cases used with
        | zero => exact Or.inl (by simpa using member)
        | succ used =>
            rw [pow_succ'] at member
            obtain ⟨first, firstMember, rest, restMember, rfl⟩ := Language.mem_mul.mp member
            exact Or.inr ⟨first, firstMember, rest,
              (ih rest).mpr ⟨used, Nat.le_of_succ_le_succ bound, restMember⟩, rfl⟩

/-- Bounded repetition accepts exactly the powers whose factor counts lie
between its inclusive bounds. -/
theorem mem_language_boundedRepeat (p : Regex α) (lower upper : Nat) (w : List α) :
    w ∈ language (boundedRepeat p lower upper) ↔
      ∃ count, lower ≤ count ∧ count ≤ upper ∧ w ∈ language p ^ count := by
  unfold boundedRepeat
  split
  · next ordered =>
      rw [language_mul, language_pow, Language.mem_mul]
      constructor
      · rintro ⟨first, firstMember, rest, restMember, rfl⟩
        obtain ⟨used, bound, member⟩ := (mem_language_atMostRepeat p _ rest).mp restMember
        refine ⟨lower + used, Nat.le_add_right _ _, by omega, ?_⟩
        rw [pow_add]
        exact Language.mem_mul.mpr ⟨first, firstMember, rest, member, rfl⟩
      · rintro ⟨count, lowerBound, upperBound, member⟩
        obtain ⟨used, rfl⟩ := Nat.exists_eq_add_of_le lowerBound
        rw [pow_add] at member
        obtain ⟨first, firstMember, rest, restMember, rfl⟩ := Language.mem_mul.mp member
        exact ⟨first, firstMember, rest,
          (mem_language_atMostRepeat p _ rest).mpr ⟨used, by omega, restMember⟩, rfl⟩
  · next reversed =>
      constructor
      · intro member
        exact False.elim (Language.notMem_zero _ member)
      · rintro ⟨count, lowerBound, upperBound, _⟩
        exact False.elim (reversed (lowerBound.trans upperBound))

/-- The count bounds constrain the number of accepted factors, including empty
factors, rather than the length of the resulting word. -/
theorem mem_language_boundedRepeat_factors (p : Regex α) (lower upper : Nat) (w : List α) :
    w ∈ language (boundedRepeat p lower upper) ↔
      ∃ factors : List (List α), lower ≤ factors.length ∧ factors.length ≤ upper ∧
        w = factors.flatten ∧ ∀ factor ∈ factors, factor ∈ language p := by
  rw [mem_language_boundedRepeat]
  constructor
  · rintro ⟨count, hlower, hupper, hw⟩
    obtain ⟨factors, hword, hcount, hall⟩ := Language.mem_pow.mp hw
    exact ⟨factors, hcount ▸ hlower, hcount ▸ hupper, hword, hall⟩
  · rintro ⟨factors, hlower, hupper, hword, hall⟩
    exact ⟨factors.length, hlower, hupper,
      Language.mem_pow.mpr ⟨factors, hword, rfl, hall⟩⟩

theorem language_boundedRepeat_of_reversed (p : Regex α) {lower upper : Nat}
    (h : upper < lower) : language (boundedRepeat p lower upper) = 0 := by
  ext w
  rw [mem_language_boundedRepeat]
  constructor
  · rintro ⟨count, hlower, hupper, _⟩
    exact False.elim ((Nat.not_le.mpr h) (hlower.trans hupper))
  · exact fun hw => False.elim (Language.notMem_zero _ hw)

/-- A range with equal bounds accepts exactly that many factors. -/
theorem language_boundedRepeat_self (p : Regex α) (count : Nat) :
    language (boundedRepeat p count count) = language p ^ count := by
  ext w
  rw [mem_language_boundedRepeat]
  constructor
  · rintro ⟨used, lowerBound, upperBound, member⟩
    obtain rfl : used = count := Nat.le_antisymm upperBound lowerBound
    exact member
  · intro member
    exact ⟨count, le_rfl, le_rfl, member⟩

namespace RepetitionControls

/-- Two and three Unicode characters are both accepted by the inclusive range. -/
theorem bounded_unicode_accepts_two :
    fullMatch (boundedRepeat (literal 'λ') 2 3) ['λ', 'λ'] = true := by
  decide

theorem bounded_unicode_accepts_three :
    fullMatch (boundedRepeat (literal 'λ') 2 3) ['λ', 'λ', 'λ'] = true := by
  decide

theorem bounded_unicode_rejects_one :
    fullMatch (boundedRepeat (literal 'λ') 2 3) ['λ'] = false := by
  decide

theorem bounded_unicode_rejects_four :
    fullMatch (boundedRepeat (literal 'λ') 2 3) ['λ', 'λ', 'λ', 'λ'] = false := by
  decide

/-- Reversing the bounds accepts neither the empty word nor a literal. -/
theorem reversed_bounds_reject_empty :
    fullMatch (boundedRepeat (literal 'λ') 3 2) [] = false := by
  decide

theorem reversed_bounds_reject_literal :
    fullMatch (boundedRepeat (literal 'λ') 3 2) ['λ'] = false := by
  decide

/-- Three repetitions of a nullable operand can consume no characters. -/
theorem nullable_operand_accepts_empty :
    fullMatch (boundedRepeat (optional (literal 'λ')) 3 3) [] = true := by
  decide

/-- The same three factors can consume just one character. -/
theorem nullable_operand_accepts_one :
    fullMatch (boundedRepeat (optional (literal 'λ')) 3 3) ['λ'] = true := by
  decide

theorem nullable_operand_rejects_four :
    fullMatch (boundedRepeat (optional (literal 'λ')) 3 3) ['λ', 'λ', 'λ', 'λ'] = false := by
  decide

/-- A range holds one copy of its operand for each count up to the upper
bound: here two for the lower bound and one for the difference. -/
theorem bounded_range_is_linear :
    boundedRepeat (literal 'λ') 2 3 =
      (literal 'λ') ^ 2 * (1 + literal 'λ' * 1) := rfl

end RepetitionControls

end Mettapedia.Computability.RegularLanguages
