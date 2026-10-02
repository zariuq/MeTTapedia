import Mettapedia.Computability.RegularLanguages.Regex
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Function.Iterate

/-!
# Language-preserving simplification of derivative expressions

Each simplification is an equation of regular expressions read from its larger
side to its smaller:

* union: the empty language is the unit, and union is associative and
  idempotent, so a union is rebuilt from the distinct alternatives at the
  leaves of its tree of unions;
* concatenation: the empty language absorbs and the empty word is the unit;
* star: the star of the empty language, of the empty word and of a star.

Idempotence is what stops repeated derivatives from doubling. The derivative
of `(a*)*` by `a` holds two copies of the derivative before it; without
idempotence every further letter about doubles the expression, and with it
the derivative by three letters is the derivative by two.

The observation these simplifications preserve is the accepted language, and
simplification never adds a constructor. No bound on the number of simplified
derivatives of an arbitrary expression is proved here, and distinct authored
expressions remain distinct even when they denote the same language.
-/

set_option autoImplicit false

open scoped Computability

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

deriving instance DecidableEq for RegularExpression

/-- The alternatives of an expression: the leaves of its tree of unions,
leaving out the empty language. -/
def alternatives : Regex α → List (Regex α)
  | .zero => []
  | .plus p q => alternatives p ++ alternatives q
  | p => [p]

/-- The union of a list of alternatives. The empty list denotes the empty
language. -/
def unionOf : List (Regex α) → Regex α
  | [] => 0
  | [p] => p
  | p :: q :: rest => p + unionOf (q :: rest)

theorem mem_language_unionOf (list : List (Regex α)) (w : List α) :
    w ∈ language (unionOf list) ↔ ∃ p ∈ list, w ∈ language p := by
  induction list with
  | nil => simp [unionOf]
  | cons p rest ih =>
      cases rest with
      | nil => simp [unionOf]
      | cons q rest =>
          change w ∈ language p + language (unionOf (q :: rest)) ↔ _
          rw [Language.mem_add, ih]
          constructor
          · rintro (first | ⟨r, member, accepted⟩)
            · exact ⟨p, List.mem_cons_self, first⟩
            · exact ⟨r, List.mem_cons_of_mem _ member, accepted⟩
          · rintro ⟨r, member, accepted⟩
            rcases List.mem_cons.mp member with rfl | later
            · exact Or.inl accepted
            · exact Or.inr ⟨r, later, accepted⟩

/-- A word is accepted exactly when one of the alternatives accepts it. -/
theorem mem_language_iff_alternatives (p : Regex α) (w : List α) :
    w ∈ language p ↔ ∃ q ∈ alternatives p, w ∈ language q := by
  induction p with
  | zero => simp [alternatives]
  | epsilon => simp [alternatives]
  | char atom => simp [alternatives]
  | plus p q hp hq =>
      change w ∈ language p + language q ↔ ∃ r ∈ alternatives p ++ alternatives q, _
      rw [Language.mem_add, hp, hq]
      simp only [List.mem_append]
      constructor
      · rintro (⟨r, member, accepted⟩ | ⟨r, member, accepted⟩)
        · exact ⟨r, Or.inl member, accepted⟩
        · exact ⟨r, Or.inr member, accepted⟩
      · rintro ⟨r, member | member, accepted⟩
        · exact Or.inl ⟨r, member, accepted⟩
        · exact Or.inr ⟨r, member, accepted⟩
  | comp p q _ _ => simp [alternatives]
  | star p _ => simp [alternatives]

/-- Number of syntax constructors; distinct authored alternatives remain
distinct even when they denote the same language. -/
def nodeCount : Regex α → Nat
  | .zero | .epsilon | .char _ => 1
  | .plus p q | .comp p q => nodeCount p + nodeCount q + 1
  | .star p => nodeCount p + 1

theorem nodeCount_pos (p : Regex α) : 0 < nodeCount p := by
  cases p <;> simp [nodeCount]

/-- The constructors of a list of alternatives, counting one union for each
alternative. -/
def alternativesWeight (list : List (Regex α)) : Nat :=
  (list.map fun p => nodeCount p + 1).sum

theorem alternativesWeight_append (first second : List (Regex α)) :
    alternativesWeight (first ++ second) =
      alternativesWeight first + alternativesWeight second := by
  simp [alternativesWeight]

theorem alternativesWeight_le_of_sublist {first second : List (Regex α)}
    (sublist : first.Sublist second) :
    alternativesWeight first ≤ alternativesWeight second :=
  (sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _

/-- A union of alternatives has one constructor fewer than their weight. -/
theorem nodeCount_unionOf (list : List (Regex α)) (nonempty : list ≠ []) :
    nodeCount (unionOf list) + 1 = alternativesWeight list := by
  induction list with
  | nil => exact absurd rfl nonempty
  | cons p rest ih =>
      cases rest with
      | nil => simp [unionOf, alternativesWeight]
      | cons q rest =>
          have later := ih (List.cons_ne_nil q rest)
          change nodeCount p + nodeCount (unionOf (q :: rest)) + 1 + 1 =
            (nodeCount p + 1) + alternativesWeight (q :: rest)
          omega

/-- Taking an expression apart into its alternatives adds no constructor. -/
theorem alternativesWeight_alternatives_le (p : Regex α) :
    alternativesWeight (alternatives p) ≤ nodeCount p + 1 := by
  induction p with
  | zero => simp [alternatives, alternativesWeight]
  | epsilon => simp [alternatives, alternativesWeight]
  | char atom => simp [alternatives, alternativesWeight]
  | plus p q hp hq =>
      change alternativesWeight (alternatives p ++ alternatives q) ≤
        nodeCount p + nodeCount q + 1 + 1
      rw [alternativesWeight_append]
      omega
  | comp p q _ _ => simp [alternatives, alternativesWeight]
  | star p _ => simp [alternatives, alternativesWeight]

def smartConcat : Regex α → Regex α → Regex α
  | .zero, _ => 0
  | _, .zero => 0
  | .epsilon, q => q
  | p, .epsilon => p
  | p, q => p * q

/-- The star of the empty language and of the empty word is the empty word;
the star of a star is that star. -/
def smartStar : Regex α → Regex α
  | .zero => 1
  | .epsilon => 1
  | .star p => p.star
  | p => p.star

@[simp] theorem language_smartConcat (p q : Regex α) :
    language (smartConcat p q) = language p * language q := by
  cases p <;> cases q <;> simp [smartConcat]

@[simp] theorem language_smartStar (p : Regex α) :
    language (smartStar p) = (language p)∗ := by
  cases p <;> simp [smartStar]

theorem smartConcat_nodeCount_le (p q : Regex α) :
    nodeCount (smartConcat p q) ≤ nodeCount p + nodeCount q + 1 := by
  cases p <;> cases q <;> simp [smartConcat, nodeCount] <;> omega

theorem smartStar_nodeCount_le (p : Regex α) :
    nodeCount (smartStar p) ≤ nodeCount p + 1 := by
  cases p <;> simp [smartStar, nodeCount]

section Simplification
variable [DecidableEq α]

/-- Union up to its unit, associativity and idempotence: the distinct
alternatives of the two operands. -/
def smartUnion (p q : Regex α) : Regex α :=
  unionOf (alternatives p ++ alternatives q).dedup

@[simp] theorem language_smartUnion (p q : Regex α) :
    language (smartUnion p q) = language p + language q := by
  ext w
  rw [smartUnion, mem_language_unionOf, Language.mem_add,
    mem_language_iff_alternatives p, mem_language_iff_alternatives q]
  simp only [List.mem_dedup, List.mem_append]
  constructor
  · rintro ⟨r, member | member, accepted⟩
    · exact Or.inl ⟨r, member, accepted⟩
    · exact Or.inr ⟨r, member, accepted⟩
  · rintro (⟨r, member, accepted⟩ | ⟨r, member, accepted⟩)
    · exact ⟨r, Or.inl member, accepted⟩
    · exact ⟨r, Or.inr member, accepted⟩

theorem smartUnion_nodeCount_le (p q : Regex α) :
    nodeCount (smartUnion p q) ≤ nodeCount p + nodeCount q + 1 := by
  have weight : alternativesWeight (alternatives p ++ alternatives q).dedup ≤
      nodeCount p + nodeCount q + 2 := by
    refine (alternativesWeight_le_of_sublist (List.dedup_sublist _)).trans ?_
    rw [alternativesWeight_append]
    have left := alternativesWeight_alternatives_le p
    have right := alternativesWeight_alternatives_le q
    omega
  unfold smartUnion
  by_cases empty : (alternatives p ++ alternatives q).dedup = []
  · rw [empty]
    have positive := nodeCount_pos p
    change 1 ≤ nodeCount p + nodeCount q + 1
    omega
  · have exact := nodeCount_unionOf _ empty
    omega

/-- A structural simplifier, with language equality as its contract. -/
def normalize : Regex α → Regex α
  | .zero => 0
  | .epsilon => 1
  | .char atom => .char atom
  | .plus p q => smartUnion (normalize p) (normalize q)
  | .comp p q => smartConcat (normalize p) (normalize q)
  | .star p => smartStar (normalize p)

@[simp] theorem normalize_language (p : Regex α) :
    language (normalize p) = language p := by
  induction p with
  | zero => rfl
  | epsilon => rfl
  | char _ => rfl
  | plus p q hp hq =>
      change language (smartUnion (normalize p) (normalize q)) = language p + language q
      rw [language_smartUnion, hp, hq]
  | comp p q hp hq =>
      change language (smartConcat (normalize p) (normalize q)) = language p * language q
      rw [language_smartConcat, hp, hq]
  | star p hp =>
      change language (smartStar (normalize p)) = (language p)∗
      rw [language_smartStar, hp]

theorem normalize_nodeCount_le (p : Regex α) : nodeCount (normalize p) ≤ nodeCount p := by
  induction p with
  | zero => exact le_rfl
  | epsilon => exact le_rfl
  | char _ => exact le_rfl
  | plus p q hp hq =>
      exact (smartUnion_nodeCount_le _ _).trans
        (Nat.add_le_add_right (Nat.add_le_add hp hq) 1)
  | comp p q hp hq =>
      exact (smartConcat_nodeCount_le _ _).trans
        (Nat.add_le_add_right (Nat.add_le_add hp hq) 1)
  | star p hp =>
      exact (smartStar_nodeCount_le _).trans (Nat.add_le_add_right hp 1)

def normalizedDerivative (a : α) (p : Regex α) : Regex α := normalize (derivative a p)

theorem normalizedDerivative_language (a : α) (p : Regex α) :
    language (normalizedDerivative a p) = leftDerivative a (language p) := by
  rw [normalizedDerivative, normalize_language, derivative_language]

/-- A matcher that simplifies after each derivative. It consumes the
original word exactly once; its semantic guarantee is independent of size. -/
def matchNormalized : Regex α → List α → Bool
  | p, [] => p.matchEpsilon
  | p, a :: rest => matchNormalized (normalizedDerivative a p) rest

theorem matchNormalized_correct (p : Regex α) (word : List α) :
    matchNormalized p word = true ↔ word ∈ language p := by
  induction word generalizing p with
  | nil => exact nullable_correct p
  | cons a rest ih =>
      rw [matchNormalized, ih, normalizedDerivative_language, mem_leftDerivative]

theorem matchNormalized_eq_fullMatch (p : Regex α) (word : List α) :
    matchNormalized p word = fullMatch p word := by
  exact Bool.eq_iff_iff.mpr ((matchNormalized_correct p word).trans (fullMatch_correct p word).symm)

end Simplification

namespace NormalizationControls

theorem removes_empty_branch : normalize (0 + literal 'λ') = literal 'λ' := by decide

theorem removes_unit_factor : normalize (1 * literal 'λ') = literal 'λ' := by decide

/-- A repeated alternative is kept once, wherever it sits in the union. -/
theorem removes_repeated_alternative :
    normalize (literal 'λ' + (literal 'β' + literal 'λ')) = literal 'β' + literal 'λ' := by
  decide

theorem removes_star_of_star :
    normalize (literal 'λ').star.star = (literal 'λ').star := by decide

/-- Distinct alternatives are all kept. -/
theorem keeps_distinct_alternatives :
    normalize (literal 'λ' + literal 'β') = literal 'λ' + literal 'β' := by decide

/-- Language simplification does not claim the original source was identical. -/
theorem different_source_same_language :
    (0 + literal 'λ' : Regex Char) ≠ literal 'λ' ∧
      language (0 + literal 'λ') = language (literal 'λ') := by
  constructor
  · intro h
    cases h
  · simp

theorem normalized_nullable_concat :
    matchNormalized ((1 + literal 'λ') * literal 'β') ['β'] = true := by decide

theorem normalized_wrong_letter : matchNormalized (literal 'λ') ['β'] = false := by decide

/-- The star of a star of a letter. -/
def starOfStar : Regex Char := (literal 'a').star.star

/-- Without simplification every further letter about doubles the derivative. -/
theorem unsimplified_derivatives_grow :
    (List.range 6).map (fun count =>
        nodeCount (derivatives starOfStar (List.replicate count 'a'))) =
      [3, 8, 22, 50, 106, 218] := by decide

/-- With simplification the derivative by three letters is the derivative by
two. -/
theorem simplified_derivative_fixed :
    normalizedDerivative 'a'
        (normalizedDerivative 'a' (normalizedDerivative 'a' starOfStar)) =
      normalizedDerivative 'a' (normalizedDerivative 'a' starOfStar) := by decide

/-- So the simplifying matcher meets the same expression at every letter
after the second, however long the word. -/
theorem simplified_derivatives_stabilize (count : Nat) :
    (normalizedDerivative 'a')^[count + 2] starOfStar =
      (normalizedDerivative 'a')^[2] starOfStar := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (normalizedDerivative 'a')^[(count + 2).succ] starOfStar = _
      rw [Function.iterate_succ_apply', ih]
      exact simplified_derivative_fixed

theorem simplified_derivative_size :
    nodeCount ((normalizedDerivative 'a')^[2] starOfStar) = 8 := by decide

end NormalizationControls

end Mettapedia.Computability.RegularLanguages
