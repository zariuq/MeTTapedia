import Mettapedia.Computability.RegularLanguages.Regex
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Powerset

/-!
# The languages of regular expressions are regular

A language is regular when a finite automaton accepts it, and by the
Myhill–Nerode theorem when it has finitely many left quotients. A finite
family of languages that is closed under removing a first letter contains
every left quotient of each of its members, so each member is regular.

For a product `L * M` the family consists of the languages `A * M + ⋃ S`
with `A` a left quotient of `L` and `S` a set of left quotients of `M`. For a
star `L∗` it consists of `L∗` and the languages `(⋃ S) * L∗` with `S` a set of
left quotients of `L`. Both are finite when `L` and `M` are regular, which
gives closure of the regular languages under concatenation and star.

The language of every expression is therefore regular, over any alphabet and
with the wildcard, and so is the language Mathlib assigns to its own regular
expressions.
-/

set_option autoImplicit false

open scoped Computability

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

/-- The left quotient by a word with one more letter at its end. -/
theorem leftQuotient_concat (L : Language α) (word : List α) (a : α) :
    L.leftQuotient (word ++ [a]) = leftDerivative a (L.leftQuotient word) :=
  Language.leftQuotient_append L word [a]

/-- Removing a first letter from a left quotient gives a left quotient. -/
theorem leftDerivative_mem_range_leftQuotient (L : Language α) (a : α) {K : Language α}
    (member : K ∈ Set.range L.leftQuotient) :
    leftDerivative a K ∈ Set.range L.leftQuotient := by
  obtain ⟨word, rfl⟩ := member
  exact ⟨word ++ [a], leftQuotient_concat L word a⟩

/-- **A finite family of languages closed under removing a first letter
consists of regular languages.** -/
theorem isRegular_of_finite_closed {family : Set (Language α)} (finite : family.Finite)
    (closed : ∀ K ∈ family, ∀ a, leftDerivative a K ∈ family) {L : Language α}
    (member : L ∈ family) : L.IsRegular := by
  apply Language.IsRegular.of_finite_range_leftQuotient
  refine finite.subset ?_
  rintro _ ⟨word, rfl⟩
  induction word using List.reverseRecOn with
  | nil => exact member
  | append_singleton word a ih =>
      rw [leftQuotient_concat]
      exact closed _ ih a

/-- A word of a union of languages is a word of one of them. -/
theorem mem_sSup_iff (S : Set (Language α)) (w : List α) :
    w ∈ sSup S ↔ ∃ K ∈ S, w ∈ K :=
  Set.mem_sUnion

/-- A word of a union of languages followed by a language. -/
theorem mem_sSup_mul_iff (S : Set (Language α)) (M : Language α) (w : List α) :
    w ∈ sSup S * M ↔ ∃ K ∈ S, w ∈ K * M := by
  constructor
  · intro member
    obtain ⟨first, firstMember, rest, restMember, rfl⟩ := Language.mem_mul.mp member
    obtain ⟨K, inS, inK⟩ := (mem_sSup_iff S first).mp firstMember
    exact ⟨K, inS, Language.mem_mul.mpr ⟨first, inK, rest, restMember, rfl⟩⟩
  · rintro ⟨K, inS, member⟩
    obtain ⟨first, firstMember, rest, restMember, rfl⟩ := Language.mem_mul.mp member
    exact Language.mem_mul.mpr
      ⟨first, (mem_sSup_iff S first).mpr ⟨K, inS, firstMember⟩, rest, restMember, rfl⟩

theorem isRegular_zero : (0 : Language α).IsRegular :=
  isRegular_of_finite_closed (family := {0}) (Set.finite_singleton _)
    (by rintro K rfl a; exact leftDerivative_zero a) rfl

theorem isRegular_one : (1 : Language α).IsRegular :=
  isRegular_of_finite_closed (family := {1, 0}) (Set.toFinite _)
    (by
      rintro K (rfl | rfl) a
      · exact Or.inr (leftDerivative_one a)
      · exact Or.inr (leftDerivative_zero a))
    (Or.inl rfl)

/-- The language of a literal and the language of the wildcard are regular,
whatever the alphabet. -/
theorem isRegular_atomLanguage (atom : Atom α) : (atomLanguage atom).IsRegular := by
  classical
  refine isRegular_of_finite_closed (family := {atomLanguage atom, 1, 0}) (Set.toFinite _) ?_
    (Or.inl rfl)
  rintro K (rfl | rfl | rfl) a
  · rw [leftDerivative_atomLanguage]
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr (leftDerivative_one a))
  · exact Or.inr (Or.inr (leftDerivative_zero a))

/-- The family for a product. -/
def productFamily (L M : Language α) : Set (Language α) :=
  Set.image2 (fun A S => A * M + sSup S) (Set.range L.leftQuotient)
    (𝒫 (Set.range M.leftQuotient))

theorem productFamily_finite {L M : Language α}
    (left : (Set.range L.leftQuotient).Finite) (right : (Set.range M.leftQuotient).Finite) :
    (productFamily L M).Finite :=
  Set.Finite.image2 _ left right.powerset

theorem mem_productFamily (L M : Language α) : L * M ∈ productFamily L M := by
  refine ⟨L, ⟨[], rfl⟩, ∅, Set.empty_subset _, ?_⟩
  ext w
  simp

theorem productFamily_closed (L M : Language α) (K : Language α)
    (member : K ∈ productFamily L M) (a : α) : leftDerivative a K ∈ productFamily L M := by
  obtain ⟨A, inLeft, S, inRight, rfl⟩ := member
  refine ⟨leftDerivative a A, leftDerivative_mem_range_leftQuotient L a inLeft,
    leftDerivative a '' S ∪ {B | B = leftDerivative a M ∧ [] ∈ A}, ?_, ?_⟩
  · rintro B (⟨C, inS, rfl⟩ | ⟨rfl, _⟩)
    · exact leftDerivative_mem_range_leftQuotient M a (inRight inS)
    · exact ⟨[a], rfl⟩
  · ext w
    simp only [mem_leftDerivative, Language.mem_add, mem_sSup_iff]
    rw [← mem_leftDerivative, mem_leftDerivative_mul]
    constructor
    · rintro (product | ⟨B, ⟨C, inS, rfl⟩ | ⟨rfl, empty⟩, accepted⟩)
      · exact Or.inl (Or.inl product)
      · exact Or.inr ⟨C, inS, accepted⟩
      · exact Or.inl (Or.inr ⟨empty, accepted⟩)
    · rintro ((product | ⟨empty, accepted⟩) | ⟨C, inS, accepted⟩)
      · exact Or.inl product
      · exact Or.inr ⟨leftDerivative a M, Or.inr ⟨rfl, empty⟩, accepted⟩
      · exact Or.inr ⟨leftDerivative a C, Or.inl ⟨C, inS, rfl⟩, accepted⟩

/-- **The regular languages are closed under concatenation.** -/
theorem isRegular_mul {L M : Language α} (left : L.IsRegular) (right : M.IsRegular) :
    (L * M).IsRegular :=
  isRegular_of_finite_closed
    (productFamily_finite left.finite_range_leftQuotient right.finite_range_leftQuotient)
    (productFamily_closed L M) (mem_productFamily L M)

/-- The family for a star. -/
def starFamily (L : Language α) : Set (Language α) :=
  insert (L∗) ((fun S => sSup S * L∗) '' 𝒫 (Set.range L.leftQuotient))

theorem starFamily_finite {L : Language α} (finite : (Set.range L.leftQuotient).Finite) :
    (starFamily L).Finite :=
  (finite.powerset.image _).insert _

theorem starFamily_closed (L : Language α) (K : Language α)
    (member : K ∈ starFamily L) (a : α) : leftDerivative a K ∈ starFamily L := by
  rcases member with rfl | ⟨S, inRange, rfl⟩
  · refine Or.inr ⟨{leftDerivative a L}, ?_, ?_⟩
    · rintro B rfl
      exact ⟨[a], rfl⟩
    · show sSup {leftDerivative a L} * L∗ = leftDerivative a (L∗)
      rw [sSup_singleton, leftDerivative_kstar]
  · refine Or.inr
      ⟨leftDerivative a '' S ∪ {B | B = leftDerivative a L ∧ ∃ C ∈ S, [] ∈ C}, ?_, ?_⟩
    · rintro B (⟨C, inS, rfl⟩ | ⟨rfl, _⟩)
      · exact leftDerivative_mem_range_leftQuotient L a (inRange inS)
      · exact ⟨[a], rfl⟩
    · show sSup _ * L∗ = leftDerivative a (sSup S * L∗)
      ext w
      rw [mem_leftDerivative, mem_sSup_mul_iff, mem_sSup_mul_iff]
      constructor
      · rintro ⟨B, ⟨C, inS, rfl⟩ | ⟨rfl, C, inS, empty⟩, accepted⟩
        · exact ⟨C, inS, (mem_leftDerivative_mul a C (L∗) w).mpr (Or.inl accepted)⟩
        · refine ⟨C, inS, (mem_leftDerivative_mul a C (L∗) w).mpr (Or.inr ⟨empty, ?_⟩)⟩
          rw [leftDerivative_kstar]
          exact accepted
      · rintro ⟨C, inS, accepted⟩
        rcases (mem_leftDerivative_mul a C (L∗) w).mp accepted with product | ⟨empty, later⟩
        · exact ⟨leftDerivative a C, Or.inl ⟨C, inS, rfl⟩, product⟩
        · rw [leftDerivative_kstar] at later
          exact ⟨leftDerivative a L, Or.inr ⟨rfl, C, inS, empty⟩, later⟩

/-- **The regular languages are closed under star.** -/
theorem isRegular_kstar {L : Language α} (regular : L.IsRegular) : (L∗).IsRegular :=
  isRegular_of_finite_closed (starFamily_finite regular.finite_range_leftQuotient)
    (starFamily_closed L) (Or.inl rfl)

/-- **The language of a regular expression is regular.** -/
theorem language_isRegular (p : Regex α) : (language p).IsRegular := by
  induction p with
  | zero => exact isRegular_zero
  | epsilon => exact isRegular_one
  | char atom => exact isRegular_atomLanguage atom
  | plus p q hp hq => exact hp.add hq
  | comp p q hp hq => exact isRegular_mul hp hq
  | star p hp => exact isRegular_kstar hp

/-- An expression has finitely many derivatives up to their languages. -/
theorem finite_derivative_languages [DecidableEq α] (p : Regex α) :
    (Set.range fun word => language (derivatives p word)).Finite := by
  have quotients := (language_isRegular p).finite_range_leftQuotient
  refine quotients.subset ?_
  rintro _ ⟨word, rfl⟩
  exact ⟨word, (derivatives_language p word).symm⟩

/-- The language Mathlib assigns to one of its regular expressions is
regular. -/
theorem matches'_isRegular (p : RegularExpression α) : p.matches'.IsRegular :=
  ofRegular_language p ▸ language_isRegular (ofRegular p)

namespace RegularityControls

/-- Regular over an infinite alphabet, with the wildcard. -/
example : (language ((any : Regex ℕ).star * literal 0)).IsRegular := language_isRegular _

/-- The words with as many zeros as ones are not the language of an
expression: removing `n` leading zeros gives a different language for each
`n`. -/
def balanced : Language Bool := {w | w.count false = w.count true}

theorem balanced_quotients_differ {first second : ℕ} (different : first ≠ second) :
    balanced.leftQuotient (List.replicate first false) ≠
      balanced.leftQuotient (List.replicate second false) := by
  intro same
  have member : List.replicate first true ∈
      balanced.leftQuotient (List.replicate first false) := by
    change (List.replicate first false ++ List.replicate first true).count false =
      (List.replicate first false ++ List.replicate first true).count true
    simp [List.count_append, List.count_replicate]
  rw [same] at member
  change (List.replicate second false ++ List.replicate first true).count false =
    (List.replicate second false ++ List.replicate first true).count true at member
  simp [List.count_append, List.count_replicate] at member
  exact different member.symm

theorem balanced_not_regular : ¬ balanced.IsRegular := by
  intro regular
  have finite := regular.finite_range_leftQuotient
  have injective : Function.Injective fun count : ℕ =>
      balanced.leftQuotient (List.replicate count false) := by
    intro first second same
    by_contra different
    exact balanced_quotients_differ different same
  exact Set.infinite_range_of_injective injective
    (finite.subset (by rintro _ ⟨count, rfl⟩; exact ⟨_, rfl⟩))

/-- So no expression denotes it. -/
theorem balanced_not_expressible (p : Regex Bool) : language p ≠ balanced :=
  fun same => balanced_not_regular (same ▸ language_isRegular p)

end RegularityControls

end Mettapedia.Computability.RegularLanguages
