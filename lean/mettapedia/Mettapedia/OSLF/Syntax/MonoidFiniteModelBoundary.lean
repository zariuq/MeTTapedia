import Mettapedia.OSLF.Syntax.MonoidAuthoredComparison
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Finset.Max

/-!
# Finite monoid axioms do not make every model finitely generated

The Chapter 7 monoid presentation has three equations. That finite axiom
list specifies a theory, while models of the theory may use infinitely many
generators. The free monoid on natural-number letters is a concrete control:
the letters appearing in any finite proposed generating set form a finite
support, and concatenation cannot introduce a new letter.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.MonoidFiniteModelBoundary

/-- Letters present in a finite family of words. -/
noncomputable def support (generators : Finset (FreeMonoid Nat)) : Finset Nat :=
  (generators.toList.flatMap FreeMonoid.toList).toFinset

/-- The submonoid of words using only a given finite alphabet. -/
def wordsOver (letters : Finset Nat) : Submonoid (FreeMonoid Nat) where
  carrier := {word | ∀ letter ∈ FreeMonoid.toList word, letter ∈ letters}
  one_mem' := by simp
  mul_mem' := by
    intro left right leftAllowed rightAllowed letter member
    rcases List.mem_append.mp
      (show letter ∈ FreeMonoid.toList left ++ FreeMonoid.toList right from
        by simpa using member) with fromLeft | fromRight
    · exact leftAllowed letter fromLeft
    · exact rightAllowed letter fromRight

theorem generator_uses_support
    (generators : Finset (FreeMonoid Nat))
    {word : FreeMonoid Nat} (member : word ∈ generators) :
    word ∈ wordsOver (support generators) := by
  intro letter inWord
  change letter ∈ (generators.toList.flatMap FreeMonoid.toList).toFinset
  rw [List.mem_toFinset]
  exact List.mem_flatMap.mpr
    ⟨word, Finset.mem_toList.mpr member, inWord⟩

theorem closure_uses_support
    (generators : Finset (FreeMonoid Nat)) :
    Submonoid.closure (generators : Set (FreeMonoid Nat)) ≤
      wordsOver (support generators) := by
  apply Submonoid.closure_le.mpr
  intro word member
  exact generator_uses_support generators member

/-- A finite alphabet has a fresh natural-number letter. -/
theorem fresh_letter (letters : Finset Nat) :
    ∃ letter : Nat, letter ∉ letters := by
  refine ⟨letters.sup id + 1, ?_⟩
  intro member
  have bound : letters.sup id + 1 ≤ letters.sup id :=
    Finset.le_sup (f := id) member
  omega

/-- No finite set of words generates the free monoid on countably many
letters. This is the exact failure relevant to confusing finite equations
with finite generation of all their models. -/
theorem freeMonoid_nat_not_finitely_generated :
    ¬ ∃ generators : Finset (FreeMonoid Nat),
      Submonoid.closure (generators : Set (FreeMonoid Nat)) = ⊤ := by
  rintro ⟨generators, generates⟩
  obtain ⟨letter, fresh⟩ := fresh_letter (support generators)
  have memberClosure :
      FreeMonoid.of letter ∈
        Submonoid.closure (generators : Set (FreeMonoid Nat)) := by
    rw [generates]
    trivial
  have memberSupport :=
    closure_uses_support generators memberClosure
  have included : letter ∈ support generators := by
    exact memberSupport letter (by simp)
  exact fresh included

/-- The finite-alphabet case remains a positive control: the singleton words
over a finite alphabet generate every word by concatenation. -/
theorem freeMonoid_fin_finitely_generated (arity : Nat) :
    ∃ generators : Finset (FreeMonoid (Fin arity)),
      Submonoid.closure (generators : Set (FreeMonoid (Fin arity))) = ⊤ := by
  classical
  let generators : Finset (FreeMonoid (Fin arity)) :=
    Finset.univ.image FreeMonoid.of
  refine ⟨generators, ?_⟩
  apply top_unique
  intro word _
  induction word using FreeMonoid.inductionOn' with
  | one => exact one_mem _
  | of_mul letter tail inductionHypothesis =>
      have singletonMember : FreeMonoid.of letter ∈
          (generators : Set (FreeMonoid (Fin arity))) := by
        simp [generators]
      exact mul_mem (Submonoid.subset_closure singletonMember)
        (inductionHypothesis (by trivial))

/-- The actual three-row authored monoid theory has a model whose underlying
monoid is not finitely generated. The rows describe algebraic laws; they do
not place a finite-generation bound on every interpretation. -/
theorem authored_monoid_has_non_finitely_generated_model :
    MonoidAuthoredComparison.authored.equations.length = 3 ∧
    (∀ a b c : FreeMonoid Nat, (a * b) * c = a * (b * c)) ∧
    (∀ a : FreeMonoid Nat, 1 * a = a ∧ a * 1 = a) ∧
    ¬ ∃ generators : Finset (FreeMonoid Nat),
      Submonoid.closure (generators : Set (FreeMonoid Nat)) = ⊤ := by
  refine ⟨by decide, ?_, ?_, freeMonoid_nat_not_finitely_generated⟩
  · intro a b c
    exact mul_assoc a b c
  · intro a
    exact ⟨one_mul a, mul_one a⟩

end Mettapedia.OSLF.Binding.MonoidFiniteModelBoundary
