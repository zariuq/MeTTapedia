import Mettapedia.GSLT.LanguageDef.Gauthier.PatternSourceSupport
import Mathlib.Data.Set.Card

/-!
# Anti-unification and completion weakness

Plotkin least-general generalization and Michael Timothy Bennett's weakness
optimize opposite directions unless the candidate fibre has additional
constraints.  An LGG is the most specific common generalizer.  Therefore its
set of matching programs in a fixed finite presentation is contained in the
matching set of every other common generalizer.

This file gives the exact characterization: the LGG is weakness-maximal among
role-correct common generalizers iff every such generalizer has the same
presentation-relative completion set as the LGG.  A two-example presentation
satisfies the premise.  Adding a third mixed example gives a strict
counterexample: a fresh-hole generalizer covers it, while the memoized LGG's
repeated hole correctly retains an equality constraint and rejects it.

Thus anti-unification and Bennett's Razor are complementary.  LGG preserves
the strongest common structure; weakness chooses the least commitment only
after the admissible hypothesis fibre and observation presentation are fixed.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.AntiUnificationWeakness

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierE2
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierPatternSupport

universe u

variable {σ : Type u}

/-! ## Finite presentation-relative completion sets -/

/-- Programs in a fixed finite presentation that instantiate a pattern. -/
def completionSet (presentation : Finset Prog) (pattern : Pattern) : Set Prog :=
  {program | program ∈ presentation ∧ Matches pattern program}

theorem completionSet_finite (presentation : Finset Prog) (pattern : Pattern) :
    (completionSet presentation pattern).Finite := by
  exact presentation.finite_toSet.subset fun _ member => member.1

/-- Bennett weakness of a pattern relative to a fixed finite presentation. -/
noncomputable def weakness (presentation : Finset Prog) (pattern : Pattern) : ℕ :=
  (completionSet presentation pattern).ncard

/-- Specialization cannot increase match freedom. -/
theorem completionSet_mono {general specific : Pattern}
    (order : MoreGeneral general specific) (presentation : Finset Prog) :
    completionSet presentation specific ⊆ completionSet presentation general := by
  intro program member
  exact ⟨member.1, matches_mono_moreGeneral order member.2⟩

theorem weakness_mono {general specific : Pattern}
    (order : MoreGeneral general specific) (presentation : Finset Prog) :
    weakness presentation specific ≤ weakness presentation general := by
  exact Set.ncard_le_ncard
    (completionSet_mono order presentation)
    (completionSet_finite presentation general)

/-- Plotkin leastness makes LGG completion weakness a lower bound among common
generalizers, not an upper bound. -/
theorem lgg_weakness_le_commonGeneralizer
    {sig : Signature σ} {role : HoleRole} {pattern : Pattern}
    {left right : Prog} (generalizer : Generalizes sig role pattern left right)
    (presentation : Finset Prog) :
    weakness presentation (lgg sig role left right) ≤
      weakness presentation pattern :=
  weakness_mono (lgg_least generalizer) presentation

/-- The condition under which the LGG also maximizes Bennett weakness in the
common-generalizer fibre. -/
def LGGWeaknessMaximal (sig : Signature σ) (role : HoleRole)
    (presentation : Finset Prog) (left right : Prog) : Prop :=
  ∀ pattern, Generalizes sig role pattern left right →
    weakness presentation pattern ≤
      weakness presentation (lgg sig role left right)

/-- Exact characterization: because the LGG match set is already included in
every common generalizer's match set, it can be weakness-maximal precisely
when none of those inclusions adds a presented program. -/
theorem lggWeaknessMaximal_iff_completionSet_eq
    (sig : Signature σ) (role : HoleRole)
    (presentation : Finset Prog) (left right : Prog) :
    LGGWeaknessMaximal sig role presentation left right ↔
      ∀ pattern, Generalizes sig role pattern left right →
        completionSet presentation pattern =
          completionSet presentation (lgg sig role left right) := by
  constructor
  · intro maximal pattern generalizer
    have included :
        completionSet presentation (lgg sig role left right) ⊆
          completionSet presentation pattern :=
      completionSet_mono (lgg_least generalizer) presentation
    have equal := Set.eq_of_subset_of_ncard_le included
      (maximal pattern generalizer)
      (completionSet_finite presentation pattern)
    exact equal.symm
  · intro equalCompletions pattern generalizer
    exact le_of_eq (by
      simpa [weakness] using
        congrArg Set.ncard (equalCompletions pattern generalizer))

/-! ## Positive control: the exact two-example presentation -/

def pairPresentation (left right : Prog) : Finset Prog := {left, right}

theorem commonGeneralizer_completionSet_pairPresentation
    {sig : Signature σ} {role : HoleRole} {pattern : Pattern}
    {left right : Prog} (generalizer : Generalizes sig role pattern left right) :
    completionSet (pairPresentation left right) pattern =
      (pairPresentation left right : Set Prog) := by
  apply Set.Subset.antisymm
  · intro program member
    exact member.1
  · intro program member
    simp only [pairPresentation, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with equal | equal
    · subst program
      exact ⟨by simp [pairPresentation],
        ⟨generalizer.leftSubstitution, generalizer.instantiateLeft⟩⟩
    · subst program
      exact ⟨by simp [pairPresentation],
        ⟨generalizer.rightSubstitution, generalizer.instantiateRight⟩⟩

theorem lgg_completionSet_pairPresentation
    (sig : Signature σ) (role : HoleRole) (left right : Prog) :
    completionSet (pairPresentation left right) (lgg sig role left right) =
      (pairPresentation left right : Set Prog) := by
  apply Set.Subset.antisymm
  · intro program member
    exact member.1
  · intro program member
    simp only [pairPresentation, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with equal | equal
    · subst program
      exact ⟨by simp [pairPresentation], lgg_matches_left sig role left right⟩
    · subst program
      exact ⟨by simp [pairPresentation], lgg_matches_right sig role left right⟩

/-- On the presentation containing only the two examples, every common
generalizer covers exactly those examples, so LGG is both least-general and
weakness-maximal. -/
theorem lgg_weaknessMaximal_on_pairPresentation
    (sig : Signature σ) (role : HoleRole) (left right : Prog) :
    LGGWeaknessMaximal sig role (pairPresentation left right) left right := by
  rw [lggWeaknessMaximal_iff_completionSet_eq]
  intro pattern generalizer
  rw [commonGeneralizer_completionSet_pairPresentation generalizer,
    lgg_completionSet_pairPresentation]

/-! ## Negative control: an additional mixed completion -/

namespace MixedCanary

def mixed : Prog := .node 3 [zero, one]

def presentation : Finset Prog := {repeatedLeft, repeatedRight, mixed}

def allZero : TermSubstitution := fun _ => zero
def allOne : TermSubstitution := fun _ => one

theorem fresh_rolesCorrect :
    RolesCorrect orgMemoSignature .root freshAtEveryMismatch := by
  refine RolesCorrect.node
    (entry := entry "addi" 2 0 Prim.addi) rfl rfl ?_
  apply RolesCorrectChildren.cons
  · exact RolesCorrect.hole rfl
  · apply RolesCorrectChildren.cons
    · exact RolesCorrect.hole rfl
    · exact RolesCorrectChildren.nil

theorem instantiate_allZero_fresh :
    instantiate allZero freshAtEveryMismatch = repeatedLeft := by
  simp [allZero, freshAtEveryMismatch, repeatedLeft, instantiate]

theorem instantiate_allOne_fresh :
    instantiate allOne freshAtEveryMismatch = repeatedRight := by
  simp [allOne, freshAtEveryMismatch, repeatedRight, instantiate]

/-- The fresh-hole pattern is a genuine role-correct common generalizer, not a
syntactic comparator outside the admissible fibre. -/
def freshGeneralizes :
    Generalizes orgMemoSignature .root freshAtEveryMismatch
      repeatedLeft repeatedRight where
  roles := fresh_rolesCorrect
  leftSubstitution := allZero
  rightSubstitution := allOne
  instantiateLeft := instantiate_allZero_fresh
  instantiateRight := instantiate_allOne_fresh

def mixedSubstitution : TermSubstitution :=
  fun key => if key = repeatedKey then zero else one

theorem fresh_matches_mixed : Matches freshAtEveryMismatch mixed := by
  refine ⟨mixedSubstitution, ?_⟩
  simp [mixedSubstitution, freshAtEveryMismatch, mixed, instantiate,
    repeatedKey, freshSecondKey, zero, one]

theorem lgg_not_matches_mixed :
    ¬ Matches (lgg orgMemoSignature .root repeatedLeft repeatedRight) mixed := by
  rw [repeated_disagreement_reuses_one_hole]
  exact repeated_hole_rejects_distinct_children

theorem lgg_completionSet_strict_subset_fresh :
    completionSet presentation
        (lgg orgMemoSignature .root repeatedLeft repeatedRight) ⊂
      completionSet presentation freshAtEveryMismatch := by
  rw [repeated_disagreement_reuses_one_hole]
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · exact completionSet_mono fresh_mismatch_specializes_to_memoized presentation
  · intro equalSets
    have mixedInFresh : mixed ∈ completionSet presentation freshAtEveryMismatch :=
      ⟨by simp [presentation], fresh_matches_mixed⟩
    have mixedInMemoized :
        mixed ∈ completionSet presentation
          (.node 3 [.hole repeatedKey, .hole repeatedKey]) := by
      rw [equalSets]
      exact mixedInFresh
    exact repeated_hole_rejects_distinct_children mixedInMemoized.2

theorem lgg_weakness_strictly_less_than_fresh :
    weakness presentation
        (lgg orgMemoSignature .root repeatedLeft repeatedRight) <
      weakness presentation freshAtEveryMismatch := by
  exact Set.ncard_lt_ncard lgg_completionSet_strict_subset_fresh
    (completionSet_finite presentation freshAtEveryMismatch)

/-- Outside the equal-completion premise, LGG is not weakness-maximal. -/
theorem lgg_not_weaknessMaximal :
    ¬ LGGWeaknessMaximal orgMemoSignature .root presentation
      repeatedLeft repeatedRight := by
  intro maximal
  have reverse := maximal freshAtEveryMismatch freshGeneralizes
  exact (Nat.not_le_of_lt lgg_weakness_strictly_less_than_fresh) reverse

end MixedCanary

#print axioms lggWeaknessMaximal_iff_completionSet_eq
#print axioms lgg_weaknessMaximal_on_pairPresentation
#print axioms MixedCanary.lgg_weakness_strictly_less_than_fresh
#print axioms MixedCanary.lgg_not_weaknessMaximal

end Mettapedia.Enactive.AntiUnificationWeakness
