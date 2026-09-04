import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryDescent
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.A2sRouteCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

private def declaration : ReflectivePresentationDecl :=
  rhoReflectivePresentation.toReflectivePresentationDecl

/-- Positive falsification control: a unit sibling disappears beside the
bound-variable contributor, so a variable-valued parallel need not have a
literal singleton element list. -/
example : canonicalize declaration
    (.collection declaration.parallelCollection
      [.bvar 2, .apply declaration.parallelUnitConstructor []] none) =
      .bvar 2 := by
  apply canonicalize_parallel_units_around declaration
      (before := []) (after := [.apply declaration.parallelUnitConstructor []])
      (mid := .bvar 2)
  · simp
  · intro sibling membership
    simp only [List.mem_singleton] at membership
    subst sibling
    rw [canonicalize_apply_of_ne_quote]
    · rfl
    · decide
  · simp [canonicalize]
  · simp
  · simp

/-- The literal-singleton inversion proposed in the stale probe is false. -/
example : ¬ (∀ (elements : List Pattern) (index : Nat),
    canonicalize declaration
        (.collection declaration.parallelCollection elements none) =
      .bvar index → elements = [.bvar index]) := by
  intro alleged
  have impossible := alleged
    [.bvar 2, .apply declaration.parallelUnitConstructor []] 2 (by
      apply canonicalize_parallel_units_around declaration
          (before := [])
          (after := [.apply declaration.parallelUnitConstructor []])
          (mid := .bvar 2)
      · simp
      · intro sibling membership
        simp only [List.mem_singleton] at membership
        subst sibling
        rw [canonicalize_apply_of_ne_quote]
        · rfl
        · decide
      · simp [canonicalize]
      · simp
      · simp)
  cases impossible

/-- Positive route invariant: although literal singleton shape is false, an
actual contributor in the variable canonical class always exists. -/
example (elements : List Pattern) (index : Nat)
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) =
      .bvar index) :
    ∃ element ∈ elements, canonicalize declaration element = .bvar index :=
  exists_member_of_parallel_collapse_bvar declaration collapsed

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.A2sRouteCanary
