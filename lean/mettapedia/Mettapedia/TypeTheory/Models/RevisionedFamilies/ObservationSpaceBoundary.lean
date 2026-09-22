import Mettapedia.TypeTheory.Calculi.StagedScopedReflective.Presentation
import Mettapedia.PLN.WorldModel.WMCalculusNativeSpace

/-!
# Extensional type spaces are the support of multiplicity world-model spaces

The staged-reflective candidate interprets a type as a `Pattern → Prop`
space. A multiplicity WM space has a sound support projection into that
extensional type space. It preserves union as logical join and meet as
logical meet, but it forgets counts: equal type-space support does not imply
WM behavioral agreement. Thus this existing type interpretation can consume
the support of a WM space, but cannot by itself be the semantic authority
for PLN evidence or multiplicity-sensitive revision.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.ObservationSpaceBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading

/-- Forget multiplicities but retain which patterns are present. -/
def support (space : MSpace Pattern) : Space :=
  fun pattern => 0 < space pattern

/-- Membership in the candidate type-space interpretation is precisely
positive multiplicity in the WM space. -/
theorem mem_support_iff (space : MSpace Pattern) (pattern : Pattern) :
    Space.Mem pattern (support space) ↔ 0 < space pattern :=
  Iff.rfl

/-- Additive WM revision projects to join in the extensional type-space
lattice, though the latter no longer records how many sources contributed. -/
theorem support_union (first second : MSpace Pattern) :
    support (sUnion first second) =
      Space.union (support first) (support second) := by
  funext pattern
  apply propext
  change 0 < first pattern + second pattern ↔
    0 < first pattern ∨ 0 < second pattern
  omega

/-- Pointwise multiplicity meet projects to type-space intersection. -/
theorem support_meet (first second : MSpace Pattern) :
    support (sMeet first second) =
      Space.inter (support first) (support second) := by
  funext pattern
  apply propext
  change 0 < min (first pattern) (second pattern) ↔
    0 < first pattern ∧ 0 < second pattern
  omega

/-- Any extensional type-space can be represented by a zero-or-one
multiplicity space. The section is semantic and uses decidability of
membership; it does not make extensional join additive revision. -/
noncomputable def zeroOneLift (typeSpace : Space) : MSpace Pattern := by
  classical
  exact fun pattern => if typeSpace pattern then 1 else 0

/-- Support recovers the original candidate type-space interpretation. -/
theorem support_zeroOneLift (typeSpace : Space) :
    support (zeroOneLift typeSpace) = typeSpace := by
  classical
  funext pattern
  apply propext
  by_cases present : typeSpace pattern <;>
    simp [support, zeroOneLift, present]

/-- The section does not preserve joins: two overlapping type spaces
collapse to one support element, while WM revision records two occurrences. -/
theorem zeroOneLift_union_not_revision :
    ∃ first second : Space,
      zeroOneLift (Space.union first second) ≠
        sUnion (zeroOneLift first) (zeroOneLift second) := by
  refine ⟨Space.top, Space.top, ?_⟩
  intro same
  have atPattern := congrArg (fun space : MSpace Pattern => space (.fvar "x")) same
  norm_num [zeroOneLift, Space.union, Space.top, sUnion] at atPattern

/-- WM agreement is strong enough to imply equal extensional type-space
supports for the full singleton-candidate reading. -/
theorem wmAgree_implies_same_support
    (world : String → MSpace Pattern)
    (query : String → List Pattern)
    (first second : MSpace Pattern)
    (agree : (additiveReading (Ev := ℕ) world query).Agree
      .state first second) :
    support first = support second := by
  have same := (Mettapedia.PLN.WorldModel.WMCalculusNativeSpace.spaceAgree_iff_eq
    world query first second).mp agree
  rw [same]

/-- The converse fails: one and two occurrences have the same type-space
support but different WM answers to a singleton query. -/
theorem same_support_not_wmAgree :
    ∃ first second : MSpace Pattern,
      support first = support second ∧
        ¬ (additiveReading (Ev := ℕ)
          (fun _ => first) (fun _ => ([] : List Pattern))).Agree
          .state first second := by
  let first : MSpace Pattern := fun _ => 1
  let second : MSpace Pattern := fun _ => 2
  refine ⟨first, second, ?_, ?_⟩
  · funext pattern
    apply propext
    simp [support, first, second]
  · intro agree
    have one := agree [.fvar "x"]
    change weightedAnswers first [.fvar "x"] =
      weightedAnswers second [.fvar "x"] at one
    norm_num [weightedAnswers, first, second] at one

end Mettapedia.TypeTheory.Models.RevisionedFamilies.ObservationSpaceBoundary
