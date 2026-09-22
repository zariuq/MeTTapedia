import Mettapedia.TypeTheory.DisplayedPresheafCwf
import Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge

/-!
# Comparison of the two proof-relevant semantic CwF views

The fixed-syntax presheaf CwF extends a context by a total presheaf; the
category-indexed CwF extends the category of elements by the displayed
family. Their established equivalence is compatible with the canonical
dependent variable and with base-change substitutions. This does not
identify arbitrary categories with presheaf contexts or supply Pi types.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafCwfIndexedComparison

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafCwf
open Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf

universe u

variable {Context : Type u} [Category.{u} Context]

/-- Regrouping the total-context point into indexed comprehension does not
change the evidence read by its canonical dependent last variable. -/
theorem variable_agrees_with_indexed
    {base : Face.{u, u, u} Context}
    (family : DisplayedFamily.{u, u, u, u} base)
    (point : (totalSpace family).Elements) :
    (presheafVariable family).val point =
      (lastVariable (context := Cat.of base.Elements) family).val
        ((totalElementsToDisplayed family).obj point) := by
  rfl

/-- The presheaf CwF's generic extension substitution and the indexed
comprehension's reindexing commute under the established arrow-level
equivalence, not merely at object values. -/
theorem substitution_lift_agrees_with_indexed
    {source target : Face.{u, u, u} Context}
    (substitution : source ⟶ target)
    (family : DisplayedFamily.{u, u, u, u} target) :
    (show totalSpace (reindexDisplayed substitution family) ⟶
        totalSpace family from
      Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := presheafCwf Context) substitution family).mapElements ⋙
        totalElementsToDisplayed family =
      totalElementsToDisplayed (reindexDisplayed substitution family) ⋙
        reindexedElementsToOriginal substitution family := by
  rw [extensionSubstitution_eq_totalReindexMap]
  exact totalElementsEquivalence_baseChange substitution family

/-- The two CwF views reindex the same natural dependent section by the
same functor on categories of elements. This is an equality of sections,
not merely of their values at one point. -/
theorem section_reindex_agrees_with_indexed
    {source target : Face.{u, u, u} Context}
    (substitution : source ⟶ target)
    (family : DisplayedFamily.{u, u, u, u} target)
    (sectionValue : family.sections) :
    reindexDisplayedSection substitution family sectionValue =
      reindexSection (source := Cat.of source.Elements)
        (target := Cat.of target.Elements) sectionValue
        substitution.mapElements := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

#print axioms variable_agrees_with_indexed
#print axioms substitution_lift_agrees_with_indexed
#print axioms section_reindex_agrees_with_indexed

end Mettapedia.TypeTheory.DisplayedPresheafCwfIndexedComparison
