import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionEquationModel
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws

/-!
# Matching-colour canonicalization of generated collection laws

Both generated parallel declarations have an actual sorted empty-unit law.
The declaration retained by that occurrence determines its reflective
absorber. In particular the base canonicalizer does not absorb the wrapped
unit equation; a uniform base-only absorption claim would be false.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionCanonicalControls

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
open GeneratedCollectionEquationModel

/-- The actual declaration and its empty collection typing produce the raw
presentation-derived occurrence, independently of its canonical readout. -/
def emptyUnitOccurrence (color : CostStaticColor) :
    DerivedGeneratorWitness language (.collection .hashBag [] none)
      (.apply (unitName color) []) :=
  .emptyUnit (parallelRule color) .hashBag (parallelAlgebra color)
    (unitName color) (parallelDeclaration color) rfl
    ⟨WellSorted.FreeTypeContext.empty, [], .collectionConstructor
      (parallel_member color) (parallel_shape color) (.nil _ _)⟩

theorem emptyUnit_declared (color : CostStaticColor) :
    DerivedInstance language (.collection .hashBag [] none)
      (.apply (unitName color) []) :=
  (emptyUnitOccurrence color).erase

/-- Selection computes from the actual generated rule, without a supplied
normalizer or a choice of an absorbing declaration. -/
theorem emptyUnit_color (color : CostStaticColor) :
    rhoCostDerivedGeneratorColor (emptyUnitOccurrence color) = color := by
  cases color <;> rfl

theorem emptyUnit_absorbed (color : CostStaticColor) :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
        (.collection .hashBag [] none) =
      canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply (unitName color) []) := by
  simpa only [emptyUnit_color] using
    rho_costDerivedGenerator_canonicalize_eq (emptyUnitOccurrence color)

/-- The same actual wrapped law refutes absorption by a fixed base
canonicalizer. This does not refute matching-colour absorption. -/
theorem wrapped_unit_not_absorbed_by_base :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl)
        (.collection .hashBag [] none) ≠
      canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply (unitName .wrapped) []) := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionCanonicalControls
