import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionCanonicalControls

/-!
# Colour information lost by raw collection equivalence

The same raw empty bag admits both generated collection declarations. Their
unit laws therefore identify the base and wrapped units in the unindexed raw
equivalence. A fixed-colour canonical readout distinguishes those units and
cannot factor through that equivalence.

The intrinsic binding family keeps the declaring category. Its comparison
with raw equations must retain that sorting evidence rather than recover it
from the erased pattern.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionColorBoundary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open GeneratedCollectionEquationModel GeneratedCollectionCanonicalControls

/-- Each actual declaration equates the erased empty bag with its own unit. -/
theorem empty_unit_equivalent (base : BasePremiseEvaluator) (color : CostStaticColor) :
    EquationEquiv base language (.collection .hashBag [] none)
      (.apply (unitName color) []) :=
  Relation.EqvGen.rel _ _ (.inContext .hole (Or.inr (emptyUnit_declared color)))

/-- Erasing the declaring sort allows the empty bag to connect two distinct
constructor fibres in the actual generated raw equation theory. -/
theorem raw_equivalence_connects_colors (base : BasePremiseEvaluator) :
    EquationEquiv base language (.apply (unitName .base) [])
      (.apply (unitName .wrapped) []) :=
  Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (empty_unit_equivalent base .base))
    (empty_unit_equivalent base .wrapped)

/-- The base readout keeps the two generated units distinct. -/
theorem base_canonicalizer_distinguishes_units :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply (unitName .base) []) ≠
      canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply (unitName .wrapped) []) := by
  intro same
  exact wrapped_unit_not_absorbed_by_base ((emptyUnit_absorbed .base).trans same)

/-- No uniform base-colour readout respects the entire unindexed raw
static equivalence. Matching-colour generator absorption is a different law. -/
theorem no_base_readout_of_raw_equivalence (base : BasePremiseEvaluator) :
    ¬ ∀ left right, EquationEquiv base language left right →
      canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
          rhoReflectivePresentation.toReflectivePresentationDecl) left =
        canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
          rhoReflectivePresentation.toReflectivePresentationDecl) right := by
  intro respects
  exact base_canonicalizer_distinguishes_units
    (respects _ _ (raw_equivalence_connects_colors base))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionColorBoundary
