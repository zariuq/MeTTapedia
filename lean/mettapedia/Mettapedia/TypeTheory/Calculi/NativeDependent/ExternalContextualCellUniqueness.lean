import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualPresentation
import Mettapedia.GSLT.Core.ContextualPseudoCwfTransformation

/-!
# Corrected contextual cells are determined on chosen presentations

The finite selected-comprehension presentation covers every admitted context
up to its earned conversion isomorphism. Naturality transports equality of
base components through that comparison. The shared corrected CwF cell
theorem then determines the full displayed component from its actual
comprehension square.

This proves uniqueness of supplied coherent cells from their presentation
components. It does not construct a model morphism or a cell, nor assert
classifying initiality from their hypothetical existence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Presentation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

universe u v w
variable {S : Symbols.{u}} {D : Signature S}

noncomputable def baseComparison (context : (QuotientCwf.cwf D).base.Context) :
    (⟨(quotientNormalizer D).obj context.val⟩ : (QuotientCwf.cwf D).base.Context) ≅ context where
  hom := (quotientComparison context.val).hom
  inv := (quotientComparison context.val).inv
  hom_inv_id := (quotientComparison context.val).hom_inv_id
  inv_hom_id := (quotientComparison context.val).inv_hom_id

theorem baseNatTrans_ext_chosen {Target : Type v} [Category.{w} Target]
    {first second : (QuotientCwf.cwf D).base.Context ⥤ Target}
    (left right : first ⟶ second)
    (onChosen : ∀ context, Chosen D context.val.as → left.app context = right.app context) :
    left = right := by
  apply NatTrans.ext
  funext context
  let arrow := (baseComparison context).hom
  apply (cancel_epi (first.map arrow)).mp
  rw [left.naturality, right.naturality]
  rw [onChosen ⟨(quotientNormalizer D).obj context.val⟩ (quotientNormalizer_chosen context.val)]

theorem correctedCell_ext_chosen {Target : CwfWithTerminal.{u, u, u, u}}
    {first second : PseudoCwfMorphism (QuotientCwf.withTerminal D) Target}
    (left right : CorrectedTransformationData first second)
    (onChosen : ∀ context, Chosen D context.as → left.base.app ⟨context⟩ = right.base.app ⟨context⟩) :
    left = right := by
  apply CorrectedTransformationData.ext_of_base_eq
  exact baseNatTrans_ext_chosen left.base right.base (fun context chosen => onChosen context.val chosen)

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Presentation
