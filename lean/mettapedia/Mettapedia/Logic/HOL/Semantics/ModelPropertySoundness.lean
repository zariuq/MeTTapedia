import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Soundness over property-defined classes of Henkin models

This module connects independent model properties to the existing HOL
soundness theorems.  It does not select a named HOL implementation or add
choice and infinity axioms to the calculus.

The extensional derivation overlay consumes exactly
`FunctionsRespectEqv`.  Full domains are one sufficient condition, while an
`ExtensionalChoiceInfinity` value supplies the same condition directly.  The
choice and infinity components are deliberately unused until a calculus with
corresponding object-level axioms is specified.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

namespace Soundness

/-- Every theorem of the extensional calculus is valid in a full-domain
Henkin model. -/
theorem extTheorem_sound_of_fullDomains
    {φ : ClosedFormula Const} (d : ExtDerivation.Theorem Const φ)
    (M : HenkinModel.{u, v, w} Base Const) (hFull : M.FullDomains) :
    M.models φ :=
  extTheorem_sound d M (M.functionsRespectEqv_of_fullDomains hFull)

/-- Every theorem of the extensional calculus is valid in a model carrying
the extensionality/choice/infinity property bundle.  Only its extensionality
field is needed for this calculus. -/
theorem extTheorem_sound_of_extensionalChoiceInfinity
    {φ : ClosedFormula Const} (d : ExtDerivation.Theorem Const φ)
    (M : HenkinModel.{u, v, w} Base Const) (b : Base)
    (properties : M.ExtensionalChoiceInfinity b) : M.models φ :=
  extTheorem_sound d M properties.extensional

/-- A full-domain Henkin model separates the extensional calculus from
falsity. -/
theorem no_extTheorem_bot_of_fullDomains
    (M : HenkinModel.{u, v, w} Base Const) (hFull : M.FullDomains) :
    ¬ ExtDerivation.Theorem Const (.bot : ClosedFormula Const) := by
  intro derivesBottom
  exact M.models_bot
    (extTheorem_sound_of_fullDomains derivesBottom M hFull)

/-- The combined model-property bundle likewise separates the extensional
calculus from falsity. -/
theorem no_extTheorem_bot_of_extensionalChoiceInfinity
    (M : HenkinModel.{u, v, w} Base Const) (b : Base)
    (properties : M.ExtensionalChoiceInfinity b) :
    ¬ ExtDerivation.Theorem Const (.bot : ClosedFormula Const) := by
  intro derivesBottom
  exact M.models_bot
    (extTheorem_sound_of_extensionalChoiceInfinity
      derivesBottom M b properties)

/-! ## Concrete controls -/

open HenkinModel.ModelPropertyCanary

/-- Positive control: every closed extensional theorem is valid in the
standard natural-number base model. -/
theorem naturalBaseModel_validates_extTheorem
    {φ : ClosedFormula (HenkinModel.ModelPropertyCanary.NoConstants Unit)}
    (d : ExtDerivation.Theorem
      (HenkinModel.ModelPropertyCanary.NoConstants Unit) φ) :
    naturalBaseModel.models φ :=
  extTheorem_sound_of_fullDomains d naturalBaseModel
    naturalBaseModel_fullDomains

/-- Negative control: falsity has no proof in the extensional calculus over
the empty constant family. -/
theorem naturalBaseModel_rejects_extensional_bottom :
    ¬ ExtDerivation.Theorem
      (HenkinModel.ModelPropertyCanary.NoConstants Unit)
      (.bot : ClosedFormula
        (HenkinModel.ModelPropertyCanary.NoConstants Unit)) :=
  no_extTheorem_bot_of_fullDomains naturalBaseModel
    naturalBaseModel_fullDomains

end Soundness

end Mettapedia.Logic.HOL
