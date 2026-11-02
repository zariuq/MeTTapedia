import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiNamedAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerControls

/-!
# Controls: named π at the front door

- **Unfolding is a law**: `!a(x).0` and `a(x).0 | !a(x).0` have translations `piCalc`'s static theory identifies
  (`server_static_same`), and they satisfy the same forward formulas under named partners
  (`server_agrees_unfolded`), being structurally congruent in the named calculus.
- **Two copies of a server are one** in `piCalc`'s static theory (`duplicates_static_same`), a law strong
  bisimilarity validates beyond the named congruence.
- **A partner separates what has no step of its own**: `x(y).0` and `0` are not saturated reduction bisimilar in the
  named calculus (`receiver_not_inaction`), decided at the front door beside the named output `x⟨w⟩`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiNamedControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc piToPattern)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiNamed
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartners (frontDoor decided_holds decided_fails)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerControls (beside receiver sender
  receiver_steps_beside_sender inaction_stuck_beside_sender)

/-- **Structurally congruent named processes are saturated reduction bisimilar.** -/
theorem saturated_of_congruent {first second : Process}
    (congruent : Mettapedia.Languages.ProcessCalculi.PiCalculus.Congruent first second) :
    SaturatedReductionBisimilar first second :=
  saturated_congruent (SaturatedReductionBisimilar.refl first)
    (Mettapedia.Languages.ProcessCalculi.PiCalculus.Congruent.refl first) congruent

/-- A server, `!a(x).0`. -/
def server : Process := .replicate "a" "x" .nil

/-- The server unfolded, `a(x).0 | !a(x).0`. -/
def unfolded : Process := .par (.input "a" "x" .nil) server

/-- **`piCalc`'s static theory identifies the server and its unfolding.** -/
theorem server_static_same :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (piToPattern server) (piToPattern unfolded) :=
  PrenexForm.equationEquiv_of_structural (.replicate_unfold "a" "x" .nil)

/-- **Two copies of a server are one** in `piCalc`'s static theory. -/
theorem duplicates_static_same :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (piToPattern (.par server server)) (piToPattern server) :=
  PrenexForm.duplicates_identified

/-- **And they have the same native types under named partners.** -/
theorem server_agrees_unfolded :
    frontDoor.AgreeOn (Formula.forwardOn isNamedPartnerLabel) (piToPattern server) (piToPattern unfolded) :=
  agree_iff_named.mpr (saturated_of_congruent ⟨.replicate_unfold "a" "x" .nil⟩)

theorem receiver_translation : piToPattern (.input "x" "y" .nil) = receiver := by decide +kernel

/-- **`x(y).0` and `0` are not saturated reduction bisimilar**: beside the named output `x⟨w⟩` the input steps and
inaction does not. -/
theorem receiver_not_inaction : ¬ SaturatedReductionBisimilar (.input "x" "y" .nil) .nil := by
  intro bisimilar
  have agree := agree_iff_named.mpr bisimilar
  have forward : (Formula.possibly (beside sender) .top : Formula 0).forwardOn isNamedPartnerLabel = true := by
    decide +kernel
  rw [receiver_translation] at agree
  exact inaction_stuck_beside_sender ((agree _ forward).mp receiver_steps_beside_sender)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiNamedControls
