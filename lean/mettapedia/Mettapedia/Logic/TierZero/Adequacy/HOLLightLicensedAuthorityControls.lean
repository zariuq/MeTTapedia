import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedPublication

/-! # Private availability witnesses cannot be supplied or minted publicly -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedAuthorityControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open HOLLightContextActivation (Entry)
open HOLLightLicensedActivation

theorem command_availability_has_private_location {O : Type*} [DecidableEq O]
    {contexts : Nat → TheoryContext} (entry : Entry contexts)
    (raw : RuleInstance InferenceSchemaKernel.Value) (location : O → Location) (payload : O → Tm)
    {before : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
      (commandRule entry raw) before) (token : O) (rest : List O) (selected : picked.read = token :: rest) :
    location token = licenses := by
  have matched := LocatedSubstitution.read_locations action location payload qualified
  rw [selected] at matched
  cases matched with
  | cons same _ => exact same.symm

theorem public_availability_row_refused {O : Type*} [DecidableEq O]
    {contexts : Nat → TheoryContext} (entry : Entry contexts)
    (raw : RuleInstance InferenceSchemaKernel.Value) (location : O → Location) (payload : O → Tm)
    (before : Configuration Value O) (picked : Selection O)
    (token : O) (rest : List O) (selected : picked.read = token :: rest) (publicHere : location token = requests) :
    ¬picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence)) (commandRule entry raw) before := by
  intro qualified
  have privateHere := command_availability_has_private_location entry raw location payload qualified token rest selected
  rw [publicHere] at privateHere
  cases privateHere

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO} [DecidableEq O]
    {policy : AxiomPolicy} [DecidablePred policy] {contexts : Nat → TheoryContext}
    {entries : Nat → Option (Entry contexts)} {location : O → Location}

theorem client_cannot_create_private_license
    (system : HOLLightLicensedPublication.System policy contexts entries C X I O location)
    (payload : O → Tm) {actor : I} (client : actor ≠ system.authority.kernel)
    {before after : Configuration Value O} (step : system.Step payload actor before after)
    (token : O) (where_ : location token = licenses) (afterHere : token ∈ after.present) : token ∈ before.present := by
  apply system.authority.nonwriter_creates_no_protected_occurrence system.activate locatedAction
    (fun occurrence => (location occurrence, payload occurrence)) client step afterHere
  rw [HOLLightLicensedPublication.protectedOccurrence, where_]
  decide

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedAuthorityControls
