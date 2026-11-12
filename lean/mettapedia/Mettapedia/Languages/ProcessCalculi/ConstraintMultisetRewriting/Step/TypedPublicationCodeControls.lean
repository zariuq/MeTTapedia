import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationCodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationOutputControls

/-!
# Typed equality does not erase code-origin observations

The two actual beta-equal readings of a Ground endofunction realize the
same typed value, with different raw codes. A source or runtime observer
that inspects those codes cannot be identified with a typed-equality observer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CodeControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open TypedPublicationAgreementControls

def declared : Code scope := .value (Output.unchanged OutputControls.monomorphicOutput.value)

theorem identity_license : declared.At identityReading :=
  NativeTypesOnTheStep.below_refl_of_isType
    (OutputControls.monomorphicOutput.value.1.reindex identityReading).isType

theorem expanded_license : declared.At expandedReading :=
  NativeTypesOnTheStep.below_refl_of_isType
    (OutputControls.monomorphicOutput.value.1.reindex expandedReading).isType

theorem same_typed_readout :
    (frames levels).E (declared.readout identityReading identity_license)
      (declared.readout expandedReading expanded_license) :=
  declared.readout_agree levels readings_agree identity_license expanded_license

theorem different_raw_readouts :
    (declared.readout identityReading identity_license).2.code ≠
      (declared.readout expandedReading expanded_license).2.code := by
  intro same
  cases same

theorem typed_observation_and_raw_observation_differ :
    (frames levels).E (declared.readout identityReading identity_license)
      (declared.readout expandedReading expanded_license) ∧
    (declared.readout identityReading identity_license).2.code ≠
      (declared.readout expandedReading expanded_license).2.code :=
  ⟨same_typed_readout, different_raw_readouts⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CodeControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CodeControls.typed_observation_and_raw_observation_differ
