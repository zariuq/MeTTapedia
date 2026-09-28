import Mettapedia.Languages.Agda.Structural.AdministrativeCompatibleResults
import Mettapedia.Languages.Agda.Structural.AdministrativeBinderPreservationControls

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Statics (RawTm RawTy RawContext)

namespace Controls

noncomputable def bindingSource := includePrior Statics.RegularityControls.combinedBody

noncomputable def bindingLambdaSource : CoreDerivation (Statics.typed Statics.RegularityControls.empty
    (lam (eliminate (Statics.universeTerm (n := 1) 0) nil))
    (Statics.piType Statics.RegularityControls.domain Statics.RegularityControls.codomain).code) :=
  Derivation.core (.lambda _ Statics.RegularityControls.domain Statics.RegularityControls.codomain
    (.bind (eliminate (Statics.universeTerm (n := 1) 0) nil)))
    (consEvidence CoreDerivation (includeCanonical Statics.RegularityControls.domainFormed)
      (consEvidence CoreDerivation (includeCanonical Statics.RegularityControls.codomainFormed)
        (consEvidence CoreDerivation bindingSource (noEvidence CoreDerivation))))

noncomputable def nonbindingLambdaSource : CoreDerivation (Statics.typed Statics.RegularityControls.empty
    (lamNoAbs (eliminate (Statics.universeTerm (n := 0) 0) nil))
    (Statics.piType Statics.RegularityControls.domain Statics.RegularityControls.codomain).code) :=
  Derivation.core (.lambda _ Statics.RegularityControls.domain Statics.RegularityControls.codomain
    (.noBind (eliminate (Statics.universeTerm (n := 0) 0) nil)))
    (consEvidence CoreDerivation (includeCanonical Statics.RegularityControls.domainFormed)
      (consEvidence CoreDerivation (includeCanonical Statics.RegularityControls.codomainFormed)
        (consEvidence CoreDerivation bindingSource (noEvidence CoreDerivation))))




noncomputable def convertedLambda (beta : BetaCases) : CoreDerivation
    (Statics.typed BinderPreservationControls.empty (lam (.var .zero)) BinderPreservationControls.expandedFunction) :=
  conditionalTermPreservation beta BinderPreservationControls.bindingCertificate.step BinderPreservationControls.convertedBindingSource

noncomputable def dependentPi (beta : BetaCases) : CoreDerivation
    (Statics.typed BinderPreservationControls.empty (BinderPreservationControls.dependentFamily.pi BinderPreservationControls.domain) (Statics.universeType 0 2).code) :=
  conditionalTermPreservation beta
    (Preservation.piDomain (A := BinderPreservationControls.adminDomain) (A' := BinderPreservationControls.domain) BinderPreservationControls.dependentFamily BinderPreservationControls.domainCertificate).step
    BinderPreservationControls.dependentPiSource

noncomputable def freeNoAbs (beta : BetaCases) : CoreDerivation
    (Statics.typed BinderPreservationControls.one (lamNoAbs (.var .zero)) (Statics.piType BinderPreservationControls.secondDomain BinderPreservationControls.secondCodomain).code) :=
  conditionalTermPreservation beta BinderPreservationControls.nonbindingCertificate.step BinderPreservationControls.nonbindingSource

noncomputable def boundCodomain (beta : BetaCases) :=
  conditionalTermPreservation beta (Preservation.piCodomain BinderPreservationControls.domain BinderPreservationControls.openedDomainCertificate).step BinderPreservationControls.boundPiSource

noncomputable def noAbsCodomain (beta : BetaCases) :=
  conditionalTermPreservation beta
    (Preservation.piNoAbsCodomain BinderPreservationControls.domain BinderPreservationControls.domainCertificate BinderPreservationControls.openedDomainCertificate).step BinderPreservationControls.nonbindingPiSource

def replaceFree : Statics.RawSub 1 0 :=
  Telescope.pair (Telescope.identity (S := sig) .term 0) (Statics.universeTerm 0)

noncomputable def substitutedNoAbs (beta : BetaCases) : CoreDerivation
    (Statics.termEqual BinderPreservationControls.empty
      (lamNoAbs (eliminate (Statics.universeTerm 0) nil)) (lamNoAbs (Statics.universeTerm 0))
      BinderPreservationControls.functionType.code) :=
  compatible beta BinderPreservationControls.nonbindingCertificate.step replaceFree _ _ nonbindingLambdaSource

noncomputable def freeBindingStep : Step
    (lam (eliminate (.var (.succ .zero)) nil) : RawTm 1) (lam (.var (.succ .zero))) :=
  (Preservation.lambdaBind (Preservation.eliminateEmpty (.var (.succ .zero) : RawTm 2))).step

noncomputable def substitutedBinding (beta : BetaCases) : CoreDerivation
    (Statics.termEqual BinderPreservationControls.empty
      (lam (eliminate (Statics.universeTerm (n := 1) 0) nil)) (lam (Statics.universeTerm (n := 1) 0))
      BinderPreservationControls.functionType.code) :=
  compatible beta freeBindingStep replaceFree _ _ bindingLambdaSource

theorem lifted_substitution_does_not_capture :
    bind (Telescope.lift replaceFree) (.var .zero : RawTm 2) ≠
      bind (Telescope.lift replaceFree) (.var (.succ .zero) : RawTm 2) := by
  intro same
  cases same

theorem converted_lambda_does_not_use_beta (first second : BetaCases) : convertedLambda first = convertedLambda second := rfl

theorem noabs_opening_does_not_use_beta (first second : BetaCases) : freeNoAbs first = freeNoAbs second := rfl

end Controls
end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation
