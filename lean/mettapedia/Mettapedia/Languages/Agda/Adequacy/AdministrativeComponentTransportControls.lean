import Mettapedia.Languages.Agda.Adequacy.AdministrativeComponentTransport
import Mettapedia.Languages.Agda.Structural.AdministrativeBinderPreservationControls

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.ComponentTransport

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Structural
open Structural.Statics (RawTm RawTy RawContext TypeParameter TypeBody)
open Structural.AdministrativeStatics

namespace Controls

abbrev sourceDomain : StaticSpecification.Ty 0 := .universe 1
abbrev sourceContext : StaticSpecification.RawContext 1 := .snoc .nil sourceDomain
abbrev nativeContext : RawContext 1 := BinderPreservationControls.empty.snoc BinderPreservationControls.adminDomain.code

def sourceDomainFormed : StaticSpecification.FormTy .nil sourceDomain :=
  .ofTyping (.sort 1 .nil)

def sourceContextFormed : StaticSpecification.FormCtx sourceContext :=
  .snoc .nil sourceDomainFormed

noncomputable def returnedContext : IdentityReturn sourceContext nativeContext :=
  administrativeOperations.changeLastSubstitution BinderPreservationControls.domainFormed
    BinderPreservationControls.adminDomainFormed BinderPreservationControls.domainEquality.typeSymmetry

abbrev sourceDependent : StaticSpecification.Ty 1 := .el 1 (.var 0)
abbrev nativeDependent : RawTy 1 := (TypeParameter.mk (n := 1) 1 (eliminate (.var .zero) nil)).code
abbrev canonicalDependent : RawTy 1 := (TypeParameter.mk (n := 1) 1 (.var .zero)).code

def sourceDependentEquality : StaticSpecification.TypeEq sourceContext sourceDependent sourceDependent :=
  .atSort (.refl (.var 0 sourceContextFormed))

noncomputable def dependentCanonization : CoreDerivation
    (Statics.typeEqual nativeContext nativeDependent canonicalDependent) :=
  Derivation.core (.typeEquality nativeContext 1 (eliminate (.var .zero) nil) (.var .zero))
    (consEvidence CoreDerivation (Derivation.emptyElimination BinderPreservationControls.adminVariable)
      (noEvidence CoreDerivation))

noncomputable def dependentReturned : CoreDerivation
    (Statics.typeEqual nativeContext nativeDependent canonicalDependent) :=
  bridgeTypeEquality returnedContext (A := sourceDependent) (B := sourceDependent) dependentCanonization
    dependentCanonization.typeEndpoints.right.typeReflexivity sourceDependentEquality

theorem dependent_observation : Observation.type nativeDependent = some sourceDependent := rfl

theorem context_observation : Observation.context nativeContext = some sourceContext := rfl

theorem contexts_are_raw_distinct : nativeContext ≠ embedContext sourceContext := by
  intro same
  cases same

theorem readback_keeps_no_administrative_wrapper : nativeDependent ≠ embedTy sourceDependent := by
  intro same
  cases same

end Controls
end Mettapedia.Languages.Agda.StaticAdequacy.ComponentTransport
