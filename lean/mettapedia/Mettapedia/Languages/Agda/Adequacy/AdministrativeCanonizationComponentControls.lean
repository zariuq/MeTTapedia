import Mettapedia.Languages.Agda.Adequacy.AdministrativeCanonizationComponents
import Mettapedia.Languages.Agda.Adequacy.AdministrativeCanonizationControls

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Canonization.ComponentControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Structural
open Structural.Statics (TypeBody)
open Structural.AdministrativeStatics
open BinderPreservationControls

abbrev wrappedFamily : TypeBody 0 := .bind ⟨1, eliminate (.var .zero) nil⟩

noncomputable def wrappedPiTyped : CoreDerivation
    (Statics.typed empty (wrappedFamily.pi adminDomain) (Statics.universeType 0 2).code) :=
  Derivation.core (.pi empty adminDomain wrappedFamily)
    (consEvidence CoreDerivation adminDomainFormed
      (consEvidence CoreDerivation ComponentTransport.Controls.dependentCanonization.typeEndpoints.left
        (noEvidence CoreDerivation)))

noncomputable def wrappedPiFormed : CoreDerivation
    (Statics.formed empty (Statics.piType adminDomain wrappedFamily).code) :=
  Derivation.core (.formation empty 2 (wrappedFamily.pi adminDomain))
    (consEvidence CoreDerivation wrappedPiTyped (noEvidence CoreDerivation))

noncomputable def wrappedPiEquality : CoreDerivation
    (Statics.typeEqual empty (Statics.piType adminDomain wrappedFamily).code
      (Statics.piType domain dependentFamily).code) :=
  (formation wrappedPiFormed).at
    (a := .pi (.universe 1) (.bind (.el 1 (.var 0)))) rfl

def sourceDomainEquality : StaticSpecification.TypeEq .nil
    (StaticSpecification.Ty.universe 1) (StaticSpecification.Ty.universe 1) :=
  .atSort (.refl (.sort 1 .nil))

noncomputable def components :
    CoreDerivation (Statics.typeEqual empty adminDomain.code domain.code) ×
      CoreDerivation (Statics.typeEqual (empty.snoc adminDomain.code)
        wrappedFamily.open.code dependentFamily.open.code) :=
  transportObservedPiComponents wrappedPiEquality
    (Δ := .nil) (a := .universe 1) (a' := .universe 1)
    (b := .bind (.el 1 (.var 0))) (b' := .bind (.el 1 (.var 0)))
    rfl rfl rfl rfl rfl sourceDomainEquality ComponentTransport.Controls.sourceDependentEquality

noncomputable def returnedRightCodomain : CoreDerivation
    (Statics.formed (empty.snoc adminDomain.code) dependentFamily.open.code) :=
  components.2.typeEndpoints.right

theorem domain_canonization_is_not_raw_equality : adminDomain.code ≠ domain.code := by
  intro same
  cases same

theorem codomain_canonization_is_not_raw_equality : wrappedFamily.open.code ≠ dependentFamily.open.code := by
  intro same
  cases same

theorem extended_context_changes : empty.snoc adminDomain.code ≠ empty.snoc domain.code :=
  dependent_context_codes_change

end Mettapedia.Languages.Agda.StaticAdequacy.Canonization.ComponentControls
