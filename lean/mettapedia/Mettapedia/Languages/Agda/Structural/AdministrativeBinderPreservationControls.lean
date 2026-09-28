import Mettapedia.Languages.Agda.Structural.AdministrativeBinderPreservation
import Mettapedia.Languages.Agda.Structural.AdministrativePreservationControls

/-!
# Binder and type preservation controls

Binding and nonbinding lambdas retain their variable occurrences. A converted
lambda keeps its changed result annotation. Dependent Pi domain contraction
changes the extended context while retaining a codomain using its newest
variable. Finite type levels remain fixed; reducible neutral levels are raw
syntax without a formation derivation in this static fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.BinderPreservationControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Statics (RawTm RawTy RawContext TypeParameter TypeBody)
open Preservation

abbrev empty : RawContext 0 := .nil
abbrev domain : TypeParameter 0 := Statics.universeType 0 1
abbrev one : RawContext 1 := empty.snoc domain.code
abbrev codomain : TypeBody 0 := .noBind domain
abbrev functionType := Statics.piType domain codomain

noncomputable def domainFormed : CoreDerivation (Statics.formed empty domain.code) :=
  includeCanonical Statics.RegularityControls.domainFormed
noncomputable def oneFormed : CoreDerivation (Statics.context one) :=
  includeCanonical Statics.RegularityControls.extendedFormed
noncomputable def codomainFormed : CoreDerivation (Statics.formed one codomain.open.code) :=
  includeCanonical Statics.RegularityControls.codomainFormed

noncomputable def newest : CoreDerivation (Statics.typed one (.var .zero) codomain.open.code) :=
  Derivation.core (.variable one .zero) (consEvidence CoreDerivation oneFormed (noEvidence CoreDerivation))

noncomputable def bindingSource : CoreDerivation (Statics.typed empty
    (lam (eliminate (.var .zero) nil)) functionType.code) :=
  Derivation.core (.lambda empty domain codomain (.bind (eliminate (.var .zero) nil)))
    (consEvidence CoreDerivation domainFormed (consEvidence CoreDerivation codomainFormed
      (consEvidence CoreDerivation (Derivation.elimination newest (Derivation.nil one _)) (noEvidence CoreDerivation))))

noncomputable def bindingCertificate := lambdaBind (eliminateEmpty (.var .zero : RawTm 1))
noncomputable def bindingTarget : CoreDerivation (Statics.typed empty (lam (.var .zero)) functionType.code) :=
  bindingCertificate.typing bindingSource

def expandedFunction : RawTy 0 :=
  (TypeParameter.mk functionType.level (eliminate functionType.term nil)).code

noncomputable def functionConversion : CoreDerivation (Statics.typeEqual empty expandedFunction functionType.code) :=
  Derivation.core (.typeEquality empty functionType.level (eliminate functionType.term nil) functionType.term)
    (consEvidence CoreDerivation
      (Derivation.emptyElimination bindingSource.typingFormation.formationView.parameterTyping) (noEvidence CoreDerivation))

noncomputable def convertedBindingSource : CoreDerivation
    (Statics.typed empty (lam (eliminate (.var .zero) nil)) expandedFunction) :=
  Derivation.core (.conversion empty _ functionType.code expandedFunction)
    (consEvidence CoreDerivation bindingSource (consEvidence CoreDerivation functionConversion.typeSymmetry
      (noEvidence CoreDerivation)))

noncomputable def convertedBindingTarget : CoreDerivation
    (Statics.typed empty (lam (.var .zero)) expandedFunction) := bindingCertificate.typing convertedBindingSource

theorem converted_function_code_changes : expandedFunction ≠ functionType.code := by
  intro same
  cases same

abbrev secondDomain : TypeParameter 1 := Statics.universeType 1 1
abbrev two : RawContext 2 := one.snoc secondDomain.code
abbrev secondCodomain : TypeBody 1 := .noBind secondDomain

noncomputable def secondDomainFormed : CoreDerivation (Statics.formed one secondDomain.code) :=
  administrativeOperations.universeFormed oneFormed 1
noncomputable def twoFormed : CoreDerivation (Statics.context two) :=
  administrativeOperations.extend oneFormed secondDomainFormed
noncomputable def secondCodomainFormed : CoreDerivation (Statics.formed two secondCodomain.open.code) :=
  administrativeOperations.universeFormed twoFormed 1
noncomputable def older : CoreDerivation (Statics.typed two (.var (.succ .zero)) secondCodomain.open.code) :=
  Derivation.core (.variable two (.succ .zero)) (consEvidence CoreDerivation twoFormed (noEvidence CoreDerivation))

noncomputable def nonbindingSource : CoreDerivation (Statics.typed one
    (lamNoAbs (eliminate (.var .zero) nil)) (Statics.piType secondDomain secondCodomain).code) :=
  Derivation.core (.lambda one secondDomain secondCodomain (.noBind (eliminate (.var .zero) nil)))
    (consEvidence CoreDerivation secondDomainFormed (consEvidence CoreDerivation secondCodomainFormed
      (consEvidence CoreDerivation (Derivation.elimination older (Derivation.nil two _)) (noEvidence CoreDerivation))))

noncomputable def nonbindingCertificate := lambdaNoAbs (eliminateEmpty (.var .zero : RawTm 1))
  (eliminateEmpty (.var (.succ .zero) : RawTm 2))
noncomputable def nonbindingTarget : CoreDerivation
    (Statics.typed one (lamNoAbs (.var .zero)) (Statics.piType secondDomain secondCodomain).code) :=
  nonbindingCertificate.typing nonbindingSource

theorem nonbinding_open_does_not_capture :
    (Statics.TermBody.noBind (.var .zero : RawTm 1)).open ≠ (.var .zero : RawTm 2) := by
  intro same
  cases same

abbrev adminDomain : TypeParameter 0 := ⟨2, eliminate (Statics.universeTerm 1) nil⟩
abbrev dependentFamily : TypeBody 0 := .bind ⟨1, .var .zero⟩

noncomputable def domainEquality :=
  PreservationControls.universeConversion (includeCanonical Statics.Derivation.empty)
noncomputable def adminDomainFormed : CoreDerivation (Statics.formed empty adminDomain.code) :=
  CoreDerivation.typeEndpoints domainEquality |>.left
noncomputable def adminContextFormed : CoreDerivation (Statics.context (empty.snoc adminDomain.code)) :=
  administrativeOperations.extend (includeCanonical Statics.Derivation.empty) adminDomainFormed

noncomputable def adminVariable : CoreDerivation (Statics.typed (empty.snoc adminDomain.code)
    (.var .zero) (Statics.universeType 1 1).code) :=
  Derivation.core (.conversion (empty.snoc adminDomain.code) (.var .zero)
    (weaken adminDomain.code) (Statics.universeType 1 1).code)
    (consEvidence CoreDerivation
      (Derivation.core (.variable (empty.snoc adminDomain.code) .zero)
        (consEvidence CoreDerivation adminContextFormed (noEvidence CoreDerivation)))
      (consEvidence CoreDerivation (administrativeOperations.weakenTypeEquality adminDomainFormed domainEquality)
        (noEvidence CoreDerivation)))

noncomputable def dependentCodomainFormed : CoreDerivation
    (Statics.formed (empty.snoc adminDomain.code) dependentFamily.open.code) :=
  Derivation.core (.formation (empty.snoc adminDomain.code) 1 (.var .zero))
    (consEvidence CoreDerivation adminVariable (noEvidence CoreDerivation))

noncomputable def dependentPiSource : CoreDerivation
    (Statics.typed empty (dependentFamily.pi adminDomain) (Statics.universeType 0 2).code) :=
  Derivation.core (.pi empty adminDomain dependentFamily)
    (consEvidence CoreDerivation adminDomainFormed
      (consEvidence CoreDerivation dependentCodomainFormed (noEvidence CoreDerivation)))

noncomputable def domainCertificate : TypeCertificate adminDomain.code domain.code :=
  elTerm (eliminateEmpty (Statics.universeTerm 1)) (set (levelClosed 2))

noncomputable def dependentPiTarget : CoreDerivation
    (Statics.typed empty (dependentFamily.pi domain) (Statics.universeType 0 2).code) :=
  (piDomain (A := adminDomain) (A' := domain) dependentFamily domainCertificate).typing dependentPiSource

theorem dependent_context_codes_change : empty.snoc adminDomain.code ≠ one := by
  intro same
  cases same

abbrev adminCodomain : TypeParameter 1 := ⟨2, eliminate (Statics.universeTerm 1) nil⟩
noncomputable def adminCodomainFormed : CoreDerivation (Statics.formed one adminCodomain.code) :=
  (PreservationControls.universeConversion oneFormed).typeEndpoints.left

noncomputable def boundPiSource : CoreDerivation
    (Statics.typed empty (pi domain.code adminCodomain.code) (Statics.universeType 0 2).code) :=
  Derivation.core (.pi empty domain (.bind adminCodomain))
    (consEvidence CoreDerivation domainFormed (consEvidence CoreDerivation adminCodomainFormed (noEvidence CoreDerivation)))

noncomputable def openedDomainCertificate : TypeCertificate adminCodomain.code (Statics.universeType 1 1).code :=
  elTerm (eliminateEmpty (Statics.universeTerm 1)) (set (levelClosed 2))

noncomputable def boundPiTarget :=
  (piCodomain domain openedDomainCertificate).typing boundPiSource

noncomputable def nonbindingPiSource : CoreDerivation
    (Statics.typed empty (piNoAbs domain.code adminDomain.code) (Statics.universeType 0 2).code) :=
  Derivation.core (.pi empty domain (.noBind adminDomain))
    (consEvidence CoreDerivation domainFormed (consEvidence CoreDerivation adminCodomainFormed (noEvidence CoreDerivation)))

noncomputable def nonbindingPiTarget :=
  (piNoAbsCodomain domain domainCertificate openedDomainCertificate).typing nonbindingPiSource

noncomputable def recoveredTypeOccurrence := typeCodeStep domainCertificate.step

theorem changed_finite_level_has_no_step {n : Nat} (A B : TypeParameter n)
    (different : A.level ≠ B.level) (step : Step A.code B.code) : False := by
  have parameters := TypeParameter.code_injective (typeCodeStep step).boundary
  exact different (congrArg TypeParameter.level parameters).symm

def rawNeutralReduction : Step
    (levelNeutral (eliminate (Statics.universeTerm (n := 0) 0) nil))
    (levelNeutral (Statics.universeTerm (n := 0) 0)) := by
  apply CompatibleDerivations.Step.congr (R := Root) Op.levelNeutral
  apply CompatibleDerivations.ArgsStep.head
  exact .root (.eliminateEmpty _)

theorem neutral_annotation_unformed {n : Nat} {Γ : RawContext n} (levelTerm code : RawTm n)
    (tree : CoreDerivation (Statics.formed Γ (el (set (levelNeutral levelTerm)) code))) : False := by
  have boundary := tree.formationView.boundary
  cases boundary

theorem level_term_untyped {n : Nat} {Γ : RawContext n} {A : RawTy n} (level : Level (scope n))
    (tree : CoreDerivation (Statics.typed Γ (levelTerm level) A)) : False :=
  tree.constructorView.level level rfl

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.BinderPreservationControls
