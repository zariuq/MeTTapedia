import Mettapedia.Languages.Agda.Adequacy.AdministrativePreservation
import Mettapedia.Languages.Agda.Adequacy.AdministrativeCanonizationControls

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Structural
open Structural.Statics (RawTm RawTy RawContext TypeParameter TypeBody)
open Structural.AdministrativeStatics
open BinderPreservationControls

abbrev originalPi := Statics.piType adminDomain codomain

noncomputable def originalCodomain : CoreDerivation
    (Statics.formed (empty.snoc adminDomain.code) codomain.open.code) :=
  administrativeOperations.universeFormed adminContextFormed 1

noncomputable def originalLambda : CoreDerivation
    (Statics.typed empty (lam (.var .zero)) originalPi.code) :=
  Derivation.core (.lambda empty adminDomain codomain (.bind (.var .zero)))
    (consEvidence CoreDerivation adminDomainFormed
      (consEvidence CoreDerivation originalCodomain
        (consEvidence CoreDerivation adminVariable (noEvidence CoreDerivation))))

noncomputable def changedPi : CoreDerivation
    (Statics.typeEqual empty originalPi.code functionType.code) :=
  Derivation.core (.typeEquality empty originalPi.level originalPi.term functionType.term)
    (consEvidence CoreDerivation
      (Derivation.core (.piCongruence empty adminDomain domain codomain codomain)
        (consEvidence CoreDerivation adminDomainFormed
          (consEvidence CoreDerivation domainEquality
            (consEvidence CoreDerivation originalCodomain.typeReflexivity (noEvidence CoreDerivation)))))
      (noEvidence CoreDerivation))

noncomputable def twiceConvertedLambda : CoreDerivation
    (Statics.typed empty (lam (.var .zero)) expandedFunction) :=
  Derivation.core (.conversion empty _ functionType.code expandedFunction)
    (consEvidence CoreDerivation
      (Derivation.core (.conversion empty _ originalPi.code functionType.code)
        (consEvidence CoreDerivation originalLambda (consEvidence CoreDerivation changedPi (noEvidence CoreDerivation))))
      (consEvidence CoreDerivation functionConversion.typeSymmetry (noEvidence CoreDerivation)))

abbrev administrativeArgument : RawTm 0 := eliminate (Statics.universeTerm 0) nil

noncomputable def convertedAction : Action empty expandedFunction (cons (apply administrativeArgument) nil)
    PreservationControls.expandedUniverse :=
  Derivation.inputConversion functionConversion
    (Derivation.outputConversion
      (Derivation.cons (A := domain) (B := codomain) PreservationControls.administrativeArgument
        (Derivation.nil empty domain.code))
      (PreservationControls.universeConversion (includeCanonical Statics.Derivation.empty)).typeSymmetry)

noncomputable def convertedSource : CoreDerivation
    (Statics.typed empty (eliminate (lam (.var .zero)) (cons (apply administrativeArgument) nil))
      PreservationControls.expandedUniverse) :=
  Derivation.elimination twiceConvertedLambda convertedAction

noncomputable def convertedBeta : CoreDerivation
    (Statics.termEqual empty (eliminate (lam (.var .zero)) (cons (apply administrativeArgument) nil))
      (eliminate administrativeArgument nil) PreservationControls.expandedUniverse) := betaBinding convertedSource

theorem original_pi_components_differ : originalPi.code ≠ functionType.code := by
  intro same
  cases same

theorem original_output_keeps_conversion : PreservationControls.expandedUniverse (n := 0) ≠ domain.code :=
  PreservationControls.converted_annotation_changes_raw_code

abbrev dependentContext := Canonization.Controls.dependentContext
abbrev localDomain := Canonization.Controls.localDomain
abbrev localFamily := Canonization.Controls.localFamily
abbrev localArgument := Canonization.Controls.localArgument
abbrev functionParameter := Statics.piType localDomain localFamily
abbrev outerCodomain : TypeBody 1 := .noBind functionParameter
abbrev dependentRest : Spine (scope 1) := cons (apply localArgument) nil
abbrev outerArgument : RawTm 1 := Statics.universeTerm 0
abbrev output := (localFamily.instantiate localArgument).code

noncomputable def localDomainFormed : CoreDerivation (Statics.formed dependentContext localDomain.code) :=
  administrativeOperations.universeFormed Canonization.Controls.dependentContextFormed 1

noncomputable def projectionSub := Statics.TypedSubstitution.projection coreAlgebra
  Canonization.Controls.dependentContextFormed localDomainFormed

noncomputable def olderFunction : CoreDerivation
    (Statics.typed (dependentContext.snoc localDomain.code) (.var (.succ .zero)) outerCodomain.open.code) :=
  Canonization.Controls.dependentHead.substitution (dependentContext.snoc localDomain.code)
    (Telescope.projection (S := sig) .term 1) projectionSub

noncomputable def outerCodomainFormed : CoreDerivation
    (Statics.formed (dependentContext.snoc localDomain.code) outerCodomain.open.code) :=
  olderFunction.typingFormation

noncomputable def noAbsFunction : CoreDerivation
    (Statics.typed dependentContext (lamNoAbs (.var .zero)) (Statics.piType localDomain outerCodomain).code) :=
  Derivation.core (.lambda dependentContext localDomain outerCodomain (.noBind (.var .zero)))
    (consEvidence CoreDerivation localDomainFormed (consEvidence CoreDerivation outerCodomainFormed
      (consEvidence CoreDerivation olderFunction (noEvidence CoreDerivation))))

noncomputable def bindingFunction : CoreDerivation
    (Statics.typed dependentContext (lam (.var (.succ .zero))) (Statics.piType localDomain outerCodomain).code) :=
  Derivation.core (.lambda dependentContext localDomain outerCodomain (.bind (.var (.succ .zero))))
    (consEvidence CoreDerivation localDomainFormed (consEvidence CoreDerivation outerCodomainFormed
      (consEvidence CoreDerivation olderFunction (noEvidence CoreDerivation))))

noncomputable def outerArgumentTyped : CoreDerivation (Statics.typed dependentContext outerArgument localDomain.code) :=
  Derivation.core (.sort dependentContext 0)
    (consEvidence CoreDerivation Canonization.Controls.dependentContextFormed (noEvidence CoreDerivation))

noncomputable def nonemptyAction : Action dependentContext (Statics.piType localDomain outerCodomain).code
    (cons (apply outerArgument) dependentRest) output :=
  Derivation.cons (A := localDomain) (B := outerCodomain) outerArgumentTyped Canonization.Controls.dependentAction

noncomputable def nonbindingSource : CoreDerivation (Statics.typed dependentContext
    (eliminate (lamNoAbs (.var .zero)) (cons (apply outerArgument) dependentRest)) output) :=
  Derivation.elimination noAbsFunction nonemptyAction

noncomputable def bindingSource : CoreDerivation (Statics.typed dependentContext
    (eliminate (lam (.var (.succ .zero))) (cons (apply outerArgument) dependentRest)) output) :=
  Derivation.elimination bindingFunction nonemptyAction

noncomputable def nonbindingDependentTail : CoreDerivation (Statics.termEqual dependentContext
    (eliminate (lamNoAbs (.var .zero)) (cons (apply outerArgument) dependentRest))
    (eliminate (.var .zero) dependentRest) output) := betaNonbinding nonbindingSource

noncomputable def bindingDependentTail : CoreDerivation (Statics.termEqual dependentContext
    (eliminate (lam (.var (.succ .zero))) (cons (apply outerArgument) dependentRest))
    (eliminate (.var .zero) dependentRest) output) := betaBinding bindingSource

theorem beta_keeps_dependent_original_result : output ≠ (localFamily.instantiate outerArgument).code :=
  Canonization.Controls.dependent_output_keeps_original_raw_argument

theorem beta_does_not_capture_free_function :
    eliminate (.var .zero) dependentRest ≠ eliminate outerArgument dependentRest := by
  intro same
  cases same

abbrev outerDomain := Statics.piType domain RegularityControls.family
abbrev outerFamily : TypeBody 0 := .bind ⟨1, localArgument⟩
abbrev insideBinder : RawTm 1 := eliminate (lamNoAbs (.var .zero)) (cons (apply outerArgument) dependentRest)

noncomputable def binderSource : CoreDerivation
    (Statics.typed empty (lam insideBinder) (Statics.piType outerDomain outerFamily).code) :=
  Derivation.core (.lambda empty outerDomain outerFamily (.bind insideBinder))
    (consEvidence CoreDerivation RegularityControls.inputFormed
      (consEvidence CoreDerivation nonbindingSource.typingFormation
        (consEvidence CoreDerivation nonbindingSource (noEvidence CoreDerivation))))

def betaBelowBinder : Step (lam insideBinder) (lam (eliminate (.var .zero) dependentRest)) :=
  CompatibleDerivations.Step.congr (R := Root) Op.lam
    (.head .nil (.root (Root.betaNoAbs (.var .zero) outerArgument dependentRest)))

noncomputable def binderEquality : CoreDerivation (Statics.termEqual empty
    (lam insideBinder) (lam (eliminate (.var .zero) dependentRest)) (Statics.piType outerDomain outerFamily).code) :=
  termEquality betaBelowBinder binderSource

noncomputable def binderTarget : CoreDerivation
    (Statics.typed empty (lam (eliminate (.var .zero) dependentRest)) (Statics.piType outerDomain outerFamily).code) :=
  termPreservation betaBelowBinder binderSource

theorem raw_reduction_does_not_supply_formation :
    ¬ Nonempty (CoreDerivation (Statics.formed empty Structural.AdministrativeStatics.Controls.unsupportedType)) :=
  Structural.AdministrativeStatics.Controls.unsupported_type_unformed

end Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation.Controls
