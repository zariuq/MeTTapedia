import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayComputedFamilyControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayMixedIdentityFamilySubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedIdentityPaths
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayReflexivityAdmission

/-!
# A checked non-diagonal family after two computed substitutions

The left endpoint computes by beta; the right endpoint is the bound variable.
The family is not neutral, but its endpoint contraction is retained and
qualified. The two outer arguments have different raw syntax, while their
values agree by the independently proved checked-contraction square.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayMixedIdentityFamilyControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayQualifiedTypingControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedFamilyControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayUniverseModel

private abbrev familyLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))

def computedLeft : Tower.Tm 1 := .app (.lam (.var 0)) (.var 0)
def computedLeftCode : Code Tower.Head NoConversion 1 :=
  .appElim functionType functionType consumerCode .var
def mixedFamily : Tower.Tm 1 := .id functionType computedLeft (.var 0)
def mixedFamilyCode : Code Tower.Head NoConversion 1 :=
  .idForm familyLevel functionFormation computedLeftCode .var

theorem family_checks :
    check Tower.rules noConversionCheck (.snoc .nil functionType)
      mixedFamily (.head familyLevel) mixedFamilyCode = true := by
  decide +kernel

theorem beta_endpoint_qualified :
    computedLeftCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      (.snoc .nil familyLevel functionFormation) computedLeft functionType = true := by
  decide +kernel

theorem beta_endpoint_contracts :
    computedLeftCode.contractBeta (.var 0) (.var 0) functionType = some (.var) := by
  rfl

theorem family_is_not_neutral :
    mixedFamilyCode.neutralEliminations mixedFamily (.head familyLevel) = false := by
  decide +kernel

theorem instantiated_types_differ :
    inst0 computedFunction mixedFamily ≠ inst0 identity mixedFamily := by
  decide +kernel

/-- Extensional truth does not silently become an intensional proof. The
raw endpoints differ, so reflexivity alone is rejected by the checker. -/
theorem naive_reflexivity_rejected :
    check Tower.rules noConversionCheck (.snoc .nil functionType)
      (.refl computedLeft) mixedFamily
      (.reflIntro functionType computedLeftCode) = false := by
  decide +kernel

private def sourceContextCode : ContextCode Tower.Head NoConversion 1 :=
  .snoc .nil familyLevel functionFormation

private def diagonalFamily : Tower.Tm 1 := .id functionType (.var 0) (.var 0)
private def diagonalFamilyCode : Code Tower.Head NoConversion 1 :=
  .idForm familyLevel functionFormation .var .var

private theorem diagonal_family_checks :
    check Tower.rules noConversionCheck (.snoc .nil functionType)
      diagonalFamily (.head familyLevel) diagonalFamilyCode = true := by
  decide +kernel

private theorem endpoint_path : QualifiedBetaPath Tower.rules TowerDecisions.headTarget
    sourceContextCode functionType computedLeft computedLeftCode (.var 0) .var := by
  exact .contraction beta_endpoint_qualified beta_endpoint_contracts
    (.terminal (.var 0) .var (by decide +kernel))

private theorem variable_path : QualifiedBetaPath Tower.rules TowerDecisions.headTarget
    sourceContextCode functionType (.var 0) .var (.var 0) .var :=
  .terminal (.var 0) .var (by decide +kernel)

universe u

/-- The source family has a real proof inhabitant on every environment
admitted by its bound-variable context. Beta-path comparison identifies its
fibre with the checked diagonal identity fibre. -/
theorem source_mixed_family_inhabited
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ (source : Meaning.{u} 1) (valid : Environment.{u} 1 → Prop),
      assemble (interpretHead h seed ground valuation) constants mixedFamilyCode
        mixedFamily (.head familyLevel) = some source ∧
      assembleContext (interpretHead h seed ground valuation) constants
        sourceContextCode (.snoc .nil functionType) = some valid ∧
      ∀ env, valid env → (∅ : ZFSet.{u}) ∈ source.value env := by
  let heads := interpretHead h seed ground valuation
  have domainChecked : check Tower.rules noConversionCheck .nil
      functionType (.head familyLevel) functionFormation = true := by decide +kernel
  obtain ⟨domain, atDomain, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck functionFormation domainChecked
  let valid : Environment.{u} 1 → Prop :=
    fun env => env 0 ∈ domain.value (env ∘ wk)
  have atContext : assembleContext heads constants sourceContextCode
      (.snoc .nil functionType) = some valid := by
    simp [sourceContextCode, assembleContext, atDomain, valid]
  obtain ⟨source, atSource, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck mixedFamilyCode family_checks
  obtain ⟨diagonal, atDiagonal, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck diagonalFamilyCode diagonal_family_checks
  let proofCode : Code Tower.Head NoConversion 1 := .reflIntro functionType .var
  have atProof : assemble heads constants proofCode
      (.refl (.var 0)) diagonalFamily =
      some (Meaning.plain (fun _ => (∅ : ZFSet.{u}))) := by rfl
  have diagonalMember := reflexivity_in_same_endpoint_formation heads constants
    functionType (.var 0) familyLevel (.var) functionFormation (.var)
    (Meaning.plain (fun _ => (∅ : ZFSet.{u}))) diagonal atProof atDiagonal
  refine ⟨source, valid, atSource, atContext, ?_⟩
  intro env admitted
  have equal := identity_qualified_paths_endpoints_coherent heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h seed ground valuation groundTyped)
    (empty_constants_model _ constants) sourceContextCode
    mixedFamilyCode diagonalFamilyCode familyLevel familyLevel
    functionFormation computedLeftCode .var functionFormation .var .var
    .hole .hole .var .var .var .var
    endpoint_path variable_path variable_path variable_path
    (valid := valid) (by decide +kernel) atContext family_checks
    diagonal_family_checks rfl rfl source diagonal atSource atDiagonal env admitted
  exact equal.symm ▸ diagonalMember env

/-- The beta left endpoint and neutral right endpoint yield equal checked
family instances after two different computed substitutions. -/
theorem computed_mixed_family_values
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      mixedFamily (.head familyLevel) computedFunction mixedFamilyCode computedFunctionCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      mixedFamily (.head familyLevel) identity mixedFamilyCode identityCode
    check Tower.rules noConversionCheck .nil (inst0 computedFunction mixedFamily)
        (.head familyLevel) leftFormation = true ∧
      check Tower.rules noConversionCheck .nil (inst0 identity mixedFamily)
        (.head familyLevel) rightFormation = true ∧
      ∃ left right,
        assemble (interpretHead h seed ground valuation) constants leftFormation
          (inst0 computedFunction mixedFamily) (.head familyLevel) = some left ∧
        assemble (interpretHead h seed ground valuation) constants rightFormation
          (inst0 identity mixedFamily) (.head familyLevel) = some right ∧
        ∀ env : Environment.{u} 0, left.value env = right.value env := by
  obtain ⟨computed, _, normal, atComputed, _, atNormal, argumentEqual⟩ :=
    computed_functions_return_identity h seed ground valuation groundTyped constants
  have domainChecked : check Tower.rules noConversionCheck .nil
      functionType (.head familyLevel) functionFormation = true := by decide +kernel
  obtain ⟨domain, atDomain, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    functionFormation domainChecked
  simpa only [true_imp_iff, mixedFamily, mixedFamilyCode, computedLeft,
    computedLeftCode] using (computed_arguments_mixed_identity_family_values
    (interpretHead h seed ground valuation) constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h seed ground valuation groundTyped)
    (empty_constants_model _ constants)
    .nil (fun _ => True) rfl rfl familyLevel functionFormation domain
    (by decide +kernel) (by decide +kernel) atDomain
    computedFunctionCode identityCode computed normal
    functions_checked.2.1 functions_checked.1 functions_qualified.2.1
    atComputed atNormal (fun env _ => (argumentEqual env).1)
    functionType (.var 0) (.var 0) (.var 0) familyLevel familyLevel
    functionFormation functionFormation computedLeftCode .var
    computedLeftCode .var .var family_checks family_checks
    beta_endpoint_qualified beta_endpoint_qualified
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- The comparison is not equality of empty fibres. The computed argument
instantiates a family whose beta endpoint equals its neutral endpoint on the
admitted domain, so the empty-set proof token belongs to the result. -/
theorem computed_mixed_family_inhabited
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let formation := Code.instantiate noConversionRename noConversionSubstitute
      mixedFamily (.head familyLevel) computedFunction mixedFamilyCode computedFunctionCode
    check Tower.rules noConversionCheck .nil (inst0 computedFunction mixedFamily)
      (.head familyLevel) formation = true ∧
    ∃ result,
      assemble (interpretHead h seed ground valuation) constants formation
        (inst0 computedFunction mixedFamily) (.head familyLevel) = some result ∧
      ∀ env : Environment.{u} 0, (∅ : ZFSet.{u}) ∈ result.value env := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨source, valid, atSource, atContext, sourceMember⟩ :=
    source_mixed_family_inhabited h seed ground valuation groundTyped constants
  obtain ⟨computed, _, _, atComputed, _, _, _⟩ :=
    computed_functions_return_identity h seed ground valuation groundTyped constants
  have domainChecked : check Tower.rules noConversionCheck .nil
      functionType (.head familyLevel) functionFormation = true := by decide +kernel
  obtain ⟨domain, atDomain, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck functionFormation domainChecked
  have computedMember : ∀ env : Environment.{u} 0,
      computed.value env ∈ domain.value env := by
    intro env
    exact qualified_membership heads constants Tower.rules
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
      successor_qualified (universeModel h seed ground valuation groundTyped)
      (empty_constants_model _ constants) computedFunctionCode .nil rfl
      functions_checked.2.1 functions_qualified.2.1 (fun _ => True) computed
      rfl atComputed familyLevel functionFormation domain domainChecked atDomain
      env True.intro
  have checked := Code.instantiate_checked noConversionRename noConversionSubstitute
    Tower.rules noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) family_checks functions_checked.2.1
  obtain ⟨result, atResult, values⟩ := assemble_instantiate
    noConversionRename noConversionSubstitute heads constants Tower.rules noConversionCheck
    mixedFamilyCode computedFunctionCode source computed family_checks atSource atComputed
  refine ⟨checked, result, atResult, ?_⟩
  intro env
  have extendedAdmitted : valid (extend env (computed.value env)) :=
    (context_extension_valid_iff heads constants .nil functionType .nil
      familyLevel functionFormation (fun _ => True) valid domain rfl atDomain
      atContext env (computed.value env)).mpr ⟨True.intro, computedMember env⟩
  rw [values]
  exact sourceMember _ extendedAdmitted

#print axioms computed_mixed_family_values
#print axioms source_mixed_family_inhabited
#print axioms computed_mixed_family_inhabited

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayMixedIdentityFamilyControls
