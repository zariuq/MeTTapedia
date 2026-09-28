import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayResultQualification
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayUniverseModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedComputation

/-!
# Computed higher-order values with qualified result formations

These are closed programs for the existing cumulative checker. The examples
include function-valued arguments and results, nested applications, pairs,
both projections, reflexivity and a type value. Checking and formation
qualification are tested separately. An accepted reflexivity certificate
with a computed endpoint remains outside this qualification.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedTypingControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay
open ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayUniverseModel

private abbrev u0 : Tower.Head := .sort Tower.zero
private abbrev u1 : Tower.Head := .sort (.succ Tower.zero)
private abbrev u2 : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev u3 : Tower.Head := .sort (.succ (.succ (.succ Tower.zero)))
private abbrev functionLevel : Tower.Head := .sort (.max (.succ Tower.zero) (.succ Tower.zero))
private abbrev compoundLevel : Tower.Head := .sort
  (.max (.max (.succ Tower.zero) (.succ Tower.zero))
    (.max (.succ Tower.zero) (.succ Tower.zero)))

def functionType {n : Nat} : Tower.Tm n := .pi (.head u0) (.head u0)
def functionFormation {n : Nat} : Code Tower.Head NoConversion n :=
  .piForm u1 u1 .headType .headType
def identity {n : Nat} : Tower.Tm n := .lam (.var 0)
def identityCode {n : Nat} : Code Tower.Head NoConversion n :=
  .lamIntro functionLevel functionFormation .var

def consumerCode {n : Nat} : Code Tower.Head NoConversion n :=
  .lamIntro compoundLevel
    (.piForm functionLevel functionLevel functionFormation functionFormation) .var

def computedFunction : Tower.Tm 0 := .app identity identity
def computedFunctionCode : Code Tower.Head NoConversion 0 :=
  .appElim functionType functionType consumerCode identityCode

def nestedFunction : Tower.Tm 0 := .app identity computedFunction
def nestedFunctionCode : Code Tower.Head NoConversion 0 :=
  .appElim functionType functionType consumerCode computedFunctionCode

def pairType {n : Nat} : Tower.Tm n := .sigma functionType functionType
def pairFormation {n : Nat} : Code Tower.Head NoConversion n :=
  .sigmaForm functionLevel functionLevel functionFormation functionFormation
def computedPair : Tower.Tm 0 := .pair computedFunction nestedFunction
def computedPairCode : Code Tower.Head NoConversion 0 :=
  .pairIntro compoundLevel pairFormation computedFunctionCode nestedFunctionCode
def firstCode : Code Tower.Head NoConversion 0 := .fstElim functionType computedPairCode
def secondCode : Code Tower.Head NoConversion 0 :=
  .sndElim functionType functionType computedPairCode

def identityType : Tower.Tm 0 := .id functionType identity identity
def identityFormation : Code Tower.Head NoConversion 0 :=
  .idForm functionLevel functionFormation identityCode identityCode
def reflexivityCode : Code Tower.Head NoConversion 0 := .reflIntro functionType identityCode

private abbrev typeComputationLevel : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
def computedType : Tower.Tm 0 := .app identity (.head u0)
def computedTypeCode : Code Tower.Head NoConversion 0 :=
  .appElim (.head u1) (.head u1)
    (.lamIntro typeComputationLevel (.piForm u2 u2 .headType .headType) .var) .headType

private abbrev lowerConsumerLevel : Tower.Head := .sort
  (.max (.succ (.succ Tower.zero)) (.max (.succ Tower.zero) (.succ Tower.zero)))
private abbrev upperConsumerLevel : Tower.Head := .sort
  (.max (.succ (.succ (.succ Tower.zero))) (.max (.succ Tower.zero) (.succ Tower.zero)))

/-- The retained domain of the unused outer parameter differs between the
two certificates; its supplied argument is itself a type-valued computation. -/
def independentFunction : Tower.Tm 0 := .app (.lam identity) computedType
def lowerIndependentCode : Code Tower.Head NoConversion 0 :=
  .appElim (.head u1) functionType
    (.lamIntro lowerConsumerLevel (.piForm u2 functionLevel .headType functionFormation) identityCode)
    computedTypeCode
def upperIndependentCode : Code Tower.Head NoConversion 0 :=
  .appElim (.head u2) functionType
    (.lamIntro upperConsumerLevel (.piForm u3 functionLevel .headType functionFormation) identityCode)
    (.cumul u1 computedTypeCode)
def mixedIdentityType : Tower.Tm 0 := .id functionType independentFunction independentFunction
def mixedIdentityFormation : Code Tower.Head NoConversion 0 :=
  .idForm functionLevel functionFormation lowerIndependentCode upperIndependentCode
def mixedReflexivityCode : Code Tower.Head NoConversion 0 :=
  .reflIntro functionType lowerIndependentCode

theorem independent_functions_checked_and_qualified :
    check Tower.rules noConversionCheck .nil independentFunction functionType lowerIndependentCode = true ∧
      check Tower.rules noConversionCheck .nil independentFunction functionType upperIndependentCode = true ∧
      lowerIndependentCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
        independentFunction functionType = true ∧
      upperIndependentCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
        independentFunction functionType = true := by
  decide +kernel

theorem independent_codes_differ : lowerIndependentCode ≠ upperIndependentCode := by
  intro same
  cases same

theorem mixed_identity_checked :
    check Tower.rules noConversionCheck .nil mixedIdentityType (.head functionLevel)
      mixedIdentityFormation = true ∧
      check Tower.rules noConversionCheck .nil (.refl independentFunction) mixedIdentityType
        mixedReflexivityCode = true := by
  decide +kernel

theorem mixed_reflexivity_not_qualified :
    mixedReflexivityCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
      (.refl independentFunction) mixedIdentityType = false := by
  decide +kernel

theorem substituted_endpoint_rejected :
    check Tower.rules noConversionCheck .nil (.id functionType independentFunction identity)
      (.head functionLevel) mixedIdentityFormation = false := by
  decide +kernel

theorem computed_type_checked_and_qualified :
    check Tower.rules noConversionCheck .nil computedType (.head u1) computedTypeCode = true ∧
      computedTypeCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
        computedType (.head u1) = true := by
  decide +kernel

/-- The fibre is genuinely dependent on the first coordinate: it is the
function space of the selected type, not a fixed second-component type. -/
def dependentPairType : Tower.Tm 0 :=
  .sigma (.head u1) (.pi (.var 0) (.var 1))
private abbrev dependentPairLevel : Tower.Head := .sort
  (.max (.succ (.succ Tower.zero)) (.max (.succ Tower.zero) (.succ Tower.zero)))
def dependentPairFormation : Code Tower.Head NoConversion 0 :=
  .sigmaForm u2 functionLevel .headType (.piForm u1 u1 .var .var)
def dependentPair : Tower.Tm 0 := .pair (.head u0) computedFunction
def dependentPairCode : Code Tower.Head NoConversion 0 :=
  .pairIntro dependentPairLevel dependentPairFormation .headType computedFunctionCode

theorem dependent_pair_checked_and_qualified :
    check Tower.rules noConversionCheck .nil dependentPair dependentPairType dependentPairCode = true ∧
      dependentPairCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
        dependentPair dependentPairType = true := by
  decide +kernel

theorem functions_checked :
    check Tower.rules noConversionCheck .nil identity functionType identityCode = true ∧
      check Tower.rules noConversionCheck .nil computedFunction functionType computedFunctionCode = true ∧
        check Tower.rules noConversionCheck .nil nestedFunction functionType nestedFunctionCode = true := by
  decide +kernel

theorem functions_qualified :
    identityCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
      identity functionType = true ∧
      computedFunctionCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
        computedFunction functionType = true ∧
        nestedFunctionCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
          nestedFunction functionType = true := by
  decide +kernel

theorem pair_and_projections_checked :
    check Tower.rules noConversionCheck .nil computedPair pairType computedPairCode = true ∧
      check Tower.rules noConversionCheck .nil (.fst computedPair) functionType firstCode = true ∧
        check Tower.rules noConversionCheck .nil (.snd computedPair) functionType secondCode = true := by
  decide +kernel

theorem pair_and_projections_qualified :
    computedPairCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
      computedPair pairType = true ∧
      firstCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
        (.fst computedPair) functionType = true ∧
        secondCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
          (.snd computedPair) functionType = true := by
  decide +kernel

theorem reflexivity_and_type_checked :
    check Tower.rules noConversionCheck .nil (.refl identity) identityType reflexivityCode = true ∧
      check Tower.rules noConversionCheck .nil functionType (.head functionLevel) functionFormation = true := by
  decide +kernel

theorem reflexivity_and_type_qualified :
    reflexivityCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
      (.refl identity) identityType = true ∧
      functionFormation.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil
        functionType (.head functionLevel) = true := by
  decide +kernel

theorem computed_sources_are_not_neutral :
    computedFunctionCode.neutralEliminations computedFunction functionType = false ∧
      firstCode.neutralEliminations (.fst computedPair) functionType = false := by
  decide +kernel

/-- The boundary is incomplete, not unsound: the ordinary checker accepts
this program although the additional semantic-typing qualification fails. -/
theorem computed_identity_boundary :
    check Tower.rules noConversionCheck .nil (.refl computedFunction)
      (.id functionType computedFunction computedFunction)
      (.reflIntro functionType computedFunctionCode) = true ∧
      (Code.reflIntro functionType computedFunctionCode).resultFormationsNeutral
        Tower.rules TowerDecisions.headTarget .nil (.refl computedFunction)
        (.id functionType computedFunction computedFunction) = false := by
  decide +kernel

/-- Smallness of an identity type and inhabitance of that identity type are
different obligations. Computed endpoints do not prevent universe membership
of the identity code. -/
theorem computed_identity_formation_qualified :
    check Tower.rules noConversionCheck .nil (.id functionType computedFunction computedFunction)
      (.head functionLevel)
      (.idForm functionLevel functionFormation computedFunctionCode computedFunctionCode) = true ∧
      (Code.idForm functionLevel functionFormation computedFunctionCode computedFunctionCode).resultFormationsNeutral
        Tower.rules TowerDecisions.headTarget .nil
          (.id functionType computedFunction computedFunction) (.head functionLevel) = true := by
  decide +kernel

/-- Qualification alone does not authorize a typing judgment: head typing
still rejects a universe inhabiting itself. -/
theorem qualification_is_not_acceptance :
    (Code.headType : Code Tower.Head NoConversion 0).resultFormationsNeutral
      Tower.rules TowerDecisions.headTarget .nil (.head u0) (.head u0) = true ∧
      check Tower.rules noConversionCheck .nil (.head u0) (.head u0) .headType = false := by
  decide +kernel

universe u

theorem internal_domains_differ (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (valuation : Nat → Nat) :
    interpretHead h seed ground valuation u1 ≠ interpretHead h seed ground valuation u2 := by
  change universeSet h seed 1 ≠ universeSet h seed 2
  intro same
  have member := universeSet_mem_next h seed 1
  rw [same] at member
  exact ZFSet.mem_irrefl _ member

/-- Membership uses the constructed universe model and an independently
supplied checked formation. It does not ask the caller for semantic typing
of this program or any of its computed arguments. -/
theorem closed_membership
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u})
    (subject type : Tower.Tm 0) (code : Code Tower.Head NoConversion 0)
    (checked : check Tower.rules noConversionCheck .nil subject type code = true)
    (qualified : code.resultFormationsNeutral Tower.rules TowerDecisions.headTarget .nil subject type = true)
    (level : Tower.Head) (formation : Code Tower.Head NoConversion 0)
    (formed : check Tower.rules noConversionCheck .nil type (.head level) formation = true) :
    ∃ meaning typeMeaning,
      assemble (interpretHead h seed ground valuation) constants code subject type = some meaning ∧
      assemble (interpretHead h seed ground valuation) constants formation type (.head level) = some typeMeaning ∧
      ∀ env : Environment.{u} 0, meaning.value env ∈ typeMeaning.value env := by
  obtain ⟨meaning, atSource, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck code checked
  obtain ⟨typeMeaning, atFormation, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck formation formed
  refine ⟨meaning, typeMeaning, atSource, atFormation, ?_⟩
  intro env
  exact qualified_membership (interpretHead h seed ground valuation) constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity successor_qualified
    (ZFSetReplayUniverseModel.universeModel h seed ground valuation groundTyped)
    (empty_constants_model _ constants) code .nil rfl checked qualified
    (fun _ => True) meaning rfl atSource level formation typeMeaning formed atFormation env True.intro

/-- The consumer supplies a raised formation certificate, rather than the
particular unraised certificate extracted from the program. -/
def raisedFunctionFormation : Code Tower.Head NoConversion 0 :=
  .cumul functionLevel functionFormation

theorem raised_function_formation_checked :
    check Tower.rules noConversionCheck .nil functionType (.head u2) raisedFunctionFormation = true := by
  decide +kernel

theorem computed_function_membership
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ meaning typeMeaning,
      assemble (interpretHead h seed ground valuation) constants computedFunctionCode
        computedFunction functionType = some meaning ∧
      assemble (interpretHead h seed ground valuation) constants raisedFunctionFormation
        functionType (.head u2) = some typeMeaning ∧
      ∀ env : Environment.{u} 0, meaning.value env ∈ typeMeaning.value env :=
  closed_membership h seed ground valuation groundTyped constants computedFunction functionType
    computedFunctionCode functions_checked.2.1 functions_qualified.2.1
    u2 raisedFunctionFormation raised_function_formation_checked

theorem dependent_pair_membership
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ meaning typeMeaning,
      assemble (interpretHead h seed ground valuation) constants dependentPairCode
        dependentPair dependentPairType = some meaning ∧
      assemble (interpretHead h seed ground valuation) constants dependentPairFormation
        dependentPairType (.head dependentPairLevel) = some typeMeaning ∧
      ∀ env : Environment.{u} 0, meaning.value env ∈ typeMeaning.value env :=
  closed_membership h seed ground valuation groundTyped constants dependentPair dependentPairType
    dependentPairCode dependent_pair_checked_and_qualified.1 dependent_pair_checked_and_qualified.2
    dependentPairLevel dependentPairFormation (by decide +kernel)

theorem projected_computed_function_membership
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ meaning typeMeaning,
      assemble (interpretHead h seed ground valuation) constants secondCode
        (.snd computedPair) functionType = some meaning ∧
      assemble (interpretHead h seed ground valuation) constants raisedFunctionFormation
        functionType (.head u2) = some typeMeaning ∧
      ∀ env : Environment.{u} 0, meaning.value env ∈ typeMeaning.value env :=
  closed_membership h seed ground valuation groundTyped constants (.snd computedPair) functionType
    secondCode pair_and_projections_checked.2.2 pair_and_projections_qualified.2.2
    u2 raisedFunctionFormation raised_function_formation_checked

theorem function_contraction_receipts :
    computedFunctionCode.contractBeta (.var 0) identity functionType = some identityCode ∧
      nestedFunctionCode.contractBeta (.var 0) computedFunction functionType = some computedFunctionCode :=
  ⟨rfl, rfl⟩

/-- The outer computation receives a beta-redex, function-valued argument.
Both actual contraction receipts check, and the assembled nested program
returns the same set value as the assembled identity function. -/
theorem computed_functions_return_identity
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ computed nested result,
      assemble (interpretHead h seed ground valuation) constants computedFunctionCode
        computedFunction functionType = some computed ∧
      assemble (interpretHead h seed ground valuation) constants nestedFunctionCode
        nestedFunction functionType = some nested ∧
      assemble (interpretHead h seed ground valuation) constants identityCode
        identity functionType = some result ∧
      ∀ env : Environment.{u} 0,
        computed.value env = result.value env ∧ nested.value env = result.value env := by
  obtain ⟨computed, atComputed, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
      computedFunctionCode functions_checked.2.1
  obtain ⟨nested, atNested, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
      nestedFunctionCode functions_checked.2.2
  obtain ⟨resultCode, result, contraction, _, atResult, returned⟩ :=
    qualified_contractBeta (interpretHead h seed ground valuation) constants Tower.rules
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity successor_qualified
      (ZFSetReplayUniverseModel.universeModel h seed ground valuation groundTyped)
      (empty_constants_model _ constants) .nil computedFunctionCode computed
      (valid := fun _ => True) rfl functions_checked.2.1 functions_qualified.2.1 rfl atComputed
  rw [function_contraction_receipts.1] at contraction
  cases Option.some.inj contraction
  obtain ⟨nestedCode, nestedResult, nestedContraction, _, atNestedResult, nestedReturned⟩ :=
    qualified_contractBeta (interpretHead h seed ground valuation) constants Tower.rules
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity successor_qualified
      (ZFSetReplayUniverseModel.universeModel h seed ground valuation groundTyped)
      (empty_constants_model _ constants) .nil nestedFunctionCode nested
      (valid := fun _ => True) rfl functions_checked.2.2 functions_qualified.2.2 rfl atNested
  rw [function_contraction_receipts.2] at nestedContraction
  cases Option.some.inj nestedContraction
  change assemble _ constants computedFunctionCode computedFunction functionType = some nestedResult
    at atNestedResult
  rw [atComputed] at atNestedResult
  cases Option.some.inj atNestedResult
  refine ⟨computed, nested, result, atComputed, atNested, atResult, ?_⟩
  intro env
  exact ⟨returned env True.intro, (nestedReturned env True.intro).trans (returned env True.intro)⟩

/-- Different internal universe domains and a computed type-valued argument
give literally equal returned function sets, not merely the same inhabitance
claim or a relation on their restrictions. -/
theorem independent_functions_agree
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u})
    (left right : Meaning.{u} 0)
    (atLeft : assemble (interpretHead h seed ground valuation) constants lowerIndependentCode
      independentFunction functionType = some left)
    (atRight : assemble (interpretHead h seed ground valuation) constants upperIndependentCode
      independentFunction functionType = some right)
    (env : Environment.{u} 0) : left.value env = right.value env := by
  obtain ⟨normal, atNormal, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck identityCode functions_checked.1
  exact qualified_rootBeta_coherent (interpretHead h seed ground valuation) constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity successor_qualified
    (ZFSetReplayUniverseModel.universeModel h seed ground valuation groundTyped)
    (empty_constants_model _ constants) .nil lowerIndependentCode upperIndependentCode identityCode
    left right normal (valid := fun _ => True) rfl
    independent_functions_checked_and_qualified.1 independent_functions_checked_and_qualified.2.1
    independent_functions_checked_and_qualified.2.2.1 independent_functions_checked_and_qualified.2.2.2
    rfl atLeft atRight functions_checked.1 (by decide +kernel) atNormal env True.intro

/-- The independently supplied Id fibre mixes the two distinct endpoint
certificates. Actual reflexivity inhabits it by computed comparison, despite
failing the simpler result-formation qualification itself. -/
theorem mixed_reflexivity_membership
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ proofMeaning identityMeaning,
      assemble (interpretHead h seed ground valuation) constants mixedReflexivityCode
        (.refl independentFunction) mixedIdentityType = some proofMeaning ∧
      assemble (interpretHead h seed ground valuation) constants mixedIdentityFormation
        mixedIdentityType (.head functionLevel) = some identityMeaning ∧
      ∀ env : Environment.{u} 0, proofMeaning.value env ∈ identityMeaning.value env := by
  obtain ⟨proofMeaning, atProof, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
      mixedReflexivityCode mixed_identity_checked.2
  obtain ⟨identityMeaning, atIdentity, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
      mixedIdentityFormation mixed_identity_checked.1
  refine ⟨proofMeaning, identityMeaning, atProof, atIdentity, ?_⟩
  intro env
  exact (qualified_rootBeta_identity_membership (interpretHead h seed ground valuation)
    constants Tower.rules TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (ZFSetReplayUniverseModel.universeModel h seed ground valuation groundTyped)
    (empty_constants_model _ constants) .nil functionLevel functionFormation lowerIndependentCode
    upperIndependentCode identityCode proofMeaning identityMeaning (valid := fun _ => True) rfl
    mixed_identity_checked.1 independent_functions_checked_and_qualified.2.2.1
    independent_functions_checked_and_qualified.2.2.2 rfl atProof atIdentity
    functions_checked.1 (by decide +kernel) env True.intro).2

#print axioms functions_checked
#print axioms functions_qualified
#print axioms pair_and_projections_checked
#print axioms pair_and_projections_qualified
#print axioms reflexivity_and_type_checked
#print axioms reflexivity_and_type_qualified
#print axioms computed_identity_boundary
#print axioms qualification_is_not_acceptance
#print axioms dependent_pair_checked_and_qualified
#print axioms computed_type_checked_and_qualified
#print axioms computed_identity_formation_qualified
#print axioms closed_membership
#print axioms computed_function_membership
#print axioms dependent_pair_membership
#print axioms projected_computed_function_membership
#print axioms function_contraction_receipts
#print axioms computed_functions_return_identity
#print axioms independent_functions_checked_and_qualified
#print axioms mixed_identity_checked
#print axioms mixed_reflexivity_not_qualified
#print axioms independent_functions_agree
#print axioms mixed_reflexivity_membership
#print axioms internal_domains_differ
#print axioms substituted_endpoint_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedTypingControls
