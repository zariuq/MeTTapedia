import Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneQualificationBoundary
import Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
import Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding

/-!
# Extensional set, intensional type, and ultrainfinite grounds in one Prime waist

The established Prime authority already retains finite-stage atomless
semantics, externally interpreted set fragments, structural DTT, and one
independently meaningful dependent-Pi computation.  This module adds two
Stone presentations of one unchanged CertificateGSLT checker:

* ordinary Cantor-clopen meaning; and
* a free-ultrafilter perspective with one additional cofinite meaning.

Every public role returns a bundled conservative authority route into the
resulting host.  A role is therefore not a capability label: it carries the
source theory, source checker, exact certificate translation, and reflection
theorem.  The free perspective is deliberately not identified with the
ordinary Stone ground merely because their checkers agree.

This remains a selected atlas.  The set nodes cover the proved set core and
empty/union/powerset fragment, while the computational type node covers the
proved dependent-Pi beta cell.  No full HOTG or full DTT authority is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKSetTypeUltrainfiniteWaist

open Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneGunkSemanticAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneUltraBasisBridge

universe u v

noncomputable section

private abbrev priorTheory :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.theory.{u, v}

private abbrev priorContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.contract.{u, v}

private abbrev ordinaryTheory :=
  Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority.theory
    presentation

private abbrev ordinaryContract :=
  Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority.contract
    presentation

private abbrev freeTheory :=
  Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority.theory
    freePresentation

private abbrev freeContract :=
  Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority.contract
    freePresentation

/-! ## Conservative plural host -/

private def stoneTheory := Coproduct.theory ordinaryTheory freeTheory

private def stoneContract :=
  Coproduct.contract ordinaryTheory freeTheory ordinaryContract freeContract

/-- The established Prime waist, ordinary Stone semantics, or the selected
free-ultrafilter perspective. -/
abbrev Kind := Sum
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.Kind
  (Sum Unit Unit)

def theory := Coproduct.theory priorTheory.{u, v} stoneTheory

def contract :=
  Coproduct.contract priorTheory.{u, v} stoneTheory priorContract.{u, v}
    stoneContract

def priorInclusion :=
  Coproduct.leftInclusion priorTheory.{u, v} stoneTheory priorContract.{u, v}
    stoneContract

private def stoneInclusion :=
  Coproduct.rightInclusion priorTheory.{u, v} stoneTheory priorContract.{u, v}
    stoneContract

def ordinaryStoneInclusion : AuthorityTranslation ordinaryContract contract :=
  AuthorityTranslation.comp
    (Coproduct.leftInclusion ordinaryTheory freeTheory ordinaryContract
      freeContract)
    stoneInclusion.{u, v}

def freePerspectiveInclusion : AuthorityTranslation freeContract contract :=
  AuthorityTranslation.comp
    (Coproduct.rightInclusion ordinaryTheory freeTheory ordinaryContract
      freeContract)
    stoneInclusion.{u, v}

theorem priorInclusion_conservative :
    priorInclusion.{u, v}.toTheoryTranslation.Conservative :=
  Coproduct.leftInclusion_conservative priorTheory.{u, v} stoneTheory
    priorContract.{u, v} stoneContract

theorem ordinaryStoneInclusion_conservative :
    ordinaryStoneInclusion.{u, v}.toTheoryTranslation.Conservative := by
  exact TheoryTranslation.Conservative.comp
    (Coproduct.leftInclusion ordinaryTheory freeTheory ordinaryContract
      freeContract).toTheoryTranslation
    stoneInclusion.{u, v}.toTheoryTranslation
    (Coproduct.leftInclusion_conservative ordinaryTheory freeTheory
      ordinaryContract freeContract)
    (Coproduct.rightInclusion_conservative priorTheory.{u, v} stoneTheory
      priorContract.{u, v} stoneContract)

theorem freePerspectiveInclusion_conservative :
    freePerspectiveInclusion.{u, v}.toTheoryTranslation.Conservative := by
  exact TheoryTranslation.Conservative.comp
    (Coproduct.rightInclusion ordinaryTheory freeTheory ordinaryContract
      freeContract).toTheoryTranslation
    stoneInclusion.{u, v}.toTheoryTranslation
    (Coproduct.rightInclusion_conservative ordinaryTheory freeTheory
      ordinaryContract freeContract)
    (Coproduct.rightInclusion_conservative priorTheory.{u, v} stoneTheory
      priorContract.{u, v} stoneContract)

/-! ## Exact routes for the already earned Prime faces -/

private abbrev stagedTheory :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedTheory

private abbrev stagedContract :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedContract

private abbrev setCoreTheory :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.theory

private abbrev setCoreContract :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.contract

private abbrev setOperationTheory :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.theory

private abbrev setOperationContract :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.contract

private abbrev structuralTheory :=
  Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareNIKAuthority.theory

private abbrev structuralContract :=
  Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareNIKAuthority.contract

private abbrev dependentPiTheory :=
  Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceDependentPiExperiment.NIKProfile.theory.{u, v}

private abbrev dependentPiContract :=
  Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceDependentPiExperiment.NIKProfile.contract.{u, v}

def stagedToWaist : AuthorityTranslation stagedContract contract :=
  AuthorityTranslation.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding.stagedToPrime.{u, v}
    priorInclusion.{u, v}

theorem stagedToWaist_conservative :
    stagedToWaist.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding.stagedToPrime.{u, v}.toTheoryTranslation
    priorInclusion.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding.stagedToPrime_conservative.{u, v}
    priorInclusion_conservative.{u, v}

def setCoreToWaist : AuthorityTranslation setCoreContract contract :=
  AuthorityTranslation.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding.setCoreToPrime.{u, v}
    priorInclusion.{u, v}

theorem setCoreToWaist_conservative :
    setCoreToWaist.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding.setCoreToPrime.{u, v}.toTheoryTranslation
    priorInclusion.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding.setCoreToPrime_conservative.{u, v}
    priorInclusion_conservative.{u, v}

def setOperationToWaist : AuthorityTranslation setOperationContract contract :=
  AuthorityTranslation.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding.operationToPrime.{u, v}
    priorInclusion.{u, v}

theorem setOperationToWaist_conservative :
    setOperationToWaist.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding.operationToPrime.{u, v}.toTheoryTranslation
    priorInclusion.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding.operationToPrime_conservative.{u, v}
    priorInclusion_conservative.{u, v}

private def dependentPiToBoolean : AuthorityTranslation dependentPiContract
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.contract :=
  AuthorityTranslation.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.dependentPiInclusion.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.primeInclusion.{u, v}

private theorem dependentPiToBoolean_conservative :
    dependentPiToBoolean.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.dependentPiInclusion.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.primeInclusion.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.dependentPiInclusion_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.primeInclusion_conservative.{u, v}

private def dependentPiToAtomless : AuthorityTranslation dependentPiContract
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.contract :=
  AuthorityTranslation.comp dependentPiToBoolean.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.priorInclusion.{u, v}

private theorem dependentPiToAtomless_conservative :
    dependentPiToAtomless.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    dependentPiToBoolean.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.priorInclusion.{u, v}.toTheoryTranslation
    dependentPiToBoolean_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.priorInclusion_conservative.{u, v}

private def dependentPiToPrior : AuthorityTranslation dependentPiContract
    priorContract :=
  AuthorityTranslation.comp dependentPiToAtomless.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion.{u, v}

private theorem dependentPiToPrior_conservative :
    dependentPiToPrior.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    dependentPiToAtomless.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion.{u, v}.toTheoryTranslation
    dependentPiToAtomless_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion_conservative.{u, v}

def dependentPiToWaist : AuthorityTranslation dependentPiContract contract :=
  AuthorityTranslation.comp dependentPiToPrior.{u, v} priorInclusion.{u, v}

theorem dependentPiToWaist_conservative :
    dependentPiToWaist.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    dependentPiToPrior.{u, v}.toTheoryTranslation
    priorInclusion.{u, v}.toTheoryTranslation
    dependentPiToPrior_conservative.{u, v}
    priorInclusion_conservative.{u, v}

private def structuralToBase : AuthorityTranslation structuralContract
    Mettapedia.Languages.MeTTa.PrimePluralNIKWaist.contract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKWaist.dttInclusion

private theorem structuralToBase_conservative :
    structuralToBase.toTheoryTranslation.Conservative :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKWaist.dttInclusion_conservative

private def structuralToSetCore : AuthorityTranslation structuralContract
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.contract :=
  AuthorityTranslation.comp structuralToBase
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.primeInclusion

private theorem structuralToSetCore_conservative :
    structuralToSetCore.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp structuralToBase.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.primeInclusion.toTheoryTranslation
    structuralToBase_conservative
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.primeInclusion_conservative

private def structuralToDependentPi : AuthorityTranslation structuralContract
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.contract :=
  AuthorityTranslation.comp structuralToSetCore
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.primeInclusion.{u, v}

private theorem structuralToDependentPi_conservative :
    structuralToDependentPi.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp structuralToSetCore.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.primeInclusion.{u, v}.toTheoryTranslation
    structuralToSetCore_conservative
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.primeInclusion_conservative.{u, v}

private def structuralToBoolean : AuthorityTranslation structuralContract
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.contract :=
  AuthorityTranslation.comp structuralToDependentPi.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.primeInclusion.{u, v}

private theorem structuralToBoolean_conservative :
    structuralToBoolean.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    structuralToDependentPi.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.primeInclusion.{u, v}.toTheoryTranslation
    structuralToDependentPi_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.primeInclusion_conservative.{u, v}

private def structuralToAtomless : AuthorityTranslation structuralContract
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.contract :=
  AuthorityTranslation.comp structuralToBoolean.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.priorInclusion.{u, v}

private theorem structuralToAtomless_conservative :
    structuralToAtomless.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    structuralToBoolean.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.priorInclusion.{u, v}.toTheoryTranslation
    structuralToBoolean_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.priorInclusion_conservative.{u, v}

private def structuralToPrior : AuthorityTranslation structuralContract
    priorContract :=
  AuthorityTranslation.comp structuralToAtomless.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion.{u, v}

private theorem structuralToPrior_conservative :
    structuralToPrior.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    structuralToAtomless.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion.{u, v}.toTheoryTranslation
    structuralToAtomless_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion_conservative.{u, v}

def structuralToWaist : AuthorityTranslation structuralContract contract :=
  AuthorityTranslation.comp structuralToPrior.{u, v} priorInclusion.{u, v}

theorem structuralToWaist_conservative :
    structuralToWaist.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    structuralToPrior.{u, v}.toTheoryTranslation
    priorInclusion.{u, v}.toTheoryTranslation
    structuralToPrior_conservative.{u, v}
    priorInclusion_conservative.{u, v}

/-! ## Role-indexed routes with mathematical payload -/

inductive Role where
  | finiteStageAtomless
  | extensionalSetCore
  | extensionalSetOperations
  | intensionalStructuralType
  | intensionalDependentPi
  | ordinaryStone
  | freeStonePerspective
  deriving DecidableEq, Repr

inductive Face where
  | generativeGround
  | extensionalSet
  | intensionalType
  | ordinaryStoneGround
  | perspectivalStoneGround
  deriving DecidableEq, Repr

def Role.face : Role -> Face
  | .finiteStageAtomless => .generativeGround
  | .extensionalSetCore => .extensionalSet
  | .extensionalSetOperations => .extensionalSet
  | .intensionalStructuralType => .intensionalType
  | .intensionalDependentPi => .intensionalType
  | .ordinaryStone => .ordinaryStoneGround
  | .freeStonePerspective => .perspectivalStoneGround

def hostObject : AuthorityObject where
  Kind := Kind
  family := theory.{u, v}
  contract := contract.{u, v}

def selectedRoute : (role : Role) ->
    ConservativeAuthorityRoute hostObject.{u, v}
  | .finiteStageAtomless =>
      { source :=
          { Kind := Unit
            family := stagedTheory
            contract := stagedContract }
        translation := stagedToWaist.{u, v}
        conservative := stagedToWaist_conservative.{u, v} }
  | .extensionalSetCore =>
      { source :=
          { Kind := Unit
            family := setCoreTheory
            contract := setCoreContract }
        translation := setCoreToWaist.{u, v}
        conservative := setCoreToWaist_conservative.{u, v} }
  | .extensionalSetOperations =>
      { source :=
          { Kind := Unit
            family := setOperationTheory
            contract := setOperationContract }
        translation := setOperationToWaist.{u, v}
        conservative := setOperationToWaist_conservative.{u, v} }
  | .intensionalStructuralType =>
      { source :=
          { Kind := Unit
            family := structuralTheory
            contract := structuralContract }
        translation := structuralToWaist.{u, v}
        conservative := structuralToWaist_conservative.{u, v} }
  | .intensionalDependentPi =>
      { source :=
          { Kind := Unit
            family := dependentPiTheory.{u, v}
            contract := dependentPiContract.{u, v} }
        translation := dependentPiToWaist.{u, v}
        conservative := dependentPiToWaist_conservative.{u, v} }
  | .ordinaryStone =>
      { source :=
          { Kind := Unit
            family := ordinaryTheory
            contract := ordinaryContract }
        translation := ordinaryStoneInclusion.{u, v}
        conservative := ordinaryStoneInclusion_conservative.{u, v} }
  | .freeStonePerspective =>
      { source :=
          { Kind := Unit
            family := freeTheory
            contract := freeContract }
        translation := freePerspectiveInclusion.{u, v}
        conservative := freePerspectiveInclusion_conservative.{u, v} }

theorem selected_check_eq_source (role : Role)
    (kind : (selectedRoute.{u, v} role).source.Kind)
    (claim : (selectedRoute.{u, v} role).source.family.Claim kind)
    (certificate :
      (selectedRoute.{u, v} role).source.contract.Certificate kind) :
    (contract.{u, v}.checker
      ((selectedRoute.{u, v} role).translation.mapKind kind)).check
        ((selectedRoute.{u, v} role).translation.mapClaim kind claim)
        ((selectedRoute.{u, v} role).translation.mapCertificate
          kind certificate) =
      ((selectedRoute.{u, v} role).source.contract.checker kind).check
        claim certificate :=
  ConservativeAuthorityRoute.check_eq_source
    (selectedRoute.{u, v} role) kind claim certificate

theorem selected_scope_iff_source (role : Role)
    (kind : (selectedRoute.{u, v} role).source.Kind)
    (claim : (selectedRoute.{u, v} role).source.family.Claim kind) :
    theory.{u, v}.Scope
        ((selectedRoute.{u, v} role).translation.mapKind kind)
        ((selectedRoute.{u, v} role).translation.mapClaim kind claim) <->
      (selectedRoute.{u, v} role).source.family.Scope kind claim :=
  ConservativeAuthorityRoute.scope_iff_source
    (selectedRoute.{u, v} role) kind claim

theorem selected_meaning_iff_source (role : Role)
    (kind : (selectedRoute.{u, v} role).source.Kind)
    (claim : (selectedRoute.{u, v} role).source.family.Claim kind) :
    theory.{u, v}.Meaning
        ((selectedRoute.{u, v} role).translation.mapKind kind)
        ((selectedRoute.{u, v} role).translation.mapClaim kind claim) <->
      (selectedRoute.{u, v} role).source.family.Meaning kind claim :=
  ConservativeAuthorityRoute.meaning_iff_source
    (selectedRoute.{u, v} role) kind claim

/-! ## Discriminating controls -/

namespace Canary

theorem finiteStage_replays :
    (contract.{u, v}.checker (stagedToWaist.{u, v}.mapKind ())).check
      (stagedToWaist.{u, v}.mapClaim ()
        Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary.properPartSentence)
      (stagedToWaist.{u, v}.mapCertificate () ()) = true := by
  rw [stagedToWaist.{u, v}.check_commutes]
  exact
    Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.Canary.properPart_replays

theorem setOperation_replays :
    (contract.{u, v}.checker
      (setOperationToWaist.{u, v}.mapKind ())).check
      (setOperationToWaist.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula)
      (setOperationToWaist.{u, v}.mapCertificate ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.AxiomTag.unionIntro.proof) =
      true := by
  rw [setOperationToWaist.{u, v}.check_commutes]
  exact
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.Canary.unionIntro_replays

theorem structuralType_replays :
    (contract.{u, v}.checker
      (structuralToWaist.{u, v}.mapKind ())).check
      (structuralToWaist.{u, v}.mapClaim ()
        Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareFormedTyping.Examples.simplePiQuery)
      (structuralToWaist.{u, v}.mapCertificate ()
        Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareFormedTyping.Examples.simplePiIntrinsic.raw) =
      true := by
  rw [structuralToWaist.{u, v}.check_commutes]
  exact
    Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareNIKAuthority.simplePi_replays

theorem dependentPi_replays :
    (contract.{u, v}.checker
      (dependentPiToWaist.{u, v}.mapKind ())).check
      (dependentPiToWaist.{u, v}.mapClaim ()
        Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceDependentPiExperiment.NIKProfile.canonicalCandidate)
      (dependentPiToWaist.{u, v}.mapCertificate ()
        Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceDependentPiExperiment.NIKProfile.canonicalCertificate) =
      true := by
  rw [dependentPiToWaist.{u, v}.check_commutes]
  exact
    Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceDependentPiExperiment.NIKProfile.canonical_certificate_replays

theorem ordinaryStone_replays :
    (contract.{u, v}.checker
      (ordinaryStoneInclusion.{u, v}.mapKind ())).check
      (ordinaryStoneInclusion.{u, v}.mapClaim () perfectStoneClaim)
      (ordinaryStoneInclusion.{u, v}.mapCertificate ()
        perfectStoneCertificate) = true := by
  rw [ordinaryStoneInclusion.{u, v}.check_commutes]
  exact perfectStone_certificate_accepted

theorem freePerspective_replays_same_certificate :
    (contract.{u, v}.checker
      (freePerspectiveInclusion.{u, v}.mapKind ())).check
      (freePerspectiveInclusion.{u, v}.mapClaim () perfectStoneClaim)
      (freePerspectiveInclusion.{u, v}.mapCertificate ()
        perfectStoneCertificate) = true := by
  rw [freePerspectiveInclusion.{u, v}.check_commutes]
  exact free_checker_accepts_perfectStone

theorem freePerspective_has_extra_meaning :
    theory.{u, v}.Meaning
      (freePerspectiveInclusion.{u, v}.mapKind ())
      (freePerspectiveInclusion.{u, v}.mapClaim ()
        cofinitePerspectiveClaim) :=
  freePerspectiveInclusion.{u, v}.meaning_preserved () _
    cofinitePerspective_free_meaning

theorem ordinaryStone_lacks_extra_meaning :
    Not (theory.{u, v}.Meaning
      (ordinaryStoneInclusion.{u, v}.mapKind ())
      (ordinaryStoneInclusion.{u, v}.mapClaim ()
        cofinitePerspectiveClaim)) := by
  intro meaningful
  exact cofinitePerspective_not_ordinary
    (ordinaryStoneInclusion_conservative.{u, v}.meaning_reflecting () _
      meaningful)

theorem freePerspective_extra_meaning_not_scope :
    Not (theory.{u, v}.Scope
      (freePerspectiveInclusion.{u, v}.mapKind ())
      (freePerspectiveInclusion.{u, v}.mapClaim ()
        cofinitePerspectiveClaim)) := by
  intro inScope
  exact
    Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneQualificationBoundary.free_cofinite_semantic_gap.2
    (freePerspectiveInclusion_conservative.{u, v}.scope_reflecting () _
      inScope)

theorem set_and_dependent_type_kinds_are_distinct :
    setOperationToWaist.{u, v}.mapKind () ≠
      dependentPiToWaist.{u, v}.mapKind () := by
  intro equality
  cases equality

theorem ordinary_and_free_stone_kinds_are_distinct :
    ordinaryStoneInclusion.{u, v}.mapKind () ≠
      freePerspectiveInclusion.{u, v}.mapKind () := by
  intro equality
  cases equality

end Canary

#print axioms ConservativeAuthorityRoute.postcompose
#print axioms selected_check_eq_source
#print axioms selected_scope_iff_source
#print axioms selected_meaning_iff_source
#print axioms stagedToWaist_conservative
#print axioms setCoreToWaist_conservative
#print axioms setOperationToWaist_conservative
#print axioms structuralToWaist_conservative
#print axioms dependentPiToWaist_conservative
#print axioms ordinaryStoneInclusion_conservative
#print axioms freePerspectiveInclusion_conservative
#print axioms Canary.finiteStage_replays
#print axioms Canary.setOperation_replays
#print axioms Canary.structuralType_replays
#print axioms Canary.dependentPi_replays
#print axioms Canary.ordinaryStone_replays
#print axioms Canary.freePerspective_replays_same_certificate
#print axioms Canary.freePerspective_has_extra_meaning
#print axioms Canary.ordinaryStone_lacks_extra_meaning
#print axioms Canary.freePerspective_extra_meaning_not_scope
#print axioms Canary.set_and_dependent_type_kinds_are_distinct
#print axioms Canary.ordinary_and_free_stone_kinds_are_distinct

end

end Mettapedia.Languages.MeTTa.PrimePluralNIKSetTypeUltrainfiniteWaist
