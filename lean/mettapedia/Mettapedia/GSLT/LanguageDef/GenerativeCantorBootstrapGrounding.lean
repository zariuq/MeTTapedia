import Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding
import Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
import Mettapedia.GSLT.LanguageDef.NIKBaseChecker

/-!
# Exact finite-stage grounding in the base checker

The exhaustive Cantor-stage authority and the base checker have
different claim and certificate languages.  This module connects them at the
strongest available boundary: an exact authority translation into the
base checker's `modelSound` lane.

A closed atomless formula becomes a tagged lower contract claim.  The staged
unit receipt becomes the base checker's semantic-decision receipt.  Checking
commutes exactly, and the translation is conservative because finite-stage
meaning is equivalent to cold Cantor-clopen meaning.

The image remains deliberately proper.  No staged formula maps to a
`sourceSound` claim, and no staged receipt maps to refinement evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
open Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

private abbrev finiteStageTheory :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedTheory

private abbrev finiteStageContract :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedContract

private abbrev baseCheckerTheory :=
  Mettapedia.GSLT.LanguageDef.NIKBaseChecker.layer.toTheoryFamily

private abbrev baseCheckerContract :=
  Mettapedia.GSLT.LanguageDef.NIKBaseChecker.layer.toAuthorityContract

/-! ## Exact translation into `modelSound` -/

/-- Interpret each finite-stage semantic claim as the corresponding tagged
`modelSound` claim in the base checker. -/
def stagedToBaseCheckerModel :
    CertifiedTranslation finiteStageContract baseCheckerContract where
  mapKind := id
  mapSignature := fun _signature => baseCheckerTheory.signatureOf ()
  signature_commutes := by
    intro kind
    cases kind
    rfl
  mapClaim := fun _kind formula =>
    Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim formula
  mapCertificate := fun _kind _certificate => .semanticDecision
  check_commutes := by
    intro kind formula certificate
    cases kind
    cases certificate
    rfl
  meaning_preserved := by
    intro kind formula meaningful
    cases kind
    change StagedMeaning formula at meaningful
    change ColdMeaning formula
    exact (stagedMeaning_iff_coldMeaning formula).mp meaningful

@[simp] theorem stagedToBaseCheckerModel_mapClaim (formula : Formula 0) :
    stagedToBaseCheckerModel.mapClaim () formula =
      Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
        formula :=
  rfl

@[simp] theorem stagedToBaseCheckerModel_mapCertificate
    (certificate : finiteStageContract.Certificate ()) :
    stagedToBaseCheckerModel.mapCertificate () certificate = .semanticDecision :=
  rfl

theorem stagedToBaseCheckerModel_conservative :
    stagedToBaseCheckerModel.toTheoryTranslation.Conservative where
  scope_reflecting := by
    intro kind formula meaningful
    cases kind
    change ColdMeaning formula at meaningful
    change StagedMeaning formula
    exact (stagedMeaning_iff_coldMeaning formula).mpr meaningful
  meaning_reflecting := by
    intro kind formula meaningful
    cases kind
    change ColdMeaning formula at meaningful
    change StagedMeaning formula
    exact (stagedMeaning_iff_coldMeaning formula).mpr meaningful

/-- Exact replay survives the change in both claim and certificate syntax. -/
theorem stagedToBaseCheckerModel_check_commutes (formula : Formula 0)
    (certificate : finiteStageContract.Certificate ()) :
    (baseCheckerContract.checker ()).check
        (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
          formula)
        .semanticDecision =
      (finiteStageContract.checker ()).check formula certificate :=
  stagedToBaseCheckerModel.check_commutes () formula certificate

/-- Base-checker `modelSound` meaning is exactly finite-stage meaning on the image. -/
theorem baseCheckerModelMeaning_iff_stagedMeaning (formula : Formula 0) :
    baseCheckerTheory.Meaning ()
        (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
          formula) <->
      finiteStageTheory.Meaning () formula :=
  TheoryTranslation.meaning_iff_of_conservative
    stagedToBaseCheckerModel.toTheoryTranslation
    stagedToBaseCheckerModel_conservative () formula

/-- Base-checker acceptance is qualified against staged meaning rather than used to
define it. -/
theorem baseCheckerModelAccepts_iff_stagedMeaning (formula : Formula 0) :
    (baseCheckerContract.checker ()).check
        (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
          formula)
        .semanticDecision = true <->
      finiteStageTheory.Meaning () formula := by
  change decideClosed formula = true <-> StagedMeaning formula
  exact stagedDecisionKernel.correct formula

/-! ## Image controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary

theorem properPart_accepted_by_base_checker :
    (baseCheckerContract.checker ()).check
        (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
          properPartSentence)
        .semanticDecision = true := by
  rw [stagedToBaseCheckerModel_check_commutes properPartSentence ()]
  exact
    Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.Canary.properPart_replays

/-- Contract kind is part of the translated claim, so a staged model claim
cannot appear in the source-soundness lane. -/
theorem sourceSound_not_in_image (formula : Formula 0) :
    Not (exists stagedFormula : Formula 0,
      stagedToBaseCheckerModel.mapClaim () stagedFormula =
        Mettapedia.GSLT.LanguageDef.NIKBaseChecker.sourceSoundClaim
          formula) := by
  rintro ⟨stagedFormula, equalClaims⟩
  have equalKinds := congrArg
    (fun claim => claim.kind) equalClaims
  change BootstrapContractKind.modelSound =
    BootstrapContractKind.sourceSound at equalKinds
  cases equalKinds

/-- Refinement evidence retains distinct provenance and cannot be synthesized
from the staged semantic receipt. -/
theorem refinementEvidence_not_in_certificate_image
    (evidence : RefinementMetaAuthority.Certificate) :
    Not (exists certificate : finiteStageContract.Certificate (),
      stagedToBaseCheckerModel.mapCertificate () certificate =
        Mettapedia.GSLT.LanguageDef.NIKBaseChecker.Certificate.refinementEvidence
          evidence) := by
  rintro ⟨certificate, equalCertificates⟩
  cases certificate
  cases equalCertificates

end Canary

#print axioms stagedToBaseCheckerModel
#print axioms stagedToBaseCheckerModel_conservative
#print axioms stagedToBaseCheckerModel_check_commutes
#print axioms baseCheckerModelMeaning_iff_stagedMeaning
#print axioms baseCheckerModelAccepts_iff_stagedMeaning
#print axioms Canary.properPart_accepted_by_base_checker
#print axioms Canary.sourceSound_not_in_image
#print axioms Canary.refinementEvidence_not_in_certificate_image

end Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding
