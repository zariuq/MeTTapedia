import Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding
import Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
import Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas

/-!
# Exact finite-stage grounding in the plural bootstrap atlas

The exhaustive Cantor-stage authority and the plural bootstrap atlas have
different claim and certificate languages.  This module connects them at the
strongest available boundary: an exact authority translation into the
atlas's `modelSound` lane.

A closed atomless formula becomes a tagged lower contract claim.  The staged
unit receipt becomes the atlas's semantic-decision receipt.  Checker replay
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
open Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

private abbrev finiteStageTheory :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedTheory

private abbrev finiteStageContract :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedContract

private abbrev atlasTheory :=
  Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.layer.toTheoryFamily

private abbrev atlasContract :=
  Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.layer.toAuthorityContract

/-! ## Exact translation into `modelSound` -/

/-- Interpret each finite-stage semantic claim as the corresponding tagged
`modelSound` claim in the plural lower atlas. -/
def stagedToAtlasModel :
    AuthorityTranslation finiteStageContract atlasContract where
  mapKind := id
  mapSignature := fun _signature => atlasTheory.signatureOf ()
  signature_commutes := by
    intro kind
    cases kind
    rfl
  mapClaim := fun _kind formula =>
    Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim formula
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

@[simp] theorem stagedToAtlasModel_mapClaim (formula : Formula 0) :
    stagedToAtlasModel.mapClaim () formula =
      Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
        formula :=
  rfl

@[simp] theorem stagedToAtlasModel_mapCertificate
    (certificate : finiteStageContract.Certificate ()) :
    stagedToAtlasModel.mapCertificate () certificate = .semanticDecision :=
  rfl

theorem stagedToAtlasModel_conservative :
    stagedToAtlasModel.toTheoryTranslation.Conservative where
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
theorem stagedToAtlasModel_check_commutes (formula : Formula 0)
    (certificate : finiteStageContract.Certificate ()) :
    (atlasContract.checker ()).check
        (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
          formula)
        .semanticDecision =
      (finiteStageContract.checker ()).check formula certificate :=
  stagedToAtlasModel.check_commutes () formula certificate

/-- Atlas `modelSound` meaning is exactly finite-stage meaning on the image. -/
theorem atlasModelMeaning_iff_stagedMeaning (formula : Formula 0) :
    atlasTheory.Meaning ()
        (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
          formula) <->
      finiteStageTheory.Meaning () formula :=
  TheoryTranslation.meaning_iff_of_conservative
    stagedToAtlasModel.toTheoryTranslation
    stagedToAtlasModel_conservative () formula

/-- Atlas acceptance is qualified against staged meaning rather than used to
define it. -/
theorem atlasModelAccepts_iff_stagedMeaning (formula : Formula 0) :
    (atlasContract.checker ()).check
        (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
          formula)
        .semanticDecision = true <->
      finiteStageTheory.Meaning () formula := by
  change decideClosed formula = true <-> StagedMeaning formula
  exact stagedDecisionKernel.correct formula

/-! ## Image controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary

theorem properPart_replays_in_atlas :
    (atlasContract.checker ()).check
        (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
          properPartSentence)
        .semanticDecision = true := by
  rw [stagedToAtlasModel_check_commutes properPartSentence ()]
  exact
    Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.Canary.properPart_replays

/-- Contract kind is part of the translated claim, so a staged model claim
cannot appear in the source-soundness lane. -/
theorem sourceSound_not_in_image (formula : Formula 0) :
    Not (exists stagedFormula : Formula 0,
      stagedToAtlasModel.mapClaim () stagedFormula =
        Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.sourceSoundClaim
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
      stagedToAtlasModel.mapCertificate () certificate =
        Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.Certificate.refinementEvidence
          evidence) := by
  rintro ⟨certificate, equalCertificates⟩
  cases certificate
  cases equalCertificates

end Canary

#print axioms stagedToAtlasModel
#print axioms stagedToAtlasModel_conservative
#print axioms stagedToAtlasModel_check_commutes
#print axioms atlasModelMeaning_iff_stagedMeaning
#print axioms atlasModelAccepts_iff_stagedMeaning
#print axioms Canary.properPart_replays_in_atlas
#print axioms Canary.sourceSound_not_in_image
#print axioms Canary.refinementEvidence_not_in_certificate_image

end Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding
