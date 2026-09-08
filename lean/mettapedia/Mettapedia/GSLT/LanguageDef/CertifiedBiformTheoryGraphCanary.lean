import Mettapedia.GSLT.LanguageDef.CertifiedBiformTheoryGraph
import Mettapedia.GSLT.LanguageDef.BiformTheoryGraphCanary

/-!
# Cross-logic certificate replay canary

This specimen qualifies the established simple-to-dependent biform route with
native thin proof objects on both sides.  The positive route maps the complete
source proof object to the translated target theorem and replays exactly.  The
negative route retains the same biform arrow but maps every source certificate
to a different target theorem; replay rejects that independently well-typed
pair.

The canary separates three obligations: theorem preservation, operational
event meaning, and executable certificate replay.  Satisfying either of the
first two does not silently authorize the third.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertifiedBiformTheoryGraphCanary

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertifiedBiformTheoryGraph
open Mettapedia.GSLT.LanguageDef.BiformTheoryGraphCanary

abbrev sourceCalculus :=
  PiInstitution.ProofCalculus.thin sourceTheory.institution

abbrev targetCalculus :=
  PiInstitution.ProofCalculus.thin targetTheory.institution

private instance sourceSentenceDecidableEq :
    DecidableEq
      (sourceTheory.institution.sentence.obj sourceTheory.logical.signature) := by
  change DecidableEq (Sigma fun _ : Bool => Bool)
  infer_instance

private instance targetSentenceDecidableEq :
    DecidableEq
      (targetTheory.institution.sentence.obj targetTheory.logical.signature) := by
  change DecidableEq (Sigma fun _ : Bool => Bool)
  infer_instance

def sourceAuthority :=
  nativeProofBoundary sourceTheory.logical sourceCalculus

def targetAuthority :=
  nativeProofBoundary targetTheory.logical targetCalculus

def qualifiedSource :
    CertifiedBiformTheoryGraph.Object where
  biform := sourceBiform
  calculus := sourceCalculus
  contract := sourceAuthority

def qualifiedTarget :
    CertifiedBiformTheoryGraph.Object where
  biform := targetBiform
  calculus := targetCalculus
  contract := targetAuthority

/-- Transport the entire native thin proof object through the same
cross-institution sentence map as the biform route. -/
def mapCertificate
    (certificate : qualifiedSource.contract.Certificate ()) :
    qualifiedTarget.contract.Certificate () :=
  ⟨TheoryGraph.translateSentence
      (TheoryGraph.Hom.institution logicalRoute)
      (TheoryGraph.Hom.mapSignature logicalRoute) certificate.1,
    TheoryGraph.Hom.preserves logicalRoute certificate.2⟩

/-- Positive control: native proof replay commutes across the actual
simple-to-dependent logical boundary. -/
def qualifiedRoute : qualifiedSource ⟶ qualifiedTarget where
  biform := biformRoute
  mapCertificate := mapCertificate
  check_commutes := by
    intro formula certificate
    rfl

def sourceFalseCertificate : qualifiedSource.contract.Certificate () :=
  ⟨falseSentence, falseSentence_mem⟩

def targetTrueCertificate : qualifiedTarget.contract.Certificate () :=
  ⟨targetTrueSentence,
    TheoryGraph.Hom.preserves logicalRoute trueSentence_mem⟩

/-- A well-typed but replay-breaking certificate map. -/
def wrongCertificateMap
    (_certificate : qualifiedSource.contract.Certificate ()) :
    qualifiedTarget.contract.Certificate () :=
  targetTrueCertificate

def replayBreakingPair :
    BiformTheoryGraph.Hom
        qualifiedSource.biform qualifiedTarget.biform ×
      (qualifiedSource.contract.Certificate () →
        qualifiedTarget.contract.Certificate ()) :=
  (biformRoute, wrongCertificateMap)

theorem source_false_certificate_accepts :
    (qualifiedSource.contract.checker ()).check
      falseSentence sourceFalseCertificate = true := by
  rfl

theorem translated_false_with_true_certificate_rejects :
    (qualifiedTarget.contract.checker ()).check
      targetFalseSentence targetTrueCertificate = false := by
  simp only [qualifiedTarget, targetAuthority, nativeProofBoundary_check,
    nativeProofConclusion, targetTrueCertificate]
  exact decide_eq_false target_sentences_distinct.symm

/-- Negative control: a preserved biform route is not enough when certificate
replay does not commute through its native sentence translation. -/
theorem wrong_certificate_map_not_replayCompatible :
    ¬ ReplayCompatible (source := qualifiedSource) (target := qualifiedTarget)
      replayBreakingPair := by
  intro compatible
  have replay := compatible falseSentence sourceFalseCertificate
  change
    (qualifiedTarget.contract.checker ()).check
        targetFalseSentence targetTrueCertificate =
      (qualifiedSource.contract.checker ()).check
        falseSentence sourceFalseCertificate at replay
  rw [translated_false_with_true_certificate_rejects,
    source_false_certificate_accepts] at replay
  cases replay

theorem no_qualified_route_with_replay_breaking_pair :
    ¬ ∃ route : qualifiedSource ⟶ qualifiedTarget,
      routePair route = replayBreakingPair := by
  rw [routePair_range_iff_replayCompatible]
  exact wrong_certificate_map_not_replayCompatible

#print axioms sourceAuthority
#print axioms targetAuthority
#print axioms qualifiedRoute
#print axioms source_false_certificate_accepts
#print axioms translated_false_with_true_certificate_rejects
#print axioms wrong_certificate_map_not_replayCompatible
#print axioms no_qualified_route_with_replay_breaking_pair

end Mettapedia.GSLT.LanguageDef.CertifiedBiformTheoryGraphCanary
