import Mettapedia.Languages.Metamath.MM2SourceAssertionPublication

/-!
# Native source assertion execution inventory

This module assembles the independently checked assertion-frame snapshot,
mandatory-variable certificate, frame-selection, and publication machines.
The shared finite-list membership machine supplies the only membership
decision procedure used by the certificate and frame selector.

Verifier code and source-derived data remain separate.  The verifier inventory
is database-independent.  Publication plans are generated only for `$a`
candidates and carry the exact runtime rows derived from that candidate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceAssertionExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceAssertionCertificateExecution
open Mettapedia.Languages.Metamath.MM2SourceAssertionFrameExecution
open Mettapedia.Languages.Metamath.MM2SourceAssertionFrameSelectionExecution
open Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
open Mettapedia.Languages.Metamath.MM2SourceAssertionPublication
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.MM2FiniteListMembership

/-! ## Database-independent verifier inventory -/

/-- All executable rules needed by the native `$a` transaction.  Each phase
owns a bounded opaque reloader for precisely its finite rule inventory. -/
def nativeAssertionTransactionRules : List Atom :=
  assertionFrameSnapshotRules ++ [assertionFrameReloadRule] ++
    assertionCertificateRules ++ [assertionCertificateReloadRule] ++
      assertionFrameSelectionRules ++
        [assertionFrameSelectionReloadRule] ++
          assertionPublicationRules ++ [assertionPublicationReloadRule] ++
            membershipRules

def nativeAssertionTransactionDirectives : List SourceExecFact :=
  assertionFrameSnapshotDirectives ++ [assertionFrameReloadDirective] ++
    assertionCertificateDirectives ++ [assertionCertificateReloadDirective] ++
      assertionFrameSelectionDirectives ++
        [assertionFrameSelectionReloadDirective] ++
          assertionPublicationDirectives ++
            [assertionPublicationReloadDirective] ++ membershipDirectives

theorem nativeAssertionTransactionRules_extract_exact :
    nativeAssertionTransactionRules.filterMap extractSupportedSourceExecFact =
      nativeAssertionTransactionDirectives := by
  simp [nativeAssertionTransactionRules,
    nativeAssertionTransactionDirectives,
    assertionFrameSnapshotRules_extract_exact,
    extract_assertionFrameReloadRule_exact,
    assertionCertificateRules_extract_exact,
    extract_assertionCertificateReloadRule_exact,
    assertionFrameSelectionRules_extract_exact,
    extract_assertionFrameSelectionReloadRule_exact,
    assertionPublicationRules_extract_exact,
    extract_assertionPublicationReloadRule_exact,
    membershipRules_extract_exact]

def nativeAssertionVerifierRules : List Atom :=
  nativeAssertionTransactionRules

def nativeAssertionVerifierDirectives : List SourceExecFact :=
  nativeAssertionTransactionDirectives

theorem nativeAssertionVerifierRules_extract_exact :
    nativeAssertionVerifierRules.filterMap extractSupportedSourceExecFact =
      nativeAssertionVerifierDirectives := by
  exact nativeAssertionTransactionRules_extract_exact

/-- Opaque verifier-owned data needed to reinstall finite rule inventories and
to continue the source formula and source-verifier protocols. -/
def nativeAssertionVerifierStaticRows : List Atom :=
  assertionFrameSnapshotStaticRows ++
    assertionCertificateRuleCaptureRows ++
      [assertionCertificateReloadRuleCaptureRow] ++
      assertionFrameSelectionRuleCaptureRows ++
        [assertionFrameSelectionReloadRuleCaptureRow] ++
        assertionPublicationRuleCaptureRows ++ membershipRuleCaptureRows ++
          [membershipReloadRuleCaptureRow,
           assertionPublicationReloadRuleCaptureRow,
           assertionPublicationSourceReloadCaptureRow]

/-! ## Source-derived `$a` publication plans -/

def isNativeAxiomCandidate (candidate : SourceAssertionCandidate) : Bool :=
  match candidate.statement, candidate.gate with
  | .axiomatic _ _ _ _ _, .immediate => true
  | _, _ => false

@[simp] theorem isNativeAxiomCandidate_axiomatic_immediate
    (site label typecode body terminator) (position nextPosition
      assertionPosition nextAssertionPosition : Nat)
    (mandatoryVariables : List String) (assertion : SourceAssertion) :
    isNativeAxiomCandidate
        { position, nextPosition,
          statement := .axiomatic site label typecode body terminator,
          assertionPosition, nextAssertionPosition,
          gate := .immediate, mandatoryVariables, assertion } = true := by
  rfl

@[simp] theorem isNativeAxiomCandidate_provable
    (site label typecode body proof separator terminator)
    (position nextPosition assertionPosition nextAssertionPosition : Nat)
    (gate : SourceActionGate) (mandatoryVariables : List String)
    (assertion : SourceAssertion) :
    isNativeAxiomCandidate
        { position, nextPosition,
          statement :=
            .provable site label typecode body proof separator terminator,
          assertionPosition, nextAssertionPosition, gate,
          mandatoryVariables, assertion } = false := by
  cases gate <;> rfl

def nativeAxiomCandidates
    (candidates : List SourceAssertionCandidate) :
    List SourceAssertionCandidate :=
  candidates.filter isNativeAxiomCandidate

/-- Exact publication plans for the source-derived native `$a` candidates.
No `$p` candidate enters this stream; theorem assertions remain proof-gated.
-/
def nativeAssertionPublicationRows (owner : Atom)
    (candidates : List SourceAssertionCandidate) : List Atom :=
  (nativeAxiomCandidates candidates).flatMap
    (assertionPublicationPlanRows owner)

theorem nativeAssertionPublicationRows_all_proofNeutral
    (owner : Atom) (candidates : List SourceAssertionCandidate) :
    (nativeAssertionPublicationRows owner candidates).all
      Mettapedia.Languages.Metamath.MM2SourceEventTransformation.isProofNeutralInitialAtom =
        true := by
  simp [nativeAssertionPublicationRows,
    assertionPublicationPlanRows_all_proofNeutral]

theorem mem_nativeAssertionPublicationRows
    {owner : Atom} {candidates : List SourceAssertionCandidate} {row : Atom}
    (member : row ∈ nativeAssertionPublicationRows owner candidates) :
    ∃ candidate ∈ candidates,
      isNativeAxiomCandidate candidate = true ∧
        row ∈ assertionPublicationPlanRows owner candidate := by
  simp only [nativeAssertionPublicationRows, nativeAxiomCandidates,
    List.mem_flatMap, List.mem_filter] at member
  obtain ⟨candidate, ⟨inCandidates, native⟩, inPlan⟩ := member
  exact ⟨candidate, inCandidates, native, inPlan⟩

/-! ## Positive and negative classification controls -/

private def fixtureSpan :
    Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan :=
  { fileId := "native-assertion.mm", start := 0, stop := 1 }

private def fixtureName (name : String) :
    LocatedName :=
  { span := fixtureSpan, name }

private def fixtureAssertion : SourceAssertion :=
  { label := "ax"
    formula := { typecode := "wff", body := [] }
    frame := { distinctVariables := [], hypothesisLabels := [] }
    hypotheses := [] }

private def axiomCandidate : SourceAssertionCandidate :=
  { position := 0
    nextPosition := 1
    statement := .axiomatic fixtureSpan (fixtureName "ax")
      (fixtureName "wff") [] fixtureSpan
    assertionPosition := 0
    nextAssertionPosition := 1
    gate := .immediate
    mandatoryVariables := []
    assertion := fixtureAssertion }

private def theoremCandidate : SourceAssertionCandidate :=
  { axiomCandidate with
    statement := .provable fixtureSpan (fixtureName "th")
      (fixtureName "wff") [] (.normal []) fixtureSpan fixtureSpan
    gate := .afterProof }

theorem axiomCandidate_is_native :
    isNativeAxiomCandidate axiomCandidate = true := by
  rfl

theorem theoremCandidate_is_not_native :
    isNativeAxiomCandidate theoremCandidate = false := by
  rfl

theorem mixedCandidates_emit_only_axiom_plan :
    nativeAssertionPublicationRows (.symbol "source")
        [axiomCandidate, theoremCandidate] =
      assertionPublicationPlanRows (.symbol "source") axiomCandidate := by
  simp [nativeAssertionPublicationRows, nativeAxiomCandidates,
    axiomCandidate, theoremCandidate, isNativeAxiomCandidate]

#print axioms nativeAssertionTransactionRules_extract_exact
#print axioms nativeAssertionVerifierRules_extract_exact
#print axioms nativeAssertionPublicationRows_all_proofNeutral
#print axioms mem_nativeAssertionPublicationRows
#print axioms mixedCandidates_emit_only_axiom_plan

end Mettapedia.Languages.Metamath.MM2SourceAssertionExecution
