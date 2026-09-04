import Mettapedia.Languages.Metamath.MM2SourceActionPlan
import Mettapedia.Languages.Metamath.SourceStateNativeTypes
import Mettapedia.Languages.Metamath.SourceStateGSLT

/-!
# Source-derived assertion candidates for ordered MM2 ingestion

This module annotates the authored raw-source fold with the exact assertion
created by each accepted `$a` or `$p` occurrence.  The candidate is passive
data, not authorization: ordinary MM2 execution must reconstruct its mandatory
frame from the active hypothesis and distinct-variable ledgers before it may
publish any assertion runtime row.

The annotation follows `applyStatement` and therefore has exactly the same
rejection and final-state behavior as the authored source fold.  A theorem
candidate is retained behind the same proof gate as its source action plan.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2SourceAssertionPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceStateGSLT
open Mettapedia.Languages.Metamath.SourceStateNativeTypes

/-! ## Semantic authority -/

/-- An accepted `$a` transition is classified by the selected native type
obtained by applying OSLF to the authored source-state GSLT. -/
theorem axiomDeclaration_inhabits_source_native_type
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (declared : declareAxiom? before label formula = some after) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      SourceStateGSLT.theory).satisfies before
      (sourceStateExactTargetNativeType after).pred := by
  exact local_payload_inhabits_exact_target
    (payload := .declareAxiom label formula) declared

/-! ## Exact passive candidate -/

/-- One accepted assertion-producing source occurrence.  `assertionPosition`
is the length of the assertion table before the source step, not a position
supplied by target data. -/
structure SourceAssertionCandidate where
  position : Nat
  nextPosition : Nat
  statement : RawStatement
  assertionPosition : Nat
  nextAssertionPosition : Nat
  gate : SourceActionGate
  mandatoryVariables : List String
  assertion : SourceAssertion
deriving DecidableEq

def sourceAssertionCandidateAtom (owner : Atom)
    (candidate : SourceAssertionCandidate) : Atom :=
  .expression
    [.symbol "mm-source-assertion-candidate", owner,
      natAtom candidate.position, natAtom candidate.nextPosition,
      rawStatementAtom candidate.statement,
      natAtom candidate.assertionPosition,
      natAtom candidate.nextAssertionPosition,
      sourceActionGateAtom candidate.gate,
      listAtom stringAtom candidate.mandatoryVariables,
      sourceAssertionAtom candidate.assertion]

def decodeSourceAssertionCandidateAtom (owner : Atom) :
    Atom -> Option SourceAssertionCandidate
  | .expression
      [.symbol tag, actualOwner, encodedPosition, encodedNextPosition,
        encodedStatement, encodedAssertionPosition,
        encodedNextAssertionPosition, encodedGate,
        encodedMandatoryVariables, encodedAssertion] => do
      guard (tag == "mm-source-assertion-candidate")
      guard (actualOwner == owner)
      let position <- decodeNatAtom encodedPosition
      let nextPosition <- decodeNatAtom encodedNextPosition
      let statement <- decodeRawStatementAtom encodedStatement
      let assertionPosition <- decodeNatAtom encodedAssertionPosition
      let nextAssertionPosition <-
        decodeNatAtom encodedNextAssertionPosition
      let gate <- decodeSourceActionGateAtom encodedGate
      let mandatoryVariables <-
        decodeListAtom decodeStringAtom encodedMandatoryVariables
      let assertion <- decodeSourceAssertionAtom encodedAssertion
      pure
        { position
          nextPosition
          statement
          assertionPosition
          nextAssertionPosition
          gate
          mandatoryVariables
          assertion }
  | _ => none

@[simp] theorem decodeSourceAssertionCandidateAtom_encoded
    (owner : Atom) (candidate : SourceAssertionCandidate) :
    decodeSourceAssertionCandidateAtom owner
        (sourceAssertionCandidateAtom owner candidate) =
      some candidate := by
  cases candidate
  simp [decodeSourceAssertionCandidateAtom, sourceAssertionCandidateAtom]

theorem sourceAssertionCandidateAtom_injective (owner : Atom) :
    Function.Injective (sourceAssertionCandidateAtom owner) := by
  intro left right equal
  have decoded := congrArg (decodeSourceAssertionCandidateAtom owner) equal
  simpa using decoded

@[simp] theorem sourceAssertionCandidateAtom_proofNeutral
    (owner : Atom) (candidate : SourceAssertionCandidate) :
    isProofNeutralInitialAtom
        (sourceAssertionCandidateAtom owner candidate) = true := by
  cases candidate
  simp [sourceAssertionCandidateAtom, isProofNeutralInitialAtom,
    isVerifierTerminalObservation, isVerifierOwnedInternalRowShape,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact]

/-! ## Candidate construction at one accepted source step -/

/-- Compute the assertion annotation proposed by an assertion-producing
statement at a particular source state.  This function performs no admission;
the fold below calls it only after the same statement has been accepted by
`applyStatement`. -/
def sourceAssertionCandidate? (position : Nat) (state : SourceState)
    (statement : RawStatement) (obligations : List TheoremObligation) :
    Option SourceAssertionCandidate :=
  match statement with
  | .axiomatic _ label typecode body _ =>
      match tagBody state body with
      | .rejected _ => none
      | .ok symbols =>
          let formula : ConstantHeadedFormula :=
            { typecode := typecode.name, body := symbols }
          some
            { position
              nextPosition := position + 1
              statement
              assertionPosition := state.assertions.length
              nextAssertionPosition := state.assertions.length + 1
              gate := sourceActionGate obligations
              mandatoryVariables := mandatoryVariableNames state formula
              assertion := sourceAssertion state label.name formula }
  | .provable _ label typecode body _ _ _ =>
      match tagBody state body with
      | .rejected _ => none
      | .ok symbols =>
          let formula : ConstantHeadedFormula :=
            { typecode := typecode.name, body := symbols }
          some
            { position
              nextPosition := position + 1
              statement
              assertionPosition := state.assertions.length
              nextAssertionPosition := state.assertions.length + 1
              gate := sourceActionGate obligations
              mandatoryVariables := mandatoryVariableNames state formula
              assertion := sourceAssertion state label.name formula }
  | _ => none

theorem sourceAssertionCandidate?_statement_is_assertion
    {position : Nat} {state : SourceState} {statement : RawStatement}
    {obligations : List TheoremObligation}
    {candidate : SourceAssertionCandidate}
    (built :
      sourceAssertionCandidate? position state statement obligations =
        some candidate) :
    (exists site label typecode body terminator,
        statement = .axiomatic site label typecode body terminator) ∨
      (exists site label typecode body proof separator terminator,
        statement =
          .provable site label typecode body proof separator terminator) := by
  cases statement <;> simp_all [sourceAssertionCandidate?]

theorem sourceAssertionCandidate?_position_exact
    {position : Nat} {state : SourceState} {statement : RawStatement}
    {obligations : List TheoremObligation}
    {candidate : SourceAssertionCandidate}
    (built :
      sourceAssertionCandidate? position state statement obligations =
        some candidate) :
    candidate.position = position ∧
      candidate.nextPosition = position + 1 ∧
      candidate.assertionPosition = state.assertions.length ∧
      candidate.nextAssertionPosition = state.assertions.length + 1 ∧
      candidate.statement = statement ∧
      candidate.gate = sourceActionGate obligations := by
  cases statement with
  | openScope site => simp [sourceAssertionCandidate?] at built
  | closeScope site => simp [sourceAssertionCandidate?] at built
  | constDecl site names terminator =>
      simp [sourceAssertionCandidate?] at built
  | varDecl site names terminator =>
      simp [sourceAssertionCandidate?] at built
  | djDecl site names terminator =>
      simp [sourceAssertionCandidate?] at built
  | floating site label typecode variableName terminator =>
      simp [sourceAssertionCandidate?] at built
  | essential site label typecode body terminator =>
      simp [sourceAssertionCandidate?] at built
  | axiomatic site label typecode body terminator =>
      simp only [sourceAssertionCandidate?] at built
      split at built
      · simp at built
      · cases built
        simp
  | provable site label typecode body proof separator terminator =>
      simp only [sourceAssertionCandidate?] at built
      split at built
      · simp at built
      · cases built
        simp

/-! ## Source-fold annotation -/

/-- Replay the authored source fold and retain only its accepted assertion
occurrences.  Every state transition is still performed by `applyStatement`;
the candidate compiler does not define a second source semantics. -/
def buildSourceAssertionCandidatesFrom (owner : Atom) :
    Nat -> SourceState -> List RawStatement ->
      FoldResult (SourceState × List SourceAssertionCandidate)
  | _, state, [] => .ok (state, [])
  | position, state, statement :: statements =>
      match applyStatement state statement with
      | .rejected rejection => .rejected rejection
      | .ok (next, obligations) =>
          match buildSourceAssertionCandidatesFrom owner (position + 1)
              next statements with
          | .rejected rejection => .rejected rejection
          | .ok (final, candidates) =>
              let candidates :=
                match sourceAssertionCandidate? position state statement
                    obligations with
                | none => candidates
                | some candidate => candidate :: candidates
              .ok (final, candidates)

def buildSourceAssertionCandidates (owner : Atom)
    (statements : List RawStatement) :
    FoldResult (SourceState × List SourceAssertionCandidate) :=
  buildSourceAssertionCandidatesFrom owner 0 initialState statements

/-- Candidate annotation has exactly the rejection and final-state behavior
of the authored statement fold. -/
theorem buildSourceAssertionCandidatesFrom_state_eq_foldStatements
    (owner : Atom) (position : Nat) (state : SourceState)
    (statements : List RawStatement) :
    eraseFoldPayload
        (buildSourceAssertionCandidatesFrom owner position state statements) =
      eraseFoldPayload (foldStatements state statements) := by
  induction statements generalizing position state with
  | nil => rfl
  | cons statement statements ih =>
      simp only [buildSourceAssertionCandidatesFrom, foldStatements]
      cases applied : applyStatement state statement with
      | rejected rejection => rfl
      | ok pair =>
          obtain ⟨next, obligations⟩ := pair
          simp only
          have recursive := ih (position := position + 1) (state := next)
          cases planned :
              buildSourceAssertionCandidatesFrom owner (position + 1)
                next statements with
          | rejected planRejection =>
              simp only [planned, eraseFoldPayload] at recursive ⊢
              cases folded : foldStatements next statements with
              | rejected foldRejection =>
                  simp only [folded] at recursive ⊢
                  exact recursive
              | ok foldPair =>
                  simp only [folded] at recursive
                  contradiction
          | ok planPair =>
              obtain ⟨final, candidates⟩ := planPair
              simp only [planned, eraseFoldPayload] at recursive ⊢
              cases folded : foldStatements next statements with
              | rejected foldRejection =>
                  simp only [folded] at recursive
                  contradiction
              | ok foldPair =>
                  obtain ⟨foldFinal, restObligations⟩ := foldPair
                  simp only [folded, FoldResult.ok.injEq] at recursive ⊢
                  exact recursive

/-- Source-relative provenance of one retained candidate.  The witness names
the exact prefix state and accepted statement occurrence from which the
candidate was computed; it is stronger than final-state agreement. -/
def SourceAssertionCandidateFromSequence (startPosition : Nat)
    (initial : SourceState) (statements : List RawStatement)
    (candidate : SourceAssertionCandidate) : Prop :=
  exists beforeStatements statement afterStatements before next
      prefixObligations obligations,
    statements = beforeStatements ++ statement :: afterStatements ∧
      foldStatements initial beforeStatements =
        .ok (before, prefixObligations) ∧
      applyStatement before statement = .ok (next, obligations) ∧
      sourceAssertionCandidate?
          (startPosition + beforeStatements.length) before statement
            obligations =
        some candidate

/-- Prefixing one accepted source step transports a later candidate witness
without changing its represented occurrence. -/
theorem SourceAssertionCandidateFromSequence.cons
    {position : Nat} {state next : SourceState}
    {statement : RawStatement} {obligations : List TheoremObligation}
    {statements : List RawStatement}
    {candidate : SourceAssertionCandidate}
    (applied : applyStatement state statement = .ok (next, obligations))
    (derived :
      SourceAssertionCandidateFromSequence
        (position + 1) next statements candidate) :
    SourceAssertionCandidateFromSequence
      position state (statement :: statements) candidate := by
  obtain
    ⟨priorStatements, selected, laterStatements, before, after,
      prefixObligations, selectedObligations,
      statements_eq, prefixFold, selectedStep, candidate_eq⟩ := derived
  refine
    ⟨statement :: priorStatements, selected, laterStatements, before, after,
      obligations ++ prefixObligations, selectedObligations,
      ?_, ?_, selectedStep, ?_⟩
  · simpa only [List.cons_append] using
      congrArg (List.cons statement) statements_eq
  · simp only [foldStatements, applied, prefixFold]
  · rw [show position + (statement :: priorStatements).length =
      (position + 1) + priorStatements.length by
        simp only [List.length_cons]
        omega]
    exact candidate_eq

/-- Every candidate retained by the companion compiler has an exact accepted
source occurrence. -/
theorem buildSourceAssertionCandidatesFrom_candidate_source
    (owner : Atom) (position : Nat) (state : SourceState)
    (statements : List RawStatement) (final : SourceState)
    (candidates : List SourceAssertionCandidate)
    (built :
      buildSourceAssertionCandidatesFrom owner position state statements =
        .ok (final, candidates)) :
    forall candidate,
      candidate ∈ candidates ->
        SourceAssertionCandidateFromSequence
          position state statements candidate := by
  induction statements generalizing position state final candidates with
  | nil =>
      simp [buildSourceAssertionCandidatesFrom] at built
      obtain ⟨rfl, rfl⟩ := built
      simp
  | cons statement statements induction =>
      simp only [buildSourceAssertionCandidatesFrom] at built
      cases applied : applyStatement state statement with
      | rejected rejection => simp [applied] at built
      | ok pair =>
          obtain ⟨next, obligations⟩ := pair
          simp only [applied] at built
          cases recursive :
              buildSourceAssertionCandidatesFrom owner (position + 1)
                next statements with
          | rejected rejection => simp [recursive] at built
          | ok result =>
              obtain ⟨recursiveFinal, recursiveCandidates⟩ := result
              simp only [recursive] at built
              cases candidateStep :
                  sourceAssertionCandidate? position state statement
                    obligations with
              | none =>
                  simp only [candidateStep] at built
                  obtain ⟨rfl, rfl⟩ := FoldResult.ok.inj built
                  intro candidate member
                  exact SourceAssertionCandidateFromSequence.cons applied
                    (induction (position := position + 1) (state := next)
                      (final := final) (candidates := recursiveCandidates)
                      recursive candidate member)
              | some headCandidate =>
                  simp only [candidateStep] at built
                  obtain ⟨rfl, rfl⟩ := FoldResult.ok.inj built
                  intro candidate member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact
                      ⟨[], statement, statements, state, next, [], obligations,
                        by simp, by rfl, applied, by simpa using candidateStep⟩
                  · exact SourceAssertionCandidateFromSequence.cons applied
                      (induction (position := position + 1) (state := next)
                        (final := final) (candidates := recursiveCandidates)
                        recursive candidate member)

/-- Typed admission boundary for the assertion-candidate stream. -/
structure AdmittedSourceAssertionCandidates (owner : Atom)
    (statements : List RawStatement) where
  finalState : SourceState
  candidates : List SourceAssertionCandidate
  exact :
    buildSourceAssertionCandidates owner statements =
      .ok (finalState, candidates)

def admitSourceAssertionCandidates (owner : Atom)
    (statements : List RawStatement) :
    FoldResult (AdmittedSourceAssertionCandidates owner statements) :=
  match built : buildSourceAssertionCandidates owner statements with
  | .rejected rejection => .rejected rejection
  | .ok (finalState, candidates) =>
      .ok { finalState, candidates, exact := built }

def AdmittedSourceAssertionCandidates.rows {owner : Atom}
    {statements : List RawStatement}
    (input : AdmittedSourceAssertionCandidates owner statements) : List Atom :=
  input.candidates.map (sourceAssertionCandidateAtom owner)

@[simp] theorem AdmittedSourceAssertionCandidates.rows_all_proofNeutral
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceAssertionCandidates owner statements) :
    input.rows.all isProofNeutralInitialAtom = true := by
  simp [AdmittedSourceAssertionCandidates.rows]

theorem AdmittedSourceAssertionCandidates.finalState_eq_foldStatements
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceAssertionCandidates owner statements) :
    eraseFoldPayload (foldStatements initialState statements) =
      .ok input.finalState := by
  have agreement :=
    buildSourceAssertionCandidatesFrom_state_eq_foldStatements
      owner 0 initialState statements
  rw [show buildSourceAssertionCandidatesFrom owner 0 initialState statements =
      .ok (input.finalState, input.candidates) by
    simpa [buildSourceAssertionCandidates] using input.exact] at agreement
  exact agreement.symm

/-- The already admitted source-action plan determines the assertion-candidate
admission without another caller-supplied witness.  Both annotations replay the
same authored fold, so their final states must agree. -/
def admitSourceAssertionCandidatesFromActions
    {owner : Atom} {statements : List RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) :
    AdmittedSourceAssertionCandidates owner statements := by
  cases built : buildSourceAssertionCandidates owner statements with
  | rejected rejection =>
      have candidateAgreement :=
        buildSourceAssertionCandidatesFrom_state_eq_foldStatements
          owner 0 initialState statements
      have actionAgreement := actions.finalState_eq_foldStatements
      rw [show buildSourceAssertionCandidatesFrom owner 0 initialState
          statements = .rejected rejection by
        simpa [buildSourceAssertionCandidates] using built] at candidateAgreement
      have impossible :
          (FoldResult.rejected rejection : FoldResult SourceState) =
            .ok actions.finalState := by
        simpa only [eraseFoldPayload] using
          candidateAgreement.trans actionAgreement
      contradiction
  | ok result =>
      obtain ⟨candidateFinal, candidates⟩ := result
      have candidateAgreement :=
        buildSourceAssertionCandidatesFrom_state_eq_foldStatements
          owner 0 initialState statements
      have actionAgreement := actions.finalState_eq_foldStatements
      rw [show buildSourceAssertionCandidatesFrom owner 0 initialState
          statements = .ok (candidateFinal, candidates) by
        simpa [buildSourceAssertionCandidates] using built] at candidateAgreement
      have finalStates :
          (FoldResult.ok candidateFinal : FoldResult SourceState) =
            .ok actions.finalState := by
        simpa only [eraseFoldPayload] using
          candidateAgreement.trans actionAgreement
      have finalState_eq : candidateFinal = actions.finalState :=
        FoldResult.ok.inj finalStates
      subst candidateFinal
      exact
        { finalState := actions.finalState
          candidates
          exact := by simpa [buildSourceAssertionCandidates] using built }

/-! ## Focused positive and negative controls -/

private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "assertion-plan.mm", start, stop }

private def fixtureName (name : String) (start stop : Nat) : LocatedName :=
  { span := fixtureSpan start stop, name }

private def fixtureStatement : RawStatement :=
  .axiomatic (fixtureSpan 0 2) (fixtureName "ax" 3 5)
    (fixtureName "wff" 6 9) [] (fixtureSpan 10 12)

private def fixtureCandidate : SourceAssertionCandidate :=
  { position := 0
    nextPosition := 1
    statement := fixtureStatement
    assertionPosition := 0
    nextAssertionPosition := 1
    gate := .immediate
    mandatoryVariables := []
    assertion :=
      sourceAssertion SourceStateGSLT.oneConstantState "ax"
        { typecode := "wff", body := [] } }

theorem fixture_axiom_applies :
    applyStatement SourceStateGSLT.oneConstantState fixtureStatement =
      .ok
        ({ SourceStateGSLT.oneConstantState with
            usedLabels := ["ax"]
            assertions := [fixtureCandidate.assertion] }, []) := by
  decide

theorem fixture_axiom_candidate_exact :
    sourceAssertionCandidate? 0 SourceStateGSLT.oneConstantState
        fixtureStatement [] =
      some fixtureCandidate := by
  decide

theorem nonassertion_has_no_candidate :
    sourceAssertionCandidate? 0 initialState
        (.openScope (fixtureSpan 0 2)) [] = none := by
  rfl

private def forgedMandatoryVariablesCandidate : SourceAssertionCandidate :=
  { fixtureCandidate with mandatoryVariables := ["ghost"] }

/-- A canonical representation can carry a fabricated mandatory-variable
certificate.  Successful decoding therefore remains representation validation,
not source-relative authorization. -/
theorem forged_mandatory_variables_decode_but_are_not_source_derived :
    decodeSourceAssertionCandidateAtom (.symbol "candidate-owner")
        (sourceAssertionCandidateAtom (.symbol "candidate-owner")
          forgedMandatoryVariablesCandidate) =
      some forgedMandatoryVariablesCandidate ∧
    sourceAssertionCandidate? 0 SourceStateGSLT.oneConstantState
        fixtureStatement [] ≠
      some forgedMandatoryVariablesCandidate := by
  constructor
  · exact decodeSourceAssertionCandidateAtom_encoded _ _
  · rw [fixture_axiom_candidate_exact]
    intro equal
    have candidate_eq := Option.some.inj equal
    have variables_eq :=
      congrArg SourceAssertionCandidate.mandatoryVariables candidate_eq
    simp [fixtureCandidate, forgedMandatoryVariablesCandidate] at variables_eq

#print axioms axiomDeclaration_inhabits_source_native_type
#print axioms decodeSourceAssertionCandidateAtom_encoded
#print axioms sourceAssertionCandidateAtom_injective
#print axioms sourceAssertionCandidateAtom_proofNeutral
#print axioms sourceAssertionCandidate?_statement_is_assertion
#print axioms sourceAssertionCandidate?_position_exact
#print axioms buildSourceAssertionCandidatesFrom_state_eq_foldStatements
#print axioms buildSourceAssertionCandidatesFrom_candidate_source
#print axioms AdmittedSourceAssertionCandidates.rows_all_proofNeutral
#print axioms AdmittedSourceAssertionCandidates.finalState_eq_foldStatements
#print axioms admitSourceAssertionCandidatesFromActions
#print axioms fixture_axiom_applies
#print axioms fixture_axiom_candidate_exact
#print axioms nonassertion_has_no_candidate
#print axioms forged_mandatory_variables_decode_but_are_not_source_derived

end Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
