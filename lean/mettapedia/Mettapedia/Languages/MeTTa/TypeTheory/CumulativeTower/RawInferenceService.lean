import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension

/-!
# Unqualified inference data and exact-request admission

Requests, candidate articles, and replies are ordinary data. A reply carries
no derivation or proof of its verdict. The selected validated calculus is an
external service parameter, never a rule table supplied by the candidate.
Its scope records the selected authority and revision; these identifiers do
not authenticate an untrusted caller or justify an environment change.

The producer executes the existing closed-payload checker. Admission checks
the complete expected request and rechecks the candidate, so copying an
acceptance tag cannot create a theorem. Malformed input, a scope mismatch,
and rejection of one candidate remain distinct; none asserts that the goal
is false. The reconstruction theorem retains the identical raw proof and
uses the independently selected calculus semantics for its meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace RawInferenceService

universe u

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceLanguageWire
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension

abbrev Wire := Mettapedia.GSLT.LanguageDef.CettaWire.Term

mutual
  def wireEqual : Wire → Wire → Bool
    | .symbol a, .symbol b => a == b
    | .string a, .string b => a == b
    | .natural a, .natural b => a == b
    | .application a xs, .application b ys => a == b && wiresEqual xs ys
    | _, _ => false
  def wiresEqual : List Wire → List Wire → Bool
    | [], [] => true
    | x :: xs, y :: ys => wireEqual x y && wiresEqual xs ys
    | _, _ => false
end

mutual
  theorem wireEqual_iff (left right : Wire) : wireEqual left right = true ↔ left = right := by
    match left, right with
    | .symbol a, .symbol b => simp [wireEqual]
    | .string a, .string b => simp [wireEqual]
    | .natural a, .natural b => simp [wireEqual]
    | .application a xs, .application b ys =>
        simp only [wireEqual, Bool.and_eq_true, beq_iff_eq, wiresEqual_iff xs ys]
        constructor
        · rintro ⟨rfl, rfl⟩; rfl
        · intro equal; cases equal; exact ⟨rfl, rfl⟩
    | .symbol _, .string _ | .symbol _, .natural _ | .symbol _, .application _ _
    | .string _, .symbol _ | .string _, .natural _ | .string _, .application _ _
    | .natural _, .symbol _ | .natural _, .string _ | .natural _, .application _ _
    | .application _ _, .symbol _ | .application _ _, .string _
    | .application _ _, .natural _ => simp [wireEqual]
  termination_by structural left

  theorem wiresEqual_iff (left right : List Wire) : wiresEqual left right = true ↔ left = right := by
    match left, right with
    | [], [] => simp [wiresEqual]
    | _ :: _, [] | [], _ :: _ => simp [wiresEqual]
    | x :: xs, y :: ys =>
        simp only [wiresEqual, Bool.and_eq_true, wireEqual_iff x y, wiresEqual_iff xs ys,
          List.cons.injEq]
  termination_by structural left
end

instance wireDecidableEq : DecidableEq Wire := fun left right =>
  decidable_of_iff (wireEqual left right = true) (wireEqual_iff left right)

structure Scope where
  authority : Nat
  revision : Nat
  deriving DecidableEq, Repr

structure Request where
  scope : Scope
  goal : Wire
  deriving DecidableEq, Repr

structure Candidate where
  request : Request
  article : Wire
  deriving DecidableEq, Repr

inductive Verdict where
  | scopeMismatch
  | malformed
  | checked (accepted : Bool)
  deriving DecidableEq, Repr

structure Reply where
  candidate : Candidate
  verdict : Verdict
  deriving DecidableEq, Repr

def encodeRequest (request : Request) : Wire :=
  .application "PrimeInferenceRequest"
    [.natural request.scope.authority, .natural request.scope.revision, request.goal]

def decodeRequest : Wire → Option Request
  | .application "PrimeInferenceRequest" [.natural authority, .natural revision, goal] =>
      some ⟨⟨authority, revision⟩, goal⟩
  | _ => none

def encodeCandidate (candidate : Candidate) : Wire :=
  .application "PrimeInferenceCandidate" [encodeRequest candidate.request, candidate.article]

def decodeCandidate : Wire → Option Candidate
  | .application "PrimeInferenceCandidate" [request, article] => do
      return ⟨← decodeRequest request, article⟩
  | _ => none

def encodeVerdict : Verdict → Wire
  | .scopeMismatch => .symbol "PrimeInferenceScopeMismatch"
  | .malformed => .symbol "PrimeInferenceMalformed"
  | .checked false => .symbol "PrimeInferenceCandidateRejected"
  | .checked true => .symbol "PrimeInferenceCandidateAccepted"

def decodeVerdict : Wire → Option Verdict
  | .symbol "PrimeInferenceScopeMismatch" => some .scopeMismatch
  | .symbol "PrimeInferenceMalformed" => some .malformed
  | .symbol "PrimeInferenceCandidateRejected" => some (.checked false)
  | .symbol "PrimeInferenceCandidateAccepted" => some (.checked true)
  | _ => none

def encodeReply (reply : Reply) : Wire :=
  .application "PrimeInferenceReply" [encodeCandidate reply.candidate, encodeVerdict reply.verdict]

def decodeReply : Wire → Option Reply
  | .application "PrimeInferenceReply" [candidate, verdict] => do
      return ⟨← decodeCandidate candidate, ← decodeVerdict verdict⟩
  | _ => none

@[simp] theorem decode_encode_request (request : Request) :
    decodeRequest (encodeRequest request) = some request := by cases request; rfl

@[simp] theorem decode_encode_candidate (candidate : Candidate) :
    decodeCandidate (encodeCandidate candidate) = some candidate := by
  cases candidate
  simp [encodeCandidate, decodeCandidate]

@[simp] theorem decode_encode_verdict (verdict : Verdict) :
    decodeVerdict (encodeVerdict verdict) = some verdict := by
  cases verdict with
  | checked accepted => cases accepted <;> rfl
  | _ => rfl

@[simp] theorem decode_encode_reply (reply : Reply) :
    decodeReply (encodeReply reply) = some reply := by
  cases reply
  simp [encodeReply, decodeReply]

/-- The actual checker is fixed by the selected validated definition. -/
def check (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (candidate : Candidate) : Verdict :=
  if candidate.request.scope = scope then
    match decodePattern candidate.request.goal, decodeRawProof candidate.article with
    | some goal, some article =>
        .checked ((RuntimeInferenceLanguage.ofDefinition definition.1).checkRaw goal article)
    | _, _ => .malformed
  else .scopeMismatch

def evaluate (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (candidate : Candidate) : Reply := ⟨candidate, check definition scope candidate⟩

/-- Even a well-shaped raw reply is untrusted until this check succeeds. -/
def validate (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (reply : Reply) : Bool :=
  decide (reply.candidate.request = expected) &&
    decide (reply.verdict = .checked true) &&
    decide (check definition scope reply.candidate = .checked true)

def evaluateWire (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (input : Wire) : Option Wire := do
  return encodeReply (evaluate definition scope (← decodeCandidate input))

def validateWire (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (input : Wire) : Option Bool := do
  match input with
  | .application "PrimeInferenceAdmission" [expected, reply] =>
      return validate definition scope (← decodeRequest expected) (← decodeReply reply)
  | _ => none

@[simp] theorem evaluateWire_encode (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (candidate : Candidate) :
    evaluateWire definition scope (encodeCandidate candidate) =
      some (encodeReply (evaluate definition scope candidate)) := by
  simp [evaluateWire]

@[simp] theorem validateWire_encode (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (expected : Request) (reply : Reply) :
    validateWire definition scope
      (.application "PrimeInferenceAdmission" [encodeRequest expected, encodeReply reply]) =
      some (validate definition scope expected reply) := by
  simp [validateWire]

theorem check_accepted_iff (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (candidate : Candidate) :
    check definition scope candidate = .checked true ↔
      candidate.request.scope = scope ∧ ∃ goal article,
        decodePattern candidate.request.goal = some goal ∧
        decodeRawProof candidate.article = some article ∧
        (RuntimeInferenceLanguage.ofDefinition definition.1).checkRaw goal article = true := by
  unfold check
  by_cases current : candidate.request.scope = scope
  · simp only [current, if_true, true_and]
    cases goal : decodePattern candidate.request.goal <;>
      cases article : decodeRawProof candidate.article <;> simp
  · simp [current]

theorem validate_iff (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (reply : Reply) :
    validate definition scope expected reply = true ↔
      reply.candidate.request = expected ∧ reply.verdict = .checked true ∧
        check definition scope reply.candidate = .checked true := by
  simp only [validate, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem validate_evaluated (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (candidate : Candidate) :
    validate definition scope candidate.request (evaluate definition scope candidate) = true ↔
      check definition scope candidate = .checked true := by
  simp [validate_iff, evaluate]

def canonicalCandidate (scope : Scope) (goal : Pattern) (article : RawProof) : Candidate :=
  ⟨⟨scope, encodePattern goal⟩, encodeRawProof article⟩

@[simp] theorem check_canonical (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (goal : Pattern) (article : RawProof) :
    check definition scope (canonicalCandidate scope goal article) =
      .checked ((RuntimeInferenceLanguage.ofDefinition definition.1).checkRaw goal article) := by
  simp [check, canonicalCandidate]

/-- Completeness is precisely the existing closed-constructor payload
profile, not an unrestricted completeness claim for arbitrary raw articles. -/
theorem validate_canonical_iff (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (goal : Pattern) (article : RawProof)
    (payloads : (RuntimeInferenceLanguage.ofDefinition definition.1).proofPayloadsValid
      article = true) :
    validate definition scope (canonicalCandidate scope goal article).request
      (evaluate definition scope (canonicalCandidate scope goal article)) = true ↔
      ∃ derivation : Derivation definition goal, derivation.erase = article := by
  rw [validate_evaluated, check_canonical]
  constructor
  · intro accepted
    exact G2_checkRaw_iff_exists_derivation_erases_to.mp
      (RuntimeInferenceLanguage.checkRaw_sound definition goal article (Verdict.checked.inj accepted))
  · rintro ⟨derivation, erases⟩
    have accepted := RuntimeInferenceLanguage.checkRaw_complete definition goal article
      (G2_checkRaw_iff_exists_derivation_erases_to.mpr ⟨derivation, erases⟩) payloads
    rw [accepted]

/-- A successful raw reply reconstructs exactly the submitted article, under
the selected definition and the consumer's complete expected request. -/
theorem validate_sound (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (reply : Reply)
    (accepted : validate definition scope expected reply = true) :
    expected.scope = scope ∧ ∃ goal article,
      decodePattern expected.goal = some goal ∧
      decodeRawProof reply.candidate.article = some article ∧
      ∃ derivation : Derivation definition goal, derivation.erase = article := by
  obtain ⟨same, _, checked⟩ := (validate_iff definition scope expected reply).mp accepted
  obtain ⟨current, goal, article, goalDecoded, articleDecoded, runtimeAccepted⟩ :=
    (check_accepted_iff definition scope reply.candidate).mp checked
  rw [same] at current goalDecoded
  exact ⟨current, goal, article, goalDecoded, articleDecoded,
    G2_checkRaw_iff_exists_derivation_erases_to.mp
      (RuntimeInferenceLanguage.checkRaw_sound definition goal article runtimeAccepted)⟩

/-- Independent rule meanings interpret the reconstructed article. Merely
declaring or encoding a meaning does not discharge this semantic premise. -/
theorem validate_meaning (definition : ValidatedCalculusLanguageDef)
    {Meaning : Pattern → Type u} (semantics : CalculusLanguageSemantics definition Meaning)
    (scope : Scope) (expected : Request) (reply : Reply)
    (accepted : validate definition scope expected reply = true) :
    ∃ goal article, decodePattern expected.goal = some goal ∧
      decodeRawProof reply.candidate.article = some article ∧
      ∃ derivation : Derivation definition goal,
        derivation.erase = article ∧ Nonempty (Meaning goal) := by
  obtain ⟨_, goal, article, decodedGoal, decodedArticle, derivation, erases⟩ :=
    validate_sound definition scope expected reply accepted
  exact ⟨goal, article, decodedGoal, decodedArticle, derivation, erases,
    ⟨semantics.interpret derivation⟩⟩

theorem wrong_request_rejected (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (reply : Reply) (different : reply.candidate.request ≠ expected) :
    validate definition scope expected reply = false := by simp [validate, different]

theorem stale_scope_rejected (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (reply : Reply) (stale : expected.scope ≠ scope) :
    validate definition scope expected reply = false := by
  cases result : validate definition scope expected reply with
  | false => rfl
  | true => exact False.elim (stale (validate_sound definition scope expected reply result).1)

theorem forged_acceptance_rejected (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (candidate : Candidate) (rejected : check definition scope candidate ≠ .checked true) :
    validate definition scope candidate.request ⟨candidate, .checked true⟩ = false := by
  simp [validate, rejected]

#print axioms check_accepted_iff
#print axioms wireEqual_iff
#print axioms validate_canonical_iff
#print axioms validate_sound
#print axioms validate_meaning
#print axioms stale_scope_rejected
#print axioms forged_acceptance_rejected

end RawInferenceService
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
