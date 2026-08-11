import Mettapedia.GSLT.Dynamics.EventValuation
import Mettapedia.GSLT.Dynamics.OperatorRealization
import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

/-!
# Parallel execution articles as a NIK authority

This module connects three independently useful boundaries:

* query-relative commutation and resource compatibility of revision events;
* revision-bound operator plans, deltas, and execution receipts;
* the open, fail-closed NIK authority family.

A backend admission predicate is semantic policy, not executable evidence by
itself.  `AdmissionAuthority` therefore requires a two-sided checker for the
backend's exact admitted subset.  The combined checker additionally replays
the backend-neutral operator receipt and checks that it names the same query
as the semantic event claim.

The exact certificate scope is deliberately narrower than semantic
parallelizability.  A conservative backend may serialize a semantically
commuting pair.  Consequently the combined checker is an exact authority for
`Certified`, and only an authority projection into `Meaning`.
-/

namespace Mettapedia.GSLT.Dynamics.ParallelExecutionAuthority

open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.Dynamics.EventValuation
open Mettapedia.GSLT.Dynamics.OperatorRealization
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

set_option autoImplicit false

universe uWorld uRevision uQuery uObservation uGrade
universe uCertificate
universe uKind uClaim uGuestCertificate

/-! ## Semantic event claims and executable backend admission -/

/-- The semantic part of a parallel execution request.  The query is named
explicitly: two event orders need only agree at observations claimed by the
article. -/
structure EventClaim (theory : Theory) where
  first : theory.Revision
  second : theory.Revision
  source : theory.World
  request : theory.Query

/-- The exact subset selected by one backend's parallel planner. -/
def Admitted {theory : Theory} (backend : ParallelBackend theory)
    (claim : EventClaim theory) : Prop :=
  backend.Admits claim.first claim.second claim.source

/-- Observer-relative commutation for the single query named by an article. -/
def SelectedObservationPreserved {theory : Theory}
    (claim : EventClaim theory) : Prop :=
  Nonempty (theory.ObservedSquare claim.first claim.second claim.source
    (fun world => theory.query world claim.request))

/-- Complete-query-profile commutation implies commutation at every selected
query. -/
theorem selectedObservationPreserved_of_queryCoexecutible
    {theory : Theory} (claim : EventClaim theory)
    (coexecutible :
      theory.QueryCoexecutible claim.first claim.second claim.source) :
    SelectedObservationPreserved claim := by
  rcases coexecutible with ⟨square⟩
  refine ⟨{
    afterFirst := square.afterFirst
    afterSecond := square.afterSecond
    firstThenSecond := square.firstThenSecond
    secondThenFirst := square.secondThenFirst
    firstFromSource := square.firstFromSource
    secondFromSource := square.secondFromSource
    secondAfterFirst := square.secondAfterFirst
    firstAfterSecond := square.firstAfterSecond
    observationAgrees := congrFun square.observationAgrees claim.request }⟩

/-- An independently replayable checker for a backend's exact admission
predicate.  This is the backend-specific input to the generic NIK article;
the generic checker never guesses admission from a scheduler decision. -/
structure AdmissionAuthority {theory : Theory}
    (backend : ParallelBackend theory) where
  Certificate : Type uCertificate
  checker : Checker (EventClaim theory) Certificate
  authority : checker.Authority (Admitted backend)

namespace AdmissionAuthority

variable {theory : Theory} {backend : ParallelBackend theory}
    (admission : AdmissionAuthority.{uCertificate} backend)

/-- Exact backend admission projects to observer-relative commutation and
resource compatibility by the backend's declared soundness law. -/
def projection : admission.checker.AuthorityProjection
    (Admitted backend)
    (fun claim =>
      SelectedObservationPreserved claim ∧
        backend.valuation.Compatible claim.first claim.second) where
  authority := admission.authority
  project := by
    intro claim admitted
    have parallelizable := backend.sound admitted
    exact
      ⟨selectedObservationPreserved_of_queryCoexecutible claim
          parallelizable.1,
        parallelizable.2⟩

end AdmissionAuthority

/-! ## One combined semantic/physical claim -/

/-- The complete public claim checked by a parallel execution article.

The semantic world and the physical store snapshot are intentionally
different fields.  Their connection is the compiled plan and its named
observer, rather than an assertion that every semantic world must use one
physical representation. -/
structure Claim
    (theory : Theory)
    (Backend StoreRevision Payload PlanId DeltaId : Type) where
  event : EventClaim theory
  snapshot : Snapshot Backend StoreRevision Payload
  plan : OperatorPlan Backend StoreRevision theory.Query PlanId
  delta : Delta Backend StoreRevision Payload DeltaId
  receipt : Receipt Backend StoreRevision theory.Query PlanId DeltaId

namespace Claim

variable {theory : Theory}
    {Backend StoreRevision Payload PlanId DeltaId : Type}

/-- The backend-neutral executable obligations carried by a parallel claim. -/
def coreCheck [DecidableEq Backend] [DecidableEq StoreRevision]
    [DecidableEq theory.Query] [DecidableEq PlanId] [DecidableEq DeltaId]
    (claim : Claim theory Backend StoreRevision Payload PlanId DeltaId) : Bool :=
  accepts true claim.snapshot claim.plan claim.delta claim.receipt &&
    decide (claim.plan.observer = claim.event.request) &&
    decide (claim.receipt.mode = .parallel)

/-- The proposition exactly reflected by `coreCheck`. -/
def CoreAccepted [DecidableEq Backend] [DecidableEq StoreRevision]
    [DecidableEq theory.Query] [DecidableEq PlanId] [DecidableEq DeltaId]
    (claim : Claim theory Backend StoreRevision Payload PlanId DeltaId) : Prop :=
  accepts true claim.snapshot claim.plan claim.delta claim.receipt = true ∧
    claim.plan.observer = claim.event.request ∧
    claim.receipt.mode = .parallel

theorem coreCheck_eq_true_iff [DecidableEq Backend]
    [DecidableEq StoreRevision] [DecidableEq theory.Query]
    [DecidableEq PlanId] [DecidableEq DeltaId]
    (claim : Claim theory Backend StoreRevision Payload PlanId DeltaId) :
    claim.coreCheck = true ↔ claim.CoreAccepted := by
  simp [coreCheck, CoreAccepted, and_assoc]

end Claim

section CombinedChecker

variable {theory : Theory}
    {Backend StoreRevision Payload PlanId DeltaId : Type}
    [DecidableEq Backend] [DecidableEq StoreRevision]
    [DecidableEq theory.Query] [DecidableEq PlanId] [DecidableEq DeltaId]
    {backend : ParallelBackend.{uGrade} theory}

/-- Exact certificate scope: this backend admitted the event pair and the
physical article passed every core receipt and binding check. -/
def Certified
    (claim : Claim theory Backend StoreRevision Payload PlanId DeltaId) : Prop :=
  Admitted backend claim.event ∧ claim.CoreAccepted

/-- Projected semantic meaning of an accepted parallel execution article.
It explicitly names the selected observation and retains the independent
resource-compatibility and physical-receipt obligations. -/
def Meaning
    (claim : Claim theory Backend StoreRevision Payload PlanId DeltaId) : Prop :=
  SelectedObservationPreserved claim.event ∧
    backend.valuation.Compatible claim.event.first claim.event.second ∧
    claim.CoreAccepted

/-- Replay backend admission and backend-neutral receipt evidence together. -/
def replayChecker
    (admission : AdmissionAuthority.{uCertificate} backend) :
    Checker (Claim theory Backend StoreRevision Payload PlanId DeltaId)
      admission.Certificate where
  check := fun claim certificate =>
    admission.checker.check claim.event certificate && claim.coreCheck

theorem replayChecker_soundCertified
    (admission : AdmissionAuthority.{uCertificate} backend) :
    (replayChecker admission).Sound
      (Certified (theory := theory) (Backend := Backend)
        (StoreRevision := StoreRevision) (Payload := Payload)
        (PlanId := PlanId) (DeltaId := DeltaId) (backend := backend)) := by
  intro claim certificate accepted
  have parts :
      admission.checker.check claim.event certificate = true ∧
        claim.coreCheck = true := by
    simpa [replayChecker] using accepted
  exact
    ⟨admission.authority.sound claim.event certificate parts.1,
      (claim.coreCheck_eq_true_iff).mp parts.2⟩

theorem replayChecker_completeCertified
    (admission : AdmissionAuthority.{uCertificate} backend) :
    (replayChecker admission).CertificateComplete
      (Certified (theory := theory) (Backend := Backend)
        (StoreRevision := StoreRevision) (Payload := Payload)
        (PlanId := PlanId) (DeltaId := DeltaId) (backend := backend)) := by
  intro claim certified
  obtain ⟨certificate, accepted⟩ :=
    admission.authority.complete claim.event certified.1
  exact ⟨certificate, by
    simp [replayChecker, accepted,
      (claim.coreCheck_eq_true_iff).2 certified.2]⟩

/-- Combined replay is exact for the backend-admitted article scope. -/
theorem replayChecker_authority
    (admission : AdmissionAuthority.{uCertificate} backend) :
    (replayChecker admission).Authority
      (Certified (theory := theory) (Backend := Backend)
        (StoreRevision := StoreRevision) (Payload := Payload)
        (PlanId := PlanId) (DeltaId := DeltaId) (backend := backend)) where
  sound := replayChecker_soundCertified admission
  complete := replayChecker_completeCertified admission

/-- Backend admission plus core replay projects to named-observation
preservation, compatible valuation, and exact receipt binding. -/
theorem certified_implies_meaning
    (admission : AdmissionAuthority.{uCertificate} backend)
    (claim : Claim theory Backend StoreRevision Payload PlanId DeltaId) :
    Certified (backend := backend) claim → Meaning (backend := backend) claim := by
  intro certified
  have semantic := (admission.projection).project claim.event certified.1
  exact ⟨semantic.1, semantic.2, certified.2⟩

/-- The combined checker is an exact authority for admitted articles and a
sound projection into their observer-relative semantics. -/
def authorityProjection
    (admission : AdmissionAuthority.{uCertificate} backend) :
    (replayChecker admission).AuthorityProjection
      (Certified (theory := theory) (Backend := Backend)
        (StoreRevision := StoreRevision) (Payload := Payload)
        (PlanId := PlanId) (DeltaId := DeltaId) (backend := backend))
      (Meaning (theory := theory) (Backend := Backend)
        (StoreRevision := StoreRevision) (Payload := Payload)
        (PlanId := PlanId) (DeltaId := DeltaId) (backend := backend)) where
  authority := replayChecker_authority admission
  project := certified_implies_meaning admission

/-- The selected endpoints carried by the semantic square have equal results
for the query named by the physical operator plan. -/
theorem meaning_preserves_plan_observation
    {claim : Claim theory Backend StoreRevision Payload PlanId DeltaId}
    (meaning : Meaning (backend := backend) claim) :
    ∃ square : theory.ObservedSquare claim.event.first claim.event.second
        claim.event.source
        (fun world => theory.query world claim.event.request),
      theory.query square.firstThenSecond claim.plan.observer =
        theory.query square.secondThenFirst claim.plan.observer := by
  rcases meaning.1 with ⟨square⟩
  refine ⟨square, ?_⟩
  have observerBound : claim.plan.observer = claim.event.request :=
    meaning.2.2.2.1
  simpa [observerBound] using square.observationAgrees

/-- Accepted articles retain the exact authored occurrence order and
multiplicity checked by the core realization contract. -/
theorem meaning_preserves_authored_occurrences
    {claim : Claim theory Backend StoreRevision Payload PlanId DeltaId}
    (meaning : Meaning (backend := backend) claim) :
    claim.receipt.authoredOccurrences = claim.plan.authoredOccurrences :=
  accepted_authored_order meaning.2.2.1

/-! ## Admission into the open NIK family -/

/-- Parallel execution replay as one ordinary NIK authority fibre. -/
def family (admission : AdmissionAuthority.{uCertificate} backend) :
    AuthorityFamily Unit where
  Claim := fun _ => Claim theory Backend StoreRevision Payload PlanId DeltaId
  Certificate := fun _ => admission.Certificate
  checker := fun _ => replayChecker admission
  Certified := fun _ =>
    Certified (theory := theory) (Backend := Backend)
      (StoreRevision := StoreRevision) (Payload := Payload)
      (PlanId := PlanId) (DeltaId := DeltaId) (backend := backend)
  Meaning := fun _ =>
    Meaning (theory := theory) (Backend := Backend)
      (StoreRevision := StoreRevision) (Payload := Payload)
      (PlanId := PlanId) (DeltaId := DeltaId) (backend := backend)
  projection := fun _ => authorityProjection admission

/-- Add parallel execution articles to any existing guest authority family
without adding a privileged branch to the NIK evaluator. -/
def withParallelExecution
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uGuestCertificate} Kind)
    (admission : AdmissionAuthority.{uCertificate} backend) :=
  AuthorityFamily.sum guest
    (family (theory := theory) (Backend := Backend)
      (StoreRevision := StoreRevision) (Payload := Payload)
      (PlanId := PlanId) (DeltaId := DeltaId) admission)

/-- The typed semantic frontend used before choosing a concrete wire codec. -/
def typedFrontend (admission : AdmissionAuthority.{uCertificate} backend) :=
  Frontend.typed
    (family (theory := theory) (Backend := Backend)
      (StoreRevision := StoreRevision) (Payload := Payload)
      (PlanId := PlanId) (DeltaId := DeltaId) admission)

/-- Package one parallel article for the ordinary NIK frontend. -/
def submission (admission : AdmissionAuthority.{uCertificate} backend)
    (claim : Claim theory Backend StoreRevision Payload PlanId DeltaId)
    (certificate : admission.Certificate) :
    TypedSubmission
      (family (theory := theory) (Backend := Backend)
        (StoreRevision := StoreRevision) (Payload := Payload)
        (PlanId := PlanId) (DeltaId := DeltaId) admission) :=
  ⟨(), claim, certificate⟩

/-- An accepted parallel article is processed by the ordinary statusful NIK
frontend, not by a concurrency-specific evaluator. -/
theorem accepted_defaultRun
    (admission : AdmissionAuthority.{uCertificate} backend)
    (claim : Claim theory Backend StoreRevision Payload PlanId DeltaId)
    (certificate : admission.Certificate)
    (accepted : (replayChecker admission).check claim certificate = true) :
    (typedFrontend (theory := theory) (Backend := Backend)
        (StoreRevision := StoreRevision) (Payload := Payload)
        (PlanId := PlanId) (DeltaId := DeltaId) admission).run
        ((typedFrontend (theory := theory) (Backend := Backend)
          (StoreRevision := StoreRevision) (Payload := Payload)
          (PlanId := PlanId) (DeltaId := DeltaId) admission).encode
          (submission (theory := theory) (Backend := Backend)
            (StoreRevision := StoreRevision) (Payload := Payload)
            (PlanId := PlanId) (DeltaId := DeltaId)
            admission claim certificate)) =
      SubmissionOutcome.accepted (TypedSubmission.claim
        (submission (theory := theory) (Backend := Backend)
          (StoreRevision := StoreRevision) (Payload := Payload)
          (PlanId := PlanId) (DeltaId := DeltaId)
          admission claim certificate)) := by
  simpa [typedFrontend, family, submission, accepted] using
    (typedFrontend (theory := theory) (Backend := Backend)
      (StoreRevision := StoreRevision) (Payload := Payload)
      (PlanId := PlanId) (DeltaId := DeltaId) admission).run_encode
      (submission (theory := theory) (Backend := Backend)
        (StoreRevision := StoreRevision) (Payload := Payload)
        (PlanId := PlanId) (DeltaId := DeltaId)
        admission claim certificate)

end CombinedChecker

/-! ## Positive and negative executable witnesses -/

namespace Canary

open Mettapedia.GSLT.Dynamics.EventValuation.Canary

private instance : DecidableEq noOpTheory.Revision :=
  inferInstanceAs (DecidableEq Bool)

private instance : DecidableEq noOpTheory.Query :=
  inferInstanceAs (DecidableEq Unit)

/-- Exact executable admission for the conservative same-class backend. -/
def sameClassAdmission : AdmissionAuthority sameClassBackend where
  Certificate := Unit
  checker :=
    { check := fun claim _ => decide (claim.first = claim.second) }
  authority := by
    constructor
    · intro claim _ accepted
      simpa [Admitted, sameClassBackend] using accepted
    · intro claim admitted
      exact ⟨(), by simpa [Admitted, sameClassBackend] using admitted⟩

abbrev Backend := OperatorRealization.Example.Backend
abbrev StoreRevision := OperatorRealization.Example.Revision
abbrev Payload := OperatorRealization.Example.Payload
abbrev PlanId := OperatorRealization.Example.PlanId
abbrev DeltaId := OperatorRealization.Example.DeltaId

def plan : OperatorPlan Backend StoreRevision Unit PlanId where
  id := OperatorRealization.Example.plan.id
  observer := ()
  sourceBackend := OperatorRealization.Example.plan.sourceBackend
  targetBackend := OperatorRealization.Example.plan.targetBackend
  sourceRevision := OperatorRealization.Example.plan.sourceRevision
  authoredOccurrences :=
    OperatorRealization.Example.plan.authoredOccurrences

def receipt : Receipt Backend StoreRevision Unit PlanId DeltaId where
  planId := OperatorRealization.Example.receipt.planId
  observer := ()
  sourceBackend := OperatorRealization.Example.receipt.sourceBackend
  targetBackend := OperatorRealization.Example.receipt.targetBackend
  sourceRevision := OperatorRealization.Example.receipt.sourceRevision
  targetRevision := OperatorRealization.Example.receipt.targetRevision
  deltaId := OperatorRealization.Example.receipt.deltaId
  mode := .parallel
  authoredOccurrences :=
    OperatorRealization.Example.receipt.authoredOccurrences
  emittedOccurrences :=
    OperatorRealization.Example.receipt.emittedOccurrences

def positiveClaim :
    Claim noOpTheory Backend StoreRevision Payload PlanId DeltaId where
  event := ⟨true, true, (), ()⟩
  snapshot := OperatorRealization.Example.snapshot
  plan := plan
  delta := OperatorRealization.Example.delta
  receipt := receipt

/-- Positive witness: semantic admission, named observation, valuation, and
the revision-bound physical receipt all replay together. -/
theorem positive_article_accepted :
    (replayChecker sameClassAdmission).check positiveClaim () = true := by
  decide

theorem positive_article_meaning :
    Meaning (backend := sameClassBackend) positiveClaim := by
  exact (authorityProjection sameClassAdmission).sound
    positiveClaim () positive_article_accepted

def conservativeClaim :
    Claim noOpTheory Backend StoreRevision Payload PlanId DeltaId :=
  { positiveClaim with event := ⟨true, false, (), ()⟩ }

/-- Negative authority witness: the backend rejects a semantically commuting,
resource-compatible pair that it elects to serialize. -/
theorem conservative_article_rejected :
    (replayChecker sameClassAdmission).check conservativeClaim () = false := by
  decide

/-- The rejected pair still has the projected language meaning.  Hence exact
backend admission must not be mislabeled as semantic completeness. -/
theorem conservative_claim_is_meaningful :
    Meaning (backend := sameClassBackend) conservativeClaim := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨(noOpSquare true false).toObservedValue
      (fun world => noOpTheory.query world ())⟩
  · exact additive_compatible (theory := noOpTheory) (Grade := Nat)
      (fun _ => 1) true false
  · exact (Claim.coreCheck_eq_true_iff conservativeClaim).mp (by decide)

theorem conservative_claim_not_certified :
    ¬ Certified (backend := sameClassBackend) conservativeClaim := by
  intro certified
  have impossible : (true : Bool) = false := by
    simpa [Admitted, sameClassBackend, conservativeClaim] using certified.1
  cases impossible

def staleClaim :
    Claim noOpTheory Backend StoreRevision Payload PlanId DeltaId :=
  { positiveClaim with
    receipt := { receipt with sourceRevision := 6 } }

/-- Negative physical witness: semantic admission cannot launder a stale
receipt through the combined checker. -/
theorem stale_article_rejected :
    (replayChecker sameClassAdmission).check staleClaim () = false := by
  decide

/-- The accepted article genuinely enters the default statusful NIK. -/
theorem positive_article_defaultNIK_accepts :
    (typedFrontend sameClassAdmission).run
        ((typedFrontend sameClassAdmission).encode
          (submission sameClassAdmission positiveClaim ())) =
      SubmissionOutcome.accepted (TypedSubmission.claim
        (submission sameClassAdmission positiveClaim ())) :=
  accepted_defaultRun sameClassAdmission positiveClaim ()
    positive_article_accepted

end Canary

end Mettapedia.GSLT.Dynamics.ParallelExecutionAuthority
