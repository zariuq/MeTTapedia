import Mathlib.Data.Fintype.Basic
import Mettapedia.GSLT.LanguageDef.CertificateGSLTWireFormat

/-!
# Authority-bound finite-evidence applications for CertificateGSLT

Proof checking is finitary even when the meaning being certified concerns an
unbounded computation, an infinite path, or an open-ended theory.  This module
instantiates that observation at the CertificateGSLT checking boundary.  It is not
the core ultrainfinite GSLT theory: that ambient-first, two-variance,
proof-relevant layer lives in `Mettapedia.GSLT.Core.Ultrainfinite`.

There are four deliberately separate layers.

1. A `SemanticAuthority` gives finite evidence a meaning through a sound
   checker.  Its opaque identity is checked at the artifact boundary, so a
   semantic revision cannot silently inherit old evidence.
2. A Büchi finite-state controller, as one example, separates local transition legality from a
   global progress measure.  Their conjunction entails an infinitary Buchi
   recurrence property; local legality alone does not.
3. An operational attempt records search progress and heuristic score, but
   neither field participates in evidence acceptance.
4. A `CheckedLowering` lets a compact executable representation reach a
   semantic authority only by replaying its lowered evidence there.  This is
   the abstract obligation of a native inference kernel relative to MIK.

The concrete `wireArticleAuthority` instantiates the first layer with the
actual versioned `WireArticle` checker.  No new proof semantics or private
article checker is introduced.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

universe uId uClaim uCertificate uNative uScore uState uAction

/-! ## Semantic authority and identity -/

/-- A checker together with the semantic statement its acceptance entails.

`AuthorityId` is intentionally abstract.  Deployment may realize it by a
canonical definition identity, a signed registry identifier, or another
authenticated name.  This layer requires only exact equality and therefore
does not freeze a digest or serialization design. -/
structure SemanticAuthority (AuthorityId : Type uId) (Claim : Type uClaim)
    where
  id : AuthorityId
  Certificate : Type uCertificate
  check : Claim → Certificate → Bool
  Meaning : Claim → Prop
  sound : ∀ {claim certificate}, check claim certificate = true → Meaning claim

/-- Evidence at a transport boundary names the semantic authority under which
it was authored. -/
structure EvidenceEnvelope (AuthorityId : Type uId)
    (Certificate : Type uCertificate) where
  authority : AuthorityId
  certificate : Certificate

/-- Fail-closed checking of an authority-tagged certificate. -/
def SemanticAuthority.checkEnvelope {AuthorityId : Type uId}
    {Claim : Type uClaim} [DecidableEq AuthorityId]
    (authority : SemanticAuthority AuthorityId Claim)
    (claim : Claim)
    (envelope : EvidenceEnvelope AuthorityId authority.Certificate) : Bool :=
  decide (envelope.authority = authority.id) &&
    authority.check claim envelope.certificate

theorem SemanticAuthority.checkEnvelope_eq_true_iff
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    (authority : SemanticAuthority AuthorityId Claim)
    (claim : Claim)
    (envelope : EvidenceEnvelope AuthorityId authority.Certificate) :
    authority.checkEnvelope claim envelope = true ↔
      envelope.authority = authority.id ∧
        authority.check claim envelope.certificate = true := by
  simp [SemanticAuthority.checkEnvelope]

/-- An accepted envelope has the meaning assigned by its named authority. -/
theorem SemanticAuthority.envelope_sound
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    (authority : SemanticAuthority AuthorityId Claim)
    {claim : Claim}
    {envelope : EvidenceEnvelope AuthorityId authority.Certificate}
    (accepted : authority.checkEnvelope claim envelope = true) :
    authority.Meaning claim := by
  exact authority.sound
    (authority.checkEnvelope_eq_true_iff claim envelope |>.mp accepted).2

/-- Evidence naming a different authority is rejected before replay. -/
theorem SemanticAuthority.wrong_authority_rejected
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    (authority : SemanticAuthority AuthorityId Claim)
    (claim : Claim)
    (certificate : authority.Certificate)
    {other : AuthorityId} (different : other ≠ authority.id) :
    authority.checkEnvelope claim ⟨other, certificate⟩ = false := by
  simp [SemanticAuthority.checkEnvelope, different]

/-! ## Search and operational status are not evidence -/

/-- Operational completion is deliberately not an evidence verdict. -/
inductive OperationalStatus where
  | running
  | completed
  | resourceExhausted
  | failed
deriving Repr, DecidableEq

/-- One producer attempt.  Scores and operational state may guide Prime, but
acceptance depends only on the offered authority-tagged evidence. -/
structure EvidenceAttempt {AuthorityId : Type uId} {Claim : Type uClaim}
    (authority : SemanticAuthority AuthorityId Claim) (Score : Type uScore)
    where
  claim : Claim
  evidence : Option (EvidenceEnvelope AuthorityId authority.Certificate)
  operational : OperationalStatus
  score : Score

/-- Evidence acceptance for an attempt; operational state and score are not
inputs to this definition. -/
def EvidenceAttempt.accepted {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    {authority : SemanticAuthority AuthorityId Claim} {Score : Type uScore}
    (attempt : EvidenceAttempt authority Score) : Bool :=
  match attempt.evidence with
  | none => false
  | some envelope => authority.checkEnvelope attempt.claim envelope

/-- Changing only search status cannot change evidence acceptance. -/
theorem EvidenceAttempt.accepted_independent_of_operational
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    {authority : SemanticAuthority AuthorityId Claim} {Score : Type uScore}
    (attempt : EvidenceAttempt authority Score)
    (status : OperationalStatus) :
    ({ attempt with operational := status }).accepted = attempt.accepted := by
  rfl

/-- Changing only a heuristic score cannot change evidence acceptance. -/
theorem EvidenceAttempt.accepted_independent_of_score
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    {authority : SemanticAuthority AuthorityId Claim} {Score : Type uScore}
    (attempt : EvidenceAttempt authority Score) (score : Score) :
    ({ attempt with score := score }).accepted = attempt.accepted := by
  rfl

/-- Resource exhaustion with no evidence is not acceptance.  In a paired
positive/negative evidence layer this leaves both lanes absent; it does not
manufacture refutation. -/
theorem EvidenceAttempt.resourceExhaustion_without_evidence
    {AuthorityId : Type uId} {Claim : Type uClaim}
    [DecidableEq AuthorityId]
    {authority : SemanticAuthority AuthorityId Claim} {Score : Type uScore}
    (claim : Claim) (score : Score) :
    (EvidenceAttempt.accepted
      (authority := authority)
      { claim := claim
        evidence := none
        operational := .resourceExhausted
        score := score }) = false := by
  rfl

/-! ## Checked lowering: the NIK-to-MIK obligation -/

/-- A compact executable representation is inside an authority's trusted
waist only when every native acceptance replays as acceptance of explicitly
lowered evidence by that authority. -/
structure CheckedLowering {AuthorityId : Type uId} {Claim : Type uClaim}
    (authority : SemanticAuthority AuthorityId Claim)
    (NativeEvidence : Type uNative) where
  nativeCheck : Claim → NativeEvidence → Bool
  lower : NativeEvidence → authority.Certificate
  replay : ∀ {claim evidence}, nativeCheck claim evidence = true →
    authority.check claim (lower evidence) = true

/-- Native acceptance is semantically sound only as a corollary of replay at
the authority. -/
theorem CheckedLowering.sound
    {AuthorityId : Type uId} {Claim : Type uClaim}
    {authority : SemanticAuthority AuthorityId Claim}
    {NativeEvidence : Type uNative}
    (lowering : CheckedLowering authority NativeEvidence)
    {claim : Claim} {evidence : NativeEvidence}
    (accepted : lowering.nativeCheck claim evidence = true) :
    authority.Meaning claim :=
  authority.sound (lowering.replay accepted)

/-! ## The actual MIK article authority -/

/-- The real chronological article checker, packaged as a semantic authority.
The evidence proves exactly its stored target under the supplied validated
definition. -/
def wireArticleAuthority {AuthorityId : Type uId}
    (authorityId : AuthorityId) (definition : ValidatedCalculusLanguageDef) :
    SemanticAuthority AuthorityId Pattern where
  id := authorityId
  Certificate := WireArticle
  check := fun goal article =>
    decide (article.target = goal) && checkWireArticle definition article
  Meaning := fun goal => Nonempty (Derivation definition goal)
  sound := by
    intro goal article accepted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
    rw [← accepted.1]
    exact checkWireArticle_sound accepted.2

@[simp] theorem wireArticleAuthority_check
    {AuthorityId : Type uId} (authorityId : AuthorityId)
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern)
    (article : WireArticle) :
    (wireArticleAuthority authorityId definition).check goal article =
      (decide (article.target = goal) &&
        checkWireArticle definition article) := rfl

/-- Every derivation supplies evidence accepted by the actual article
authority. -/
theorem wireArticleAuthority_complete
    {AuthorityId : Type uId} (authorityId : AuthorityId)
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) :
    (wireArticleAuthority authorityId definition).check goal
      (articleOfDerivation derivation) = true := by
  rw [wireArticleAuthority_check]
  rw [checkWireArticle_articleOfDerivation derivation]
  simp [articleOfDerivation]

/-- Exact certificate-existence correspondence at the authority boundary. -/
theorem wireArticleAuthority_correspondence
    {AuthorityId : Type uId} (authorityId : AuthorityId)
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    (∃ article : WireArticle,
        (wireArticleAuthority authorityId definition).check goal article =
          true) ↔
      Nonempty (Derivation definition goal) := by
  constructor
  · rintro ⟨article, accepted⟩
    exact (wireArticleAuthority authorityId definition).sound accepted
  · rintro ⟨derivation⟩
    exact ⟨articleOfDerivation derivation,
      wireArticleAuthority_complete authorityId derivation⟩

/-! ## Finite controllers and infinitary recurrence -/

/-- A labelled transition system whose predicates are executable.  Finiteness
is required only by the checker below, not by the semantic soundness theorem,
so future symbolic or infinite-state definitions remain possible. -/
structure LabeledSystem (State : Type uState) (Action : Type uAction) where
  step : State → Action → State → Bool
  accepting : State → Bool

/-- An executable memoryless controller.  `active` identifies the finite cone
claimed by a certificate; inactive states impose no proof obligation. -/
structure MemorylessController (State : Type uState) (Action : Type uAction)
    where
  active : State → Bool
  action : State → Action
  next : State → State

/-- A natural-number progress measure offered for a controller. -/
structure ProgressMeasure (State : Type uState) where
  rank : State → Nat

/-- The local half of controller checking: the root is covered, and every
covered choice is a real transition to another covered state. -/
def MemorylessController.LocallyValid
    {State : Type uState} {Action : Type uAction}
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action) (root : State) : Prop :=
  controller.active root = true ∧
    ∀ state, controller.active state = true →
      system.step state (controller.action state) (controller.next state) =
          true ∧
        controller.active (controller.next state) = true

/-- The global half of controller checking.  Accepting states normalize to
rank zero.  At a nonaccepting state, the selected successor must either be
accepting or have strictly smaller rank. -/
def ProgressMeasure.GloballyValid
    {State : Type uState} {Action : Type uAction}
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action)
    (measure : ProgressMeasure State) : Prop :=
  ∀ state, controller.active state = true →
    if system.accepting state then
      measure.rank state = 0
    else
      system.accepting (controller.next state) = true ∨
        measure.rank (controller.next state) < measure.rank state

/-- Complete evidence is the conjunction of local transition legality and a
global progress argument. -/
def ProgressMeasure.Valid
    {State : Type uState} {Action : Type uAction}
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action)
    (measure : ProgressMeasure State) (root : State) : Prop :=
  controller.LocallyValid system root ∧
    measure.GloballyValid system controller

private def locallyValidDecidable
    {State : Type uState} {Action : Type uAction}
    [Fintype State]
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action) (root : State) :
    Decidable (controller.LocallyValid system root) := by
  unfold MemorylessController.LocallyValid
  infer_instance

private def globallyValidDecidable
    {State : Type uState} {Action : Type uAction}
    [Fintype State]
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action)
    (measure : ProgressMeasure State) :
    Decidable (measure.GloballyValid system controller) := by
  unfold ProgressMeasure.GloballyValid
  infer_instance

/-- Executable local checker for a finite carrier. -/
def MemorylessController.checkLocal
    {State : Type uState} {Action : Type uAction}
    [Fintype State]
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action) (root : State) : Bool :=
  @decide (controller.LocallyValid system root)
    (locallyValidDecidable system controller root)

/-- Executable global checker for a finite carrier. -/
def ProgressMeasure.checkGlobal
    {State : Type uState} {Action : Type uAction}
    [Fintype State]
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action)
    (measure : ProgressMeasure State) : Bool :=
  @decide (measure.GloballyValid system controller)
    (globallyValidDecidable system controller measure)

/-- The finite certificate checker keeps both verdicts visible. -/
def ProgressMeasure.check
    {State : Type uState} {Action : Type uAction}
    [Fintype State]
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action)
    (measure : ProgressMeasure State) (root : State) : Bool :=
  controller.checkLocal system root &&
    measure.checkGlobal system controller

theorem MemorylessController.checkLocal_eq_true_iff
    {State : Type uState} {Action : Type uAction}
    [Fintype State]
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action) (root : State) :
    controller.checkLocal system root = true ↔
      controller.LocallyValid system root := by
  simp [MemorylessController.checkLocal]

theorem ProgressMeasure.checkGlobal_eq_true_iff
    {State : Type uState} {Action : Type uAction}
    [Fintype State]
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action)
    (measure : ProgressMeasure State) :
    measure.checkGlobal system controller = true ↔
      measure.GloballyValid system controller := by
  simp [ProgressMeasure.checkGlobal]

theorem ProgressMeasure.check_eq_true_iff
    {State : Type uState} {Action : Type uAction}
    [Fintype State]
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action)
    (measure : ProgressMeasure State) (root : State) :
    measure.check system controller root = true ↔
      measure.Valid system controller root := by
  simp [ProgressMeasure.check, ProgressMeasure.Valid,
    MemorylessController.checkLocal_eq_true_iff,
    ProgressMeasure.checkGlobal_eq_true_iff]

/-- An infinite execution controlled from a chosen root. -/
structure ControlledExecution
    {State : Type uState} {Action : Type uAction}
    (controller : MemorylessController State Action) (root : State) where
  state : Nat → State
  starts : state 0 = root
  follows : ∀ n, state (n + 1) = controller.next (state n)

/-- Every total controller has a canonical infinite execution obtained by
iteration.  Consequently the universal recurrence property below is not
vacuous. -/
def MemorylessController.canonicalExecution
    {State : Type uState} {Action : Type uAction}
    (controller : MemorylessController State Action) (root : State) :
    ControlledExecution controller root where
  state n := controller.next^[n] root
  starts := by simp
  follows n := by
    simpa [Nat.succ_eq_add_one] using
      Function.iterate_succ_apply' controller.next n root

theorem MemorylessController.execution_nonempty
    {State : Type uState} {Action : Type uAction}
    (controller : MemorylessController State Action) (root : State) :
    Nonempty (ControlledExecution controller root) :=
  ⟨controller.canonicalExecution root⟩

/-- Buchi recurrence: accepting states occur beyond every finite prefix. -/
def InfinitelyOftenAccepting
    {State : Type uState} {Action : Type uAction}
    (system : LabeledSystem State Action) (path : Nat → State) : Prop :=
  ∀ lowerBound, ∃ visit, lowerBound ≤ visit ∧
    system.accepting (path visit) = true

/-- A controller wins the recurrence objective when all executions following
its selected transitions visit accepting states infinitely often. -/
def MemorylessController.BuchiWinning
    {State : Type uState} {Action : Type uAction}
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action) (root : State) : Prop :=
  ∀ execution : ControlledExecution controller root,
    InfinitelyOftenAccepting system execution.state

private theorem ControlledExecution.active
    {State : Type uState} {Action : Type uAction}
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action} {root : State}
    (localValidity : controller.LocallyValid system root)
    (execution : ControlledExecution controller root) :
    ∀ n, controller.active (execution.state n) = true := by
  intro n
  induction n with
  | zero => simpa [execution.starts] using localValidity.1
  | succ n inductionHypothesis =>
      rw [execution.follows n]
      exact (localValidity.2 _ inductionHypothesis).2

/-- **Finite evidence entails an infinitary property.**  Local edge checking
keeps the execution inside the certified cone.  If accepting states stopped
appearing, the global measure would descend strictly at every remaining
step, producing an impossible infinite descent in the natural numbers. -/
theorem ProgressMeasure.buchi_sound
    {State : Type uState} {Action : Type uAction}
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action}
    {measure : ProgressMeasure State} {root : State}
    (valid : measure.Valid system controller root) :
    controller.BuchiWinning system root := by
  intro execution lowerBound
  by_contra noVisit
  have neverAccepts : ∀ visit, lowerBound ≤ visit →
      system.accepting (execution.state visit) ≠ true := by
    intro visit lower accepting
    exact noVisit ⟨visit, lower, accepting⟩
  have active := execution.active valid.1
  have rankBound : ∀ offset,
      measure.rank (execution.state (lowerBound + offset)) + offset ≤
        measure.rank (execution.state lowerBound) := by
    intro offset
    induction offset with
    | zero => simp
    | succ offset inductionHypothesis =>
        have currentNotAccepting :=
          neverAccepts (lowerBound + offset) (by omega)
        have currentFalse :
            system.accepting (execution.state (lowerBound + offset)) =
              false := by
          cases accepted :
              system.accepting (execution.state (lowerBound + offset)) <;>
            simp_all
        have progress := valid.2
          (execution.state (lowerBound + offset))
          (active (lowerBound + offset))
        rw [if_neg (by simpa using currentFalse)] at progress
        have pathNext :
            execution.state (lowerBound + (offset + 1)) =
              controller.next
                (execution.state (lowerBound + offset)) := by
          simpa [Nat.add_assoc] using
            execution.follows (lowerBound + offset)
        have nextNotAccepting :
            system.accepting
                (controller.next
                  (execution.state (lowerBound + offset))) ≠ true := by
          intro accepted
          apply neverAccepts (lowerBound + (offset + 1)) (by omega)
          simpa [pathNext] using accepted
        have decreases :
            measure.rank
                (controller.next
                  (execution.state (lowerBound + offset))) <
              measure.rank (execution.state (lowerBound + offset)) :=
          progress.resolve_left nextNotAccepting
        rw [pathNext]
        omega
  have impossible :=
    rankBound (measure.rank (execution.state lowerBound) + 1)
  omega

/-- A claim presented to the finite Buchi authority consists of the
executable controller and its chosen initial state. -/
structure BuchiControllerClaim (State : Type uState) (Action : Type uAction)
    where
  root : State
  controller : MemorylessController State Action

/-- The finite progress checker is a semantic authority for controller
recurrence.  The identifier remains supplied by the caller and can therefore
track a definition, abstraction, and policy without fixing their encoding
here. -/
def buchiControllerAuthority
    {AuthorityId : Type uId} {State : Type uState} {Action : Type uAction}
    [Fintype State]
    (authorityId : AuthorityId) (system : LabeledSystem State Action) :
    SemanticAuthority AuthorityId (BuchiControllerClaim State Action) where
  id := authorityId
  Certificate := ProgressMeasure State
  check := fun claim measure =>
    measure.check system claim.controller claim.root
  Meaning := fun claim =>
    claim.controller.BuchiWinning system claim.root
  sound := by
    intro claim measure accepted
    exact ProgressMeasure.buchi_sound
      ((ProgressMeasure.check_eq_true_iff system claim.controller measure
        claim.root).mp accepted)

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
