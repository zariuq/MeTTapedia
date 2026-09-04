import Mettapedia.TypeTheory.Authority
import Mettapedia.GSLT.Dynamics.ProofRelevantNeed

/-!
# Logical authority under proof-relevant demand

This module relates two independent semantic structures:

* an authority outcome records established evidence, checked refutation, a
  stable fragment boundary, or incomplete search;
* a call-by-need cell records when an already justified result is demanded,
  cached, observed, or retried.

The bridge deliberately caches both positive and negative logical decisions
as values.  A checked refutation is not an evaluator fault.  Fragment
boundaries and incomplete searches are retryable for different reasons, and
neither is cached as a decision.  Operational stable faults therefore remain
available to guest evaluators without being confused with logical polarity.
-/

namespace Mettapedia.GSLT.Dynamics.AuthorityDemand

open Mettapedia.TypeTheory.AuthorityTheory

universe uEstablished uRefuted uBoundary uIncomplete uOrigin uCell

/-! ## Information retained by demand -/

/-- A checked logical decision.  Positive and negative evidence retain their
distinct types even though both are cacheable results. -/
inductive CheckedDecision
    (Established : Type uEstablished) (Refuted : Type uRefuted) where
  | established (evidence : Established)
  | refuted (obstruction : Refuted)
deriving DecidableEq, Repr

/-- A demand may be retried for two semantically different reasons.  A
fragment boundary needs a stronger authority; incompleteness needs more
resources for the same authority. -/
inductive RetryReason
    (Boundary : Type uBoundary) (Incomplete : Type uIncomplete) where
  | outsideFragment (reason : Boundary)
  | incomplete (receipt : Incomplete)
deriving DecidableEq, Repr

/-- The call-by-need outcome corresponding exactly to a four-way authority
outcome.  `Empty` reserves the stable-fault channel for operational faults;
logical refutation is a checked value. -/
def toNeedOutcome
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete} :
    Outcome Established Refuted Boundary Incomplete ->
      ProofRelevantNeed.Outcome (CheckedDecision Established Refuted) Empty
        (RetryReason Boundary Incomplete)
  | .established evidence => .value (.established evidence)
  | .refuted obstruction => .value (.refuted obstruction)
  | .outsideFragment reason =>
      .retryableFault (.outsideFragment reason)
  | .incomplete receipt => .retryableFault (.incomplete receipt)

/-- Recover the complete authority outcome from the demand outcome.  The
stable-fault branch is impossible because this bridge does not manufacture
operational faults. -/
def fromNeedOutcome
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete} :
    ProofRelevantNeed.Outcome (CheckedDecision Established Refuted) Empty
        (RetryReason Boundary Incomplete) ->
      Outcome Established Refuted Boundary Incomplete
  | .value (.established evidence) => .established evidence
  | .value (.refuted obstruction) => .refuted obstruction
  | .stableFault fault => nomatch fault
  | .retryableFault (.outsideFragment reason) => .outsideFragment reason
  | .retryableFault (.incomplete receipt) => .incomplete receipt

@[simp] theorem fromNeedOutcome_toNeedOutcome
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    fromNeedOutcome (toNeedOutcome outcome) = outcome := by
  cases outcome <;> rfl

@[simp] theorem toNeedOutcome_fromNeedOutcome
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    (outcome : ProofRelevantNeed.Outcome
      (CheckedDecision Established Refuted) Empty
      (RetryReason Boundary Incomplete)) :
    toNeedOutcome (fromNeedOutcome outcome) = outcome := by
  cases outcome with
  | value decision => cases decision <;> rfl
  | stableFault fault => exact nomatch fault
  | retryableFault reason => cases reason <;> rfl

/-- Demand scheduling preserves all four authority outcomes exactly. -/
def outcomeEquiv
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete} :
    Outcome Established Refuted Boundary Incomplete ≃
      ProofRelevantNeed.Outcome
        (CheckedDecision Established Refuted) Empty
        (RetryReason Boundary Incomplete) where
  toFun := toNeedOutcome
  invFun := fromNeedOutcome
  left_inv := fromNeedOutcome_toNeedOutcome
  right_inv := toNeedOutcome_fromNeedOutcome

/-! ## Exact demand traces -/

/-- The state reached after demanding one already justified authority
outcome.  Checked decisions are cached; boundaries and incomplete searches
reopen the same immutable suspension. -/
def terminalState
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} (origin : Origin) :
    Outcome Established Refuted Boundary Incomplete ->
      ProofRelevantNeed.CellState Origin
        (CheckedDecision Established Refuted) Empty
  | .established evidence =>
      .cachedValue origin (CheckedDecision.established evidence)
  | .refuted obstruction =>
      .cachedValue origin (CheckedDecision.refuted obstruction)
  | .outsideFragment _ => .suspended origin
  | .incomplete _ => .suspended origin

/-- Demand one authority outcome through the exact call-by-need protocol.
The outcome is an input because the protocol does not pretend to evaluate the
guest theory; its evidence licenses the corresponding commit or retry event. -/
def resolveTrace
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} {Cell : Type uCell}
    (cell : Cell) (origin : Origin)
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    ProofRelevantNeed.Trace (RetryReason Boundary Incomplete) cell
      (.suspended origin) (terminalState origin outcome) :=
  match outcome with
  | .established evidence =>
      .tail (.beginEvaluation cell origin) (.beginEvaluation origin)
        (.tail
          (.commitValue cell origin (CheckedDecision.established evidence))
          (.commitValue origin (CheckedDecision.established evidence))
          (.refl
            (.cachedValue origin (CheckedDecision.established evidence))))
  | .refuted obstruction =>
      .tail (.beginEvaluation cell origin) (.beginEvaluation origin)
        (.tail (.commitValue cell origin (CheckedDecision.refuted obstruction))
          (.commitValue origin (CheckedDecision.refuted obstruction))
          (.refl (.cachedValue origin
            (CheckedDecision.refuted obstruction))))
  | .outsideFragment reason =>
      .tail (.beginEvaluation cell origin) (.beginEvaluation origin)
        (.tail
          (.retry cell origin (RetryReason.outsideFragment reason))
          (.retry origin (RetryReason.outsideFragment reason))
          (.refl (.suspended origin)))
  | .incomplete receipt =>
      .tail (.beginEvaluation cell origin) (.beginEvaluation origin)
        (.tail (.retry cell origin (RetryReason.incomplete receipt))
          (.retry origin (RetryReason.incomplete receipt))
          (.refl (.suspended origin)))

@[simp] theorem resolveTrace_evaluationCount
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} {Cell : Type uCell}
    (cell : Cell) (origin : Origin)
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    (resolveTrace cell origin outcome).evaluationCount = 1 := by
  cases outcome <;> rfl

@[simp] theorem resolveTrace_outcomeObservationCount
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} {Cell : Type uCell}
    (cell : Cell) (origin : Origin)
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    (resolveTrace cell origin outcome).outcomeObservationCount = 0 := by
  cases outcome <;> rfl

@[simp] theorem resolveTrace_inspectionCount
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} {Cell : Type uCell}
    (cell : Cell) (origin : Origin)
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    (resolveTrace cell origin outcome).inspectionCount = 0 := by
  cases outcome <;> rfl

@[simp] theorem resolveTrace_refuted_events
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} {Cell : Type uCell}
    (cell : Cell) (origin : Origin) (obstruction : Refuted) :
    (resolveTrace (Boundary := Boundary) (Incomplete := Incomplete)
      cell origin
        (Outcome.refuted (Established := Established) obstruction)).events =
      [ProofRelevantNeed.Event.beginEvaluation cell origin,
        ProofRelevantNeed.Event.commitValue cell origin
          (CheckedDecision.refuted (Established := Established)
            obstruction)] :=
  rfl

@[simp] theorem resolveTrace_outsideFragment_events
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} {Cell : Type uCell}
    (cell : Cell) (origin : Origin) (reason : Boundary) :
    (resolveTrace (Established := Established) (Refuted := Refuted)
      (Incomplete := Incomplete) cell origin
      (.outsideFragment reason)).events =
      [ProofRelevantNeed.Event.beginEvaluation cell origin,
        ProofRelevantNeed.Event.retry cell origin
          (RetryReason.outsideFragment reason)] :=
  rfl

@[simp] theorem resolveTrace_incomplete_events
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} {Cell : Type uCell}
    (cell : Cell) (origin : Origin) (receipt : Incomplete) :
    (resolveTrace (Established := Established) (Refuted := Refuted)
      (Boundary := Boundary) cell origin (.incomplete receipt)).events =
      [ProofRelevantNeed.Event.beginEvaluation cell origin,
        ProofRelevantNeed.Event.retry cell origin
          (RetryReason.incomplete receipt)] :=
  rfl

/-! ## Logical observation of cached demand -/

/-- Read only the logical decision cached in a need cell.  Unevaluated,
evaluating, and retried cells remain undecided.  The stable-fault branch is
uninhabited in this bridge. -/
def cachedBoolean
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Origin : Type uOrigin} :
    ProofRelevantNeed.CellState Origin
      (CheckedDecision Established Refuted) Empty ->
      Option Bool
  | .absent => none
  | .suspended _ => none
  | .evaluating _ => none
  | .cachedValue _ (.established _) => some true
  | .cachedValue _ (.refuted _) => some false
  | .cachedStableFault _ fault => nomatch fault

/-- The cached logical observation agrees exactly with the authority's own
partial Boolean observation.  Demand changes availability and cost, not
logical polarity. -/
@[simp] theorem cachedBoolean_terminalState
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} (origin : Origin)
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    cachedBoolean (terminalState origin outcome) = outcome.asBool := by
  cases outcome <;> rfl

theorem cachedBoolean_terminal_eq_true_iff
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} (origin : Origin)
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    cachedBoolean (terminalState origin outcome) = some true ↔
      ∃ evidence, outcome = .established evidence := by
  rw [cachedBoolean_terminalState]
  exact outcome.asBool_eq_true_iff

theorem cachedBoolean_terminal_eq_false_iff
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} (origin : Origin)
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    cachedBoolean (terminalState origin outcome) = some false ↔
      ∃ obstruction, outcome = .refuted obstruction := by
  rw [cachedBoolean_terminalState]
  exact outcome.asBool_eq_false_iff

/-- Observing a cached logical decision is a distinct event but performs no
new evaluation. -/
def observeTrace
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} {Cell : Type uCell}
    (cell : Cell) (origin : Origin)
    (decision : CheckedDecision Established Refuted) :
    ProofRelevantNeed.Trace (RetryReason Boundary Incomplete) cell
      (ProofRelevantNeed.CellState.cachedValue (StableFault := Empty)
        origin decision)
      (ProofRelevantNeed.CellState.cachedValue (StableFault := Empty)
        origin decision) :=
  .tail (.observeValue cell origin decision) (.observeValue origin decision)
    (.refl (.cachedValue origin decision))

@[simp] theorem observeTrace_counts
    {Established : Type uEstablished} {Refuted : Type uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {Origin : Type uOrigin} {Cell : Type uCell}
    (cell : Cell) (origin : Origin)
    (decision : CheckedDecision Established Refuted) :
    (observeTrace (Boundary := Boundary) (Incomplete := Incomplete)
      cell origin decision).evaluationCount = 0 ∧
    (observeTrace (Boundary := Boundary) (Incomplete := Incomplete)
      cell origin decision).outcomeObservationCount = 1 := by
  exact ⟨rfl, rfl⟩

/-! ## Sound cached decisions -/

/-- The proposition justified by a checked decision. -/
inductive DecidedMeaning (meaning : Prop) : Type where
  | established (proof : meaning)
  | refuted (refutation : meaning -> False)

/-- Authority evidence gives every cached decision its correct logical
meaning. -/
def CheckedDecision.meaning
    {Judgment : Type uOrigin} (authority : Authority Judgment)
    {judgment : Judgment} :
    CheckedDecision (authority.Evidence judgment)
      (authority.Obstruction judgment) ->
      DecidedMeaning (authority.Holds judgment)
  | .established evidence =>
      .established (authority.evidenceSound judgment evidence)
  | .refuted obstruction =>
      .refuted (authority.obstructionSound judgment obstruction)

/-! ## Positive and negative controls -/

namespace Canary

inductive Judgment where
  | accepted
  | rejected
deriving DecidableEq, Repr

inductive Evidence : Judgment -> Type where
  | accepted : Evidence .accepted

inductive Obstruction : Judgment -> Type where
  | rejected : Obstruction .rejected

def authority : Authority Judgment where
  Holds
    | .accepted => True
    | .rejected => False
  Evidence := Evidence
  Obstruction := Obstruction
  evidenceSound := by
    intro judgment evidence
    cases evidence
    trivial
  obstructionSound := by
    intro judgment obstruction
    cases obstruction
    exact id

def acceptedOutcome :
    Outcome (authority.Evidence .accepted)
      (authority.Obstruction .accepted) Nat Nat :=
  .established .accepted

def rejectedOutcome :
    Outcome (authority.Evidence .rejected)
      (authority.Obstruction .rejected) Nat Nat :=
  .refuted .rejected

theorem accepted_is_cached_positive :
    cachedBoolean (terminalState Judgment.accepted acceptedOutcome) =
      some true :=
  rfl

/-- Negative logical evidence is cached as a decision, not as an operational
stable fault. -/
theorem rejected_is_cached_negative :
    terminalState Judgment.rejected rejectedOutcome =
      ProofRelevantNeed.CellState.cachedValue Judgment.rejected
        (CheckedDecision.refuted Obstruction.rejected) ∧
    cachedBoolean (terminalState Judgment.rejected rejectedOutcome) =
      some false := by
  exact ⟨rfl, rfl⟩

/-- A fragment boundary is not a negative decision. -/
theorem boundary_remains_undecided :
    cachedBoolean
      (terminalState Judgment.accepted
        (Outcome.outsideFragment 7 : Outcome Nat Nat Nat Nat)) = none :=
  rfl

/-- Incomplete search is not a negative decision either. -/
theorem incomplete_remains_undecided :
    cachedBoolean
      (terminalState Judgment.accepted
        (Outcome.incomplete 9 : Outcome Nat Nat Nat Nat)) = none :=
  rfl

end Canary

end Mettapedia.GSLT.Dynamics.AuthorityDemand
