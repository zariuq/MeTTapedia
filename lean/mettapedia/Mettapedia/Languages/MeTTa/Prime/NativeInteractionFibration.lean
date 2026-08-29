import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.WorkSpan

/-!
# Proof-relevant interaction fibres for MeTTa Native

An interleaving product is the semantic boundary at which two interaction
fibres are known to evolve independently.  This module lifts exact events from
the component presentations into that product and derives both chronological
orders and their commuting square.  The construction is generic in the two
GSLTs; it is not specific to rho or to a particular scheduler.

For concrete Cost-rho execution, independence is stronger than distinct
channel names.  Two events are separated when one source configuration has a
common multiset decomposition containing distinct endpoint and purse
occurrences for both events.  `CostEffectSeparation` retains that decomposition
in `Type`, allowing it to construct a proof-relevant one-wave schedule.  Its
propositional erasure is the existing `CostCompatibleAt` predicate and hence
inherits the exact costed diamond.

The resulting cost law is deliberately one-directional:

* an occurrence-separation witness licenses parallel composition and max-span;
* without such a witness there is no parallel license;
* shared resources do not by themselves prove a sequential execution.  When
  an actual chronological path exists, its established readout uses sequential
  composition.

Thus namespace predicates may be useful analyses, but operational independence
is certified by retained occurrence/resource separation rather than by names
alone.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration

open Mettapedia.Algebra
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionCost
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe uLeftSite uRightSite uLeftEvent uRightEvent uGround

/-! ## Exact events in an interleaving product -/

/-- A proof-relevant product event records which fibre moved and retains the
exact component event.  The other fibre is unchanged up to its equations. -/
inductive FibredEvent {left right : GSLT}
    (leftPresentation : InteractionPresentation.{uLeftSite, uLeftEvent} left)
    (rightPresentation : InteractionPresentation.{uRightSite, uRightEvent} right) :
    Sum leftPresentation.Site rightPresentation.Site →
      (left.Term × right.Term) → (left.Term × right.Term) → Type _ where
  | left {site : leftPresentation.Site}
      {leftSource leftTarget : left.Term}
      {rightSource rightTarget : right.Term}
      (event : leftPresentation.Event site leftSource leftTarget)
      (rightHolds : right.Equiv rightSource rightTarget) :
      FibredEvent leftPresentation rightPresentation (.inl site)
        (leftSource, rightSource) (leftTarget, rightTarget)
  | right {site : rightPresentation.Site}
      {leftSource leftTarget : left.Term}
      {rightSource rightTarget : right.Term}
      (leftHolds : left.Equiv leftSource leftTarget)
      (event : rightPresentation.Event site rightSource rightTarget) :
      FibredEvent leftPresentation rightPresentation (.inr site)
        (leftSource, rightSource) (leftTarget, rightTarget)

/-- Component presentations combine into an exact presentation of the
interleaving product. -/
def fibredPresentation {left right : GSLT}
    (leftPresentation : InteractionPresentation.{uLeftSite, uLeftEvent} left)
    (rightPresentation : InteractionPresentation.{uRightSite, uRightEvent} right) :
    InteractionPresentation (GSLT.interleavingProduct left right) where
  Site := Sum leftPresentation.Site rightPresentation.Site
  Event := FibredEvent leftPresentation rightPresentation
  sound := by
    intro site source target event
    cases event with
    | left event rightHolds =>
        exact Or.inl ⟨leftPresentation.sound event, rightHolds⟩
    | right leftHolds event =>
        exact Or.inr ⟨leftHolds, rightPresentation.sound event⟩

/-! ## MeTTa Native superposition as product lowering -/

/-- Two partial endpoint interpretations combine at precisely the native
binary-superposition constructor.  Failure in either fibre remains failure;
no fallback endpoint is manufactured. -/
def productInterpretation {left right : GSLT}
    (leftInterpretation : EndpointInterpretation left)
    (rightInterpretation : EndpointInterpretation right) :
    EndpointInterpretation (GSLT.interleavingProduct left right) where
  lower?
    | .superpose leftTerm rightTerm =>
        match leftInterpretation.lower? leftTerm,
            rightInterpretation.lower? rightTerm with
        | some leftEndpoint, some rightEndpoint =>
            some (leftEndpoint, rightEndpoint)
        | _, _ => none
    | _ => none

@[simp] theorem productInterpretation_superpose {left right : GSLT}
    (leftInterpretation : EndpointInterpretation left)
    (rightInterpretation : EndpointInterpretation right)
    (leftTerm rightTerm : StagedReflectiveTm 0 0) :
    (productInterpretation leftInterpretation rightInterpretation).lower?
        (.superpose leftTerm rightTerm) =
      Option.map₂ Prod.mk (leftInterpretation.lower? leftTerm)
        (rightInterpretation.lower? rightTerm) := by
  cases leftEq : leftInterpretation.lower? leftTerm <;>
    cases rightEq : rightInterpretation.lower? rightTerm <;>
      simp [productInterpretation, leftEq, rightEq] <;> rfl

@[simp] theorem productInterpretation_non_superpose {left right : GSLT}
    (leftInterpretation : EndpointInterpretation left)
    (rightInterpretation : EndpointInterpretation right)
    (term : StagedReflectiveTm 0 0)
    (notSuperpose : ∀ leftTerm rightTerm, term ≠ .superpose leftTerm rightTerm) :
    (productInterpretation leftInterpretation rightInterpretation).lower? term =
      none := by
  cases term <;> simp_all [productInterpretation]

/-! ## Exact commuting histories -/

section CommutingPair

variable {left right : GSLT}
variable (leftPresentation : InteractionPresentation.{uLeftSite, uLeftEvent} left)
variable (rightPresentation : InteractionPresentation.{uRightSite, uRightEvent} right)
variable {leftSite : leftPresentation.Site}
variable {rightSite : rightPresentation.Site}
variable {leftSource leftTarget : left.Term}
variable {rightSource rightTarget : right.Term}

/-- Two exact component events yield the four sides of one commuting square. -/
theorem exactEvents_commutingSquare
    (leftEvent : leftPresentation.Event leftSite leftSource leftTarget)
    (rightEvent : rightPresentation.Event rightSite rightSource rightTarget) :
    (GSLT.interleavingProduct left right).Step
        (leftSource, rightSource) (leftTarget, rightSource) ∧
      (GSLT.interleavingProduct left right).Step
        (leftTarget, rightSource) (leftTarget, rightTarget) ∧
      (GSLT.interleavingProduct left right).Step
        (leftSource, rightSource) (leftSource, rightTarget) ∧
      (GSLT.interleavingProduct left right).Step
        (leftSource, rightTarget) (leftTarget, rightTarget) :=
  GSLT.interleavingProduct_commutingSquare
    (leftPresentation.sound leftEvent) (rightPresentation.sound rightEvent)

/-- Exact history taking the left event and then the right event. -/
def leftThenRightPath
    (leftEvent : leftPresentation.Event leftSite leftSource leftTarget)
    (rightEvent : rightPresentation.Event rightSite rightSource rightTarget) :
    EventPath (fibredPresentation leftPresentation rightPresentation)
      (leftSource, rightSource) (leftTarget, rightTarget) :=
  .cons (.left leftEvent (right.equations.iseqv.refl _))
    (.cons (.right (left.equations.iseqv.refl _) rightEvent)
      (.nil (presentation := fibredPresentation leftPresentation
        rightPresentation) (leftTarget, rightTarget)))

/-- Exact history taking the right event and then the left event. -/
def rightThenLeftPath
    (leftEvent : leftPresentation.Event leftSite leftSource leftTarget)
    (rightEvent : rightPresentation.Event rightSite rightSource rightTarget) :
    EventPath (fibredPresentation leftPresentation rightPresentation)
      (leftSource, rightSource) (leftTarget, rightTarget) :=
  .cons (.right (left.equations.iseqv.refl _) rightEvent)
    (.cons (.left leftEvent (right.equations.iseqv.refl _))
      (.nil (presentation := fibredPresentation leftPresentation
        rightPresentation) (leftTarget, rightTarget)))

@[simp] theorem leftThenRightPath_length
    (leftEvent : leftPresentation.Event leftSite leftSource leftTarget)
    (rightEvent : rightPresentation.Event rightSite rightSource rightTarget) :
    EventPath.pathLength (fibredPresentation leftPresentation rightPresentation)
      (leftThenRightPath leftPresentation rightPresentation leftEvent rightEvent) =
        2 :=
  rfl

@[simp] theorem rightThenLeftPath_length
    (leftEvent : leftPresentation.Event leftSite leftSource leftTarget)
    (rightEvent : rightPresentation.Event rightSite rightSource rightTarget) :
    EventPath.pathLength (fibredPresentation leftPresentation rightPresentation)
      (rightThenLeftPath leftPresentation rightPresentation leftEvent rightEvent) =
        2 :=
  rfl

/-- The stage-independent chronological work/span readout of an exact event
path.  This is the semantic content internalized by `pathWorkSpan`; keeping the
generic definition outside the stage-zero CwF also permits higher-universe
interaction presentations. -/
def eventPathWorkSpan {theory : GSLT}
    (presentation : InteractionPresentation theory)
    {source target : theory.Term}
    (path : EventPath presentation source target) : WorkSpan :=
  let count := EventPath.pathLength presentation path
  ⟨count, count⟩

/-- A chronological observation of either ordering has two units of work and
two units of span. -/
theorem chronologicalPair_workSpan
    (leftEvent : leftPresentation.Event leftSite leftSource leftTarget)
    (rightEvent : rightPresentation.Event rightSite rightSource rightTarget) :
    eventPathWorkSpan (fibredPresentation leftPresentation rightPresentation)
      (leftThenRightPath leftPresentation rightPresentation
        leftEvent rightEvent) = ⟨2, 2⟩ :=
  rfl

end CommutingPair

/-! ## The local two-state fibre generated by one event -/

/-- Local phase of one exact event occurrence. -/
inductive EventPhase where
  | before
  | after
  deriving DecidableEq, Repr

/-- The minimal operational fibre generated by one event: one transition from
`before` to `after`, with no reverse transition. -/
def eventFibre : GSLT where
  Term := EventPhase
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    source = .before ∧ target = .after
  rewrites_resp_left := by
    rintro source source' target rfl step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    rintro source target target' step rfl
    exact step

theorem eventFibre_step : eventFibre.Step .before .after :=
  ⟨rfl, rfl⟩

/-- Negative control: an occurrence cannot fire backward. -/
theorem eventFibre_no_reverse : ¬ eventFibre.Step .after .before := by
  rintro ⟨impossible, _⟩
  cases impossible

/-- Two event fibres form the canonical four-edge commuting square. -/
theorem eventFibre_productSquare :
    (GSLT.interleavingProduct eventFibre eventFibre).Step
        (.before, .before) (.after, .before) ∧
      (GSLT.interleavingProduct eventFibre eventFibre).Step
        (.after, .before) (.after, .after) ∧
      (GSLT.interleavingProduct eventFibre eventFibre).Step
        (.before, .before) (.before, .after) ∧
      (GSLT.interleavingProduct eventFibre eventFibre).Step
        (.before, .after) (.after, .after) :=
  GSLT.interleavingProduct_commutingSquare eventFibre_step eventFibre_step

/-! ## Concrete occurrence/resource fibres for Cost-rho -/

/-- A proof-relevant separation certificate for two funded Cost-rho events.
The retained frame is the concrete fibre decomposition: both events own
distinct multiset occurrences of every endpoint and purse resource they
consume. -/
structure CostEffectSeparation (Ground : Type uGround)
    (source : CostConfig Ground) (left right : CostedEvent Ground) :
    Type uGround where
  frame : CostConfig Ground
  source_eq : source = costWaveSource [left, right] frame

namespace CostEffectSeparation

variable {Ground : Type uGround} {source : CostConfig Ground}
variable {left right : CostedEvent Ground}

/-- Forget executable decomposition data and retain the established
compatibility proposition. -/
def toCompatible
    (separation : CostEffectSeparation Ground source left right) :
    CostCompatibleAt source left right :=
  ⟨separation.frame, separation.source_eq⟩

/-- The exact common target of the one-wave execution. -/
def target (separation : CostEffectSeparation Ground source left right) :
    CostConfig Ground :=
  costWaveTarget [left, right] separation.frame

/-- The occurrence-preserving receipt of the two-event wave. -/
def receipt (_separation : CostEffectSeparation Ground source left right) :
    Multiset (SpendEvent Ground (CostName Ground)) :=
  costWaveReceipt [left, right]

/-- Realization of the two local event fibres inside the concrete Cost-rho
configuration.  The four phase pairs are the source, two intermediate
configurations, and common target of the costed diamond. -/
def realize (separation : CostEffectSeparation Ground source left right) :
    EventPhase × EventPhase → CostConfig Ground
  | (.before, .before) => source
  | (.after, .before) => costAfterLeft left right separation.frame
  | (.before, .after) => costAfterRight left right separation.frame
  | (.after, .after) => costPairTarget left right separation.frame

@[simp] theorem realize_before_before
    (separation : CostEffectSeparation Ground source left right) :
    separation.realize (.before, .before) = source :=
  rfl

@[simp] theorem realize_after_after
    (separation : CostEffectSeparation Ground source left right) :
    separation.realize (.after, .after) = separation.target := by
  simp [realize, target, costPairTarget, costWaveTarget]

/-- The left edge of the abstract product square is a concrete funded step. -/
theorem realize_leftFirst
    (separation : CostEffectSeparation Ground source left right) :
    CostStep (separation.realize (.before, .before)) left.location left.spend
      (separation.realize (.after, .before)) := by
  have step := left.toCostStepIn (right.consumed + separation.frame)
  simpa [realize, separation.source_eq, costWaveSource, costAfterLeft,
    add_assoc, add_comm, add_left_comm] using step

/-- The second left-then-right edge is a concrete funded step. -/
theorem realize_rightAfter
    (separation : CostEffectSeparation Ground source left right) :
    CostStep (separation.realize (.after, .before)) right.location right.spend
      (separation.realize (.after, .after)) := by
  have step := right.toCostStepIn (left.produced + separation.frame)
  simpa [realize, costAfterLeft, costPairTarget, add_assoc, add_comm,
    add_left_comm] using step

/-- The right edge of the abstract product square is a concrete funded step. -/
theorem realize_rightFirst
    (separation : CostEffectSeparation Ground source left right) :
    CostStep (separation.realize (.before, .before)) right.location right.spend
      (separation.realize (.before, .after)) := by
  have step := right.toCostStepIn (left.consumed + separation.frame)
  simpa [realize, separation.source_eq, costWaveSource, costAfterRight,
    add_assoc, add_comm, add_left_comm] using step

/-- The second right-then-left edge is a concrete funded step. -/
theorem realize_leftAfter
    (separation : CostEffectSeparation Ground source left right) :
    CostStep (separation.realize (.before, .after)) left.location left.spend
      (separation.realize (.after, .after)) := by
  have step := left.toCostStepIn (right.produced + separation.frame)
  simpa [realize, costAfterRight, costPairTarget, add_assoc, add_comm,
    add_left_comm] using step

/-- An occurrence/resource separation certificate realizes every edge of the
generic interleaving-product square inside Cost-rho.  This is the local product
factorization theorem; it is derived from a concrete common decomposition, not
postulated by a scheduler. -/
theorem realizes_productSquare
    (separation : CostEffectSeparation Ground source left right) :
    CostStep (separation.realize (.before, .before)) left.location left.spend
        (separation.realize (.after, .before)) ∧
      CostStep (separation.realize (.after, .before)) right.location right.spend
        (separation.realize (.after, .after)) ∧
      CostStep (separation.realize (.before, .before)) right.location right.spend
        (separation.realize (.before, .after)) ∧
      CostStep (separation.realize (.before, .after)) left.location left.spend
        (separation.realize (.after, .after)) :=
  ⟨separation.realize_leftFirst, separation.realize_rightAfter,
    separation.realize_rightFirst, separation.realize_leftAfter⟩

/-- The retained decomposition is a concrete Cost-rho matching. -/
def toMatching (separation : CostEffectSeparation Ground source left right) :
    CostMatching Ground where
  source := source
  events := [left, right]
  frame := separation.frame
  source_eq := separation.source_eq

/-- One proof-relevant separation certificate constructs a genuine concurrent
Cost-rho step. -/
theorem parallelStep (separation : CostEffectSeparation Ground source left right) :
    ParallelCostStep source separation.receipt separation.target := by
  refine ⟨separation.toMatching, rfl, ?_, rfl, rfl⟩
  change [left, right] ≠ []
  simp

/-- The two-event step extends to a one-wave, proof-relevant schedule. -/
def schedule (separation : CostEffectSeparation Ground source left right) :
    ParallelCostSchedule source separation.receipt separation.target 2 1 := by
  simpa [receipt, costWaveReceipt] using
    (ParallelCostSchedule.cons separation.parallelStep
      (ParallelCostSchedule.nil separation.target))

/-- The proof-relevant schedule erases to the existing reachability trace. -/
theorem schedule_erases
    (separation : CostEffectSeparation Ground source left right) :
    separation.schedule.toTrace =
      ParallelCostTrace.cons separation.parallelStep
        (ParallelCostTrace.nil separation.target) :=
  rfl

/-- Occurrence separation inherits the exact Cost-rho commuting diamond. -/
theorem diamond (separation : CostEffectSeparation Ground source left right) :
    CostedDiamond source left right :=
  compatible_costed_diamond separation.toCompatible

/-- The one-wave schedule has work two and span one. -/
theorem schedule_workSpan
    (separation : CostEffectSeparation Ground source left right) :
    separation.schedule.workSpan = ⟨2, 1⟩ := by
  apply WorkSpan.ext
  · exact separation.schedule.workSpan_work_eq_count
  · exact separation.schedule.workSpan_span_eq_waves

/-- The retained one-wave schedule cannot be confused with a chronological
two-event accounting result. -/
theorem schedule_ne_chronological
    (separation : CostEffectSeparation Ground source left right) :
    separation.schedule.workSpan ≠ ⟨2, 2⟩ := by
  rw [separation.schedule_workSpan]
  decide

/-- The listed left-then-right serialization reaches the same exact target. -/
theorem leftThenRight_serializes
    (separation : CostEffectSeparation Ground source left right) :
    CostTrace source (costWaveTrace [left, right]) separation.target :=
  separation.toMatching.serializes

/-- Swapping the events is another serialization to the same exact target. -/
theorem rightThenLeft_serializes
    (separation : CostEffectSeparation Ground source left right) :
    CostTrace source (costWaveTrace [right, left]) separation.target :=
  separation.toMatching.permutation_serializes
    (List.Perm.swap left right [])

/-- A shared single purse occurrence rules out the proof-relevant parallel
license as well as its propositional erasure. -/
theorem not_of_shared_single_purse [DecidableEq Ground]
    (purse : CostTerm Ground)
    (sourceCount : source.count purse = 1)
    (leftUses : purse ∈ left.fundingBefore)
    (rightUses : purse ∈ right.fundingBefore) :
    CostEffectSeparation Ground source left right → False := by
  intro separation
  exact shared_single_purse_conflicts purse sourceCount leftUses rightUses
    separation.toCompatible

end CostEffectSeparation

/-! ## A same-channel positive control and a contested-resource negative control -/

namespace Examples

abbrev Ground := String

def channel : CostName Ground := .signature {"channel"}
def leftSeal : CostSig Ground := {"left"}
def rightSeal : CostSig Ground := {"right"}

theorem leftSeal_valid : leftSeal.RuntimeValid := by
  simp [CostSig.RuntimeValid, leftSeal]

theorem rightSeal_valid : rightSeal.RuntimeValid := by
  simp [CostSig.RuntimeValid, rightSeal]

def leftSelection : FundingSelection Ground channel leftSeal where
  chosen := {⟨leftSeal, .empty, leftSeal_valid⟩}
  demand_eq := by simp

def rightSelection : FundingSelection Ground channel rightSeal where
  chosen := {⟨rightSeal, .empty, rightSeal_valid⟩}
  demand_eq := by simp

def body : CostTerm Ground := .drop (.bvar 0)
def leftPayload : CostTerm Ground := .signed .nil leftSeal
def rightPayload : CostTerm Ground := .signed .nil rightSeal

def leftEvent : CostedEvent Ground :=
  .wholeRecvSend channel body leftPayload leftSeal leftSeal_valid leftSelection

def rightEvent : CostedEvent Ground :=
  .wholeRecvSend channel body rightPayload rightSeal rightSeal_valid
    rightSelection

def source : CostConfig Ground := costWaveSource [leftEvent, rightEvent] 0

/-- Same channel, distinct endpoint and purse occurrences: the exact
decomposition licenses one parallel wave. -/
def sameChannelSeparation :
    CostEffectSeparation Ground source leftEvent rightEvent :=
  ⟨0, rfl⟩

theorem sameChannel_parallel_workSpan :
    sameChannelSeparation.schedule.workSpan = ⟨2, 1⟩ :=
  sameChannelSeparation.schedule_workSpan

def contestedPurse : CostTerm Ground :=
  .purse channel (.cons leftSeal .empty)

def leftCompetitor : CostedEvent Ground :=
  .wholeRecvSend channel body rightPayload leftSeal leftSeal_valid leftSelection

def contestedSource : CostConfig Ground :=
  leftEvent.endpoints + leftCompetitor.endpoints + leftEvent.fundingBefore

theorem contestedPurse_count : contestedSource.count contestedPurse = 1 := by
  decide

theorem leftEvent_uses_contestedPurse :
    contestedPurse ∈ leftEvent.fundingBefore := by
  decide

theorem leftCompetitor_uses_contestedPurse :
    contestedPurse ∈ leftCompetitor.fundingBefore := by
  decide

/-- Sharing one purse occurrence prevents a parallel-separation certificate;
it does not manufacture a sequential schedule. -/
theorem contested_has_no_parallel_separation :
    CostEffectSeparation Ground contestedSource leftEvent leftCompetitor →
      False :=
  CostEffectSeparation.not_of_shared_single_purse contestedPurse
    contestedPurse_count leftEvent_uses_contestedPurse
    leftCompetitor_uses_contestedPurse

end Examples

#print axioms exactEvents_commutingSquare
#print axioms chronologicalPair_workSpan
#print axioms eventFibre_productSquare
#print axioms CostEffectSeparation.realizes_productSquare
#print axioms CostEffectSeparation.schedule_workSpan
#print axioms CostEffectSeparation.schedule_ne_chronological
#print axioms CostEffectSeparation.diamond
#print axioms Examples.contested_has_no_parallel_separation

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
