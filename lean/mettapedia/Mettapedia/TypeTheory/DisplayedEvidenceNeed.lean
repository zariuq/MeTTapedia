import Mettapedia.GSLT.Dynamics.ProofRelevantNeed
import Mettapedia.TypeTheory.DisplayedEvidence

/-!
# Call-by-need cells indexed by displayed exact evidence

A nondependent lazy cell stores one fixed value type independently of the
origin it records.  Dependent evidence needs a stronger invariant: cached
evidence or a cached refutation must inhabit the family indexed by that exact
raw origin.

This module defines the indexed refinement and maps it to the existing
proof-relevant need protocol by packing each dependent payload with its raw
index.  Every indexed step becomes an ordinary need step.  The converse is
not automatic: the ordinary protocol can commit a packed value whose index
does not match the cell origin.  A concrete negative control proves that such
a state and transition lie outside the indexed image.

The evidence view forgets whether a suspended cell is currently owned by an
evaluator.  Every indexed protocol step either allocates that view or refines
it monotonically from suspension to exact evidence or exact refutation.
Evaluation ownership therefore remains operational evidence rather than part
of gradual type precision.

No evaluator, forcing policy, revision discipline, or surface language is
selected here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedEvidenceNeed

open Mettapedia.GSLT.Dynamics
open Mettapedia.TypeTheory.DisplayedEvidence

universe uRaw uExact uReason uCell uRetryable

variable (family : Family.{uRaw, uExact}) (Reason : Type uReason)

/-! ## Indexed states and events -/

/-- A lazy cell whose cached payload is indexed by the exact raw origin. -/
inductive CellState where
  | absent
  | suspended (raw : family.Raw)
  | evaluating (raw : family.Raw)
  | cachedEvidence (raw : family.Raw) (evidence : family.Exact raw)
  | cachedRefutation (raw : family.Raw)
      (obstruction : Refutation family Reason raw)

/-- Exact events of the indexed cell protocol. -/
inductive Event (Cell : Type uCell) (RetryableFault : Type uRetryable) where
  | allocate (cell : Cell) (raw : family.Raw)
  | resample (source fresh : Cell) (raw : family.Raw)
  | beginEvaluation (cell : Cell) (raw : family.Raw)
  | commitEvidence (cell : Cell) (raw : family.Raw)
      (evidence : family.Exact raw)
  | commitRefutation (cell : Cell) (raw : family.Raw)
      (obstruction : Refutation family Reason raw)
  | retry (cell : Cell) (raw : family.Raw) (fault : RetryableFault)
  | observeEvidence (cell : Cell) (raw : family.Raw)
      (evidence : family.Exact raw)
  | observeRefutation (cell : Cell) (raw : family.Raw)
      (obstruction : Refutation family Reason raw)
  | inspectRaw (cell : Cell) (raw : family.Raw)

/-- Proof-relevant transitions of one indexed cell.  A commit constructor can
only mention evidence in the fibre selected by the current raw origin. -/
inductive Step (Cell : Type uCell) (RetryableFault : Type uRetryable)
    (cell : Cell) :
    CellState family Reason -> Event family Reason Cell RetryableFault ->
      CellState family Reason -> Type _ where
  | allocate (raw : family.Raw) :
      Step Cell RetryableFault cell .absent (.allocate cell raw)
        (.suspended raw)
  | resample (source : Cell) (raw : family.Raw)
      (fresh : source = cell -> False) :
      Step Cell RetryableFault cell .absent (.resample source cell raw)
        (.suspended raw)
  | beginEvaluation (raw : family.Raw) :
      Step Cell RetryableFault cell (.suspended raw)
        (.beginEvaluation cell raw) (.evaluating raw)
  | commitEvidence (raw : family.Raw) (evidence : family.Exact raw) :
      Step Cell RetryableFault cell (.evaluating raw)
        (.commitEvidence cell raw evidence) (.cachedEvidence raw evidence)
  | commitRefutation (raw : family.Raw)
      (obstruction : Refutation family Reason raw) :
      Step Cell RetryableFault cell (.evaluating raw)
        (.commitRefutation cell raw obstruction)
        (.cachedRefutation raw obstruction)
  | retry (raw : family.Raw) (fault : RetryableFault) :
      Step Cell RetryableFault cell (.evaluating raw)
        (.retry cell raw fault) (.suspended raw)
  | observeEvidence (raw : family.Raw) (evidence : family.Exact raw) :
      Step Cell RetryableFault cell (.cachedEvidence raw evidence)
        (.observeEvidence cell raw evidence) (.cachedEvidence raw evidence)
  | observeRefutation (raw : family.Raw)
      (obstruction : Refutation family Reason raw) :
      Step Cell RetryableFault cell (.cachedRefutation raw obstruction)
        (.observeRefutation cell raw obstruction)
        (.cachedRefutation raw obstruction)
  | inspectSuspended (raw : family.Raw) :
      Step Cell RetryableFault cell (.suspended raw) (.inspectRaw cell raw)
        (.suspended raw)
  | inspectEvaluating (raw : family.Raw) :
      Step Cell RetryableFault cell (.evaluating raw) (.inspectRaw cell raw)
        (.evaluating raw)
  | inspectEvidence (raw : family.Raw) (evidence : family.Exact raw) :
      Step Cell RetryableFault cell (.cachedEvidence raw evidence)
        (.inspectRaw cell raw) (.cachedEvidence raw evidence)
  | inspectRefutation (raw : family.Raw)
      (obstruction : Refutation family Reason raw) :
      Step Cell RetryableFault cell (.cachedRefutation raw obstruction)
        (.inspectRaw cell raw) (.cachedRefutation raw obstruction)

/-! ## Erasure into the ordinary proof-relevant need protocol -/

/-- Pack exact evidence together with the raw index whose fibre it inhabits. -/
abbrev PackedEvidence := Sigma family.Exact

/-- Pack a stable refutation with the raw index it refutes. -/
abbrev PackedRefutation :=
  Sigma fun raw => Refutation family Reason raw

/-- Forget the dependent state invariant while retaining the index in each
cached payload. -/
def toNeedState : CellState family Reason ->
    ProofRelevantNeed.CellState family.Raw (PackedEvidence family)
      (PackedRefutation family Reason)
  | .absent => .absent
  | .suspended raw => .suspended raw
  | .evaluating raw => .evaluating raw
  | .cachedEvidence raw evidence => .cachedValue raw ⟨raw, evidence⟩
  | .cachedRefutation raw obstruction =>
      .cachedStableFault raw ⟨raw, obstruction⟩

/-- Map every indexed event to the corresponding ordinary need event. -/
def Event.toNeed
    {Cell : Type uCell} {RetryableFault : Type uRetryable} :
    Event family Reason Cell RetryableFault ->
      ProofRelevantNeed.Event Cell family.Raw (PackedEvidence family)
        (PackedRefutation family Reason) RetryableFault
  | .allocate cell raw => .allocate cell raw
  | .resample source fresh raw => .resample source fresh raw
  | .beginEvaluation cell raw => .beginEvaluation cell raw
  | .commitEvidence cell raw evidence =>
      .commitValue cell raw ⟨raw, evidence⟩
  | .commitRefutation cell raw obstruction =>
      .commitStableFault cell raw ⟨raw, obstruction⟩
  | .retry cell raw fault => .retry cell raw fault
  | .observeEvidence cell raw evidence =>
      .observeValue cell raw ⟨raw, evidence⟩
  | .observeRefutation cell raw obstruction =>
      .observeStableFault cell raw ⟨raw, obstruction⟩
  | .inspectRaw cell raw => .inspectOrigin cell raw

/-- Every indexed step is an ordinary proof-relevant need step after packing
its dependent payload. -/
def Step.toNeed
    {Cell : Type uCell} {RetryableFault : Type uRetryable} {cell : Cell}
    {source target : CellState family Reason}
    {event : Event family Reason Cell RetryableFault}
    (step : Step family Reason Cell RetryableFault cell source event target) :
    ProofRelevantNeed.Step RetryableFault cell
      (toNeedState family Reason source)
      (event.toNeed family Reason) (toNeedState family Reason target) := by
  cases step with
  | allocate raw => exact .allocate raw
  | resample source raw fresh => exact .resample source raw fresh
  | beginEvaluation raw => exact .beginEvaluation raw
  | commitEvidence raw evidence =>
      exact .commitValue raw
        (Sigma.mk raw evidence : PackedEvidence family)
  | commitRefutation raw obstruction =>
      exact .commitStableFault raw
        (Sigma.mk raw obstruction : PackedRefutation family Reason)
  | retry raw fault => exact .retry raw fault
  | observeEvidence raw evidence =>
      exact .observeValue raw
        (Sigma.mk raw evidence : PackedEvidence family)
  | observeRefutation raw obstruction =>
      exact .observeStableFault raw
        (Sigma.mk raw obstruction : PackedRefutation family Reason)
  | inspectSuspended raw => exact .inspectSuspended raw
  | inspectEvaluating raw => exact .inspectEvaluating raw
  | inspectEvidence raw evidence =>
      exact .inspectValue raw
        (Sigma.mk raw evidence : PackedEvidence family)
  | inspectRefutation raw obstruction =>
      exact .inspectStableFault raw
        (Sigma.mk raw obstruction : PackedRefutation family Reason)

/-! ## Displayed-evidence observation -/

/-- The gradual evidence view of a cell.  Evaluation ownership is deliberately
invisible: suspended and evaluating states have the same evidence status. -/
def evidenceView : CellState family Reason ->
    Option (Sigma fun raw => Status family Reason raw)
  | .absent => none
  | .suspended raw => some ⟨raw, .suspended⟩
  | .evaluating raw => some ⟨raw, .suspended⟩
  | .cachedEvidence raw evidence => some ⟨raw, .established evidence⟩
  | .cachedRefutation raw obstruction => some ⟨raw, .refuted obstruction⟩

/-- A view change either allocates a new suspended index or increases exact
evidence precision at the same index. -/
inductive ViewChange :
    Option (Sigma fun raw => Status family Reason raw) ->
      Option (Sigma fun raw => Status family Reason raw) -> Prop where
  | allocate (raw : family.Raw) :
      ViewChange none (some ⟨raw, .suspended⟩)
  | refine {raw : family.Raw}
      {precise coarse : Status family Reason raw}
      (precision : Status.Refines precise coarse) :
      ViewChange (some ⟨raw, coarse⟩) (some ⟨raw, precise⟩)

/-- Every indexed need step is monotone for the displayed-evidence view.
Beginning evaluation changes ownership but not precision; commits refine a
suspension; retry, observation, and inspection preserve precision. -/
theorem Step.evidenceView_change
    {Cell : Type uCell} {RetryableFault : Type uRetryable} {cell : Cell}
    {source target : CellState family Reason}
    {event : Event family Reason Cell RetryableFault}
    (step : Step family Reason Cell RetryableFault cell source event target) :
    ViewChange family Reason (evidenceView family Reason source)
      (evidenceView family Reason target) := by
  cases step with
  | allocate raw => exact .allocate raw
  | resample source raw fresh => exact .allocate raw
  | beginEvaluation raw => exact .refine (.refl .suspended)
  | commitEvidence raw evidence =>
      exact .refine (.established_suspended evidence)
  | commitRefutation raw obstruction =>
      exact .refine (.refuted_suspended obstruction)
  | retry raw fault => exact .refine (.refl .suspended)
  | observeEvidence raw evidence => exact .refine (.refl _)
  | observeRefutation raw obstruction => exact .refine (.refl _)
  | inspectSuspended raw => exact .refine (.refl .suspended)
  | inspectEvaluating raw => exact .refine (.refl .suspended)
  | inspectEvidence raw evidence => exact .refine (.refl _)
  | inspectRefutation raw obstruction => exact .refine (.refl _)

/-- The evidence view cannot reconstruct evaluation ownership. -/
theorem evidenceView_not_injective (raw : family.Raw) :
    Not (Function.Injective (evidenceView family Reason)) := by
  intro injective
  have sameView :
      evidenceView family Reason (.suspended raw) =
        evidenceView family Reason (.evaluating raw) := rfl
  have sameState := injective sameView
  cases sameState

/-! ## Positive and adversarial controls -/

namespace Canary

/-- A simple indexed family for which both Boolean origins carry one exact
witness. -/
def booleanUnit : Family.{0, 0} where
  Raw := Bool
  Exact := fun _ => PUnit

abbrev PackedBooleanEvidence := PackedEvidence booleanUnit
abbrev PackedBooleanRefutation : Type :=
  PackedRefutation booleanUnit Empty

def mismatchedPacked : PackedBooleanEvidence :=
  Sigma.mk true PUnit.unit

def matchingPacked : PackedBooleanEvidence :=
  Sigma.mk false PUnit.unit

/-- The ordinary nondependent protocol can commit a packed witness whose
internal index is `true` into a cell whose origin is `false`. -/
def mismatchedNeedCommit :
    ProofRelevantNeed.Step Empty ()
      (ProofRelevantNeed.CellState.evaluating false)
      (.commitValue () false mismatchedPacked)
      (.cachedValue false mismatchedPacked :
        ProofRelevantNeed.CellState Bool PackedBooleanEvidence
          PackedBooleanRefutation) :=
  @ProofRelevantNeed.Step.commitValue
    Unit Bool PackedBooleanEvidence PackedBooleanRefutation Empty
    () false mismatchedPacked

/-- That mismatched cached state is outside the image of the indexed state
refinement. -/
theorem mismatchedNeedState_not_in_image :
    Not (Exists fun state : CellState booleanUnit Empty =>
      toNeedState booleanUnit Empty state =
        (ProofRelevantNeed.CellState.cachedValue false
          mismatchedPacked :
          ProofRelevantNeed.CellState Bool PackedBooleanEvidence
            PackedBooleanRefutation)) := by
  rintro ⟨state, equalState⟩
  cases state with
  | absent => cases equalState
  | suspended raw => cases equalState
  | evaluating raw => cases equalState
  | cachedEvidence raw evidence =>
      have equalOrigin : raw = false := by
        injection equalState
      have equalPacked : (Sigma.mk raw evidence : PackedBooleanEvidence) =
          mismatchedPacked := by
        injection equalState
      have rawTrue : raw = true := congrArg Sigma.fst equalPacked
      exact Bool.false_ne_true (equalOrigin.symm.trans rawTrue)
  | cachedRefutation raw obstruction => cases equalState

/-- A matching indexed commit maps to the corresponding ordinary need step. -/
def matchingIndexedCommit :
    Step booleanUnit Empty Unit Empty ()
      (.evaluating false)
      (.commitEvidence () false PUnit.unit)
      (.cachedEvidence false PUnit.unit) :=
  @Step.commitEvidence booleanUnit Empty Unit Empty () false PUnit.unit

theorem matchingIndexedCommit_maps_to_need :
    matchingIndexedCommit.toNeed =
      (ProofRelevantNeed.Step.commitValue false
        matchingPacked :
        ProofRelevantNeed.Step Empty ()
          (ProofRelevantNeed.CellState.evaluating false)
          (.commitValue () false matchingPacked)
          (.cachedValue false matchingPacked)) :=
  rfl

/-- Positive and negative boundary: matching dependent evidence embeds in the
ordinary protocol, while its mismatched ordinary sibling is not representable
by any indexed state. -/
theorem indexed_need_boundary :
    Nonempty
        (Step booleanUnit Empty Unit Empty ()
          (.evaluating false)
          (.commitEvidence () false PUnit.unit)
          (.cachedEvidence false PUnit.unit)) /\
      Not (Exists fun state : CellState booleanUnit Empty =>
        toNeedState booleanUnit Empty state =
          (ProofRelevantNeed.CellState.cachedValue false
            mismatchedPacked :
            ProofRelevantNeed.CellState Bool PackedBooleanEvidence
              PackedBooleanRefutation)) :=
  ⟨⟨matchingIndexedCommit⟩, mismatchedNeedState_not_in_image⟩

end Canary

#print axioms Step.toNeed
#print axioms Step.evidenceView_change
#print axioms evidenceView_not_injective
#print axioms Canary.mismatchedNeedState_not_in_image
#print axioms Canary.matchingIndexedCommit_maps_to_need
#print axioms Canary.indexed_need_boundary

end Mettapedia.TypeTheory.DisplayedEvidenceNeed
