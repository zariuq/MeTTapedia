import Mettapedia.GSLT.Dynamics.ProofRelevantNeedOwnership
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedValuation

/-!
# Valuations of owner-sensitive Need traces

Evaluator ownership is an optional protocol refinement.  Cost, evidence, and
provenance valuations may inspect owner-sensitive events directly, or may be
pulled back from the owner-free protocol through the proved event erasure.
Erased valuation agrees exactly with first erasing the trace and then grading
it; ownership therefore adds an independent observation axis rather than a
second cost semantics.
-/

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed.Ownership

open Mettapedia.GSLT.Dynamics.IndexedEventValuation

universe uCell uOwner uOrigin uValue uStableFault uRetryableFault

namespace Trace

variable {Cell : Type uCell} {Owner : Type uOwner} {Origin : Type uOrigin}
  {Value : Type uValue} {StableFault : Type uStableFault}
  {RetryableFault : Type uRetryableFault} {cell : Cell}

/-- Grade an owner-sensitive chronological trace with any selected
valuation. -/
def grade
    (valuation : Valuation
      (Event Cell Owner Origin Value StableFault RetryableFault))
    {source target : CellState Owner Origin Value StableFault}
    (trace : Trace RetryableFault cell source target) :
    Option valuation.Grade :=
  valuation.historyGrade trace.events

/-- Owner-sensitive trace valuation follows chronological composition. -/
theorem grade_trans
    (valuation : Valuation
      (Event Cell Owner Origin Value StableFault RetryableFault))
    {source middle target : CellState Owner Origin Value StableFault}
    (first : Trace RetryableFault cell source middle)
    (second : Trace RetryableFault cell middle target) :
    (first.trans second).grade valuation =
      (first.grade valuation).bind fun left =>
        (second.grade valuation).bind fun right =>
          valuation.algebra.op left right := by
  unfold grade
  rw [events_trans, Valuation.historyGrade_append]

/-- Pulling back a base valuation through ownership erasure agrees with
grading the erased trace. -/
theorem grade_pullback_erase
    (valuation : Valuation
      (ProofRelevantNeed.Event Cell Origin Value StableFault RetryableFault))
    {source target : CellState Owner Origin Value StableFault}
    (trace : Trace RetryableFault cell source target) :
    trace.grade (valuation.pullback eraseEvent) =
      trace.erase.grade valuation := by
  unfold grade ProofRelevantNeed.Trace.grade
  rw [Valuation.pullback_historyGrade, erase_events]

end Trace

/-- Reuse the standard structural cost/provenance observation while retaining
owner-sensitive transition evidence underneath it. -/
abbrev erasedStructuralValuation
    {Cell : Type uCell} {Owner : Type uOwner} {Origin : Type uOrigin}
    {Value : Type uValue} {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault} :
    Valuation (Event Cell Owner Origin Value StableFault RetryableFault) :=
  (ProofRelevantNeed.structuralValuation :
    Valuation
      (ProofRelevantNeed.Event Cell Origin Value StableFault RetryableFault)
  ).pullback eraseEvent

/-! ## Separating canaries -/

namespace ValuationCanary

def commitThenObserve :
    Trace (Cell := Nat) (Owner := Bool) (Origin := Nat) (Value := Nat)
      (StableFault := Nat) Nat 0 (.evaluating 7 true)
      (.cachedValue 7 11) :=
  .tail (.commitValue 0 7 true 11) (.commitValue 7 true 11)
    (.tail (.observeValue 0 7 11) (.observeValue 7 11)
      (.refl (.cachedValue 7 11)))

theorem commit_observe_structural_grade :
    commitThenObserve.grade erasedStructuralValuation =
      some (((0, 1), 0),
        [ProofRelevantNeed.Operation.commitValue,
          ProofRelevantNeed.Operation.observeValue]) := by
  decide

/-- Removing the observation changes both its count and provenance even
though both traces have the same final cache state. -/
theorem commit_only_has_different_grade :
    let commitOnly :
        Trace (Cell := Nat) (Owner := Bool) (Origin := Nat) (Value := Nat)
          (StableFault := Nat) Nat 0 (.evaluating 7 true)
          (.cachedValue 7 11) :=
      .singleton (.commitValue 0 7 true 11) (.commitValue 7 true 11)
    commitOnly.grade erasedStructuralValuation ≠
      commitThenObserve.grade erasedStructuralValuation := by
  decide

end ValuationCanary

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed.Ownership
