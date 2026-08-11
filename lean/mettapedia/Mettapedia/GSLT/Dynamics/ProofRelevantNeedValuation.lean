import Mettapedia.GSLT.Dynamics.IndexedEventValuation
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedSharing

/-!
# Cost, evidence, and provenance over exact Need events

The Need cell protocol determines which event occurred.  Valuations are
independent observers of that event stream: adding or erasing a valuation does
not add a protocol edge.  Each axis selects its own partial monoid, and axes
compose by product without conflating execution cost, evidence, provenance,
or attention.
-/

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed

open Mettapedia.GSLT.Dynamics.IndexedEventValuation

universe uCell uOrigin uValue uStableFault uRetryableFault uGrade

namespace Trace

variable {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
  {StableFault : Type uStableFault}
  {RetryableFault : Type uRetryableFault} {cell : Cell}

/-- Value an exact chronological trace without changing its endpoints or
protocol evidence. -/
def grade
    (valuation : Valuation
      (Event Cell Origin Value StableFault RetryableFault))
    {source target : CellState Origin Value StableFault}
    (trace : Trace RetryableFault cell source target) :
    Option valuation.Grade :=
  valuation.historyGrade trace.events

/-- Trace valuation composes in exactly the same order as trace composition. -/
theorem grade_trans
    (valuation : Valuation
      (Event Cell Origin Value StableFault RetryableFault))
    {source middle target : CellState Origin Value StableFault}
    (first : Trace RetryableFault cell source middle)
    (second : Trace RetryableFault cell middle target) :
    (first.trans second).grade valuation =
      (first.grade valuation).bind fun left =>
        (second.grade valuation).bind fun right =>
          valuation.algebra.op left right := by
  unfold grade
  rw [events_trans, Valuation.historyGrade_append]

end Trace

/-- Charge one unit exactly when a suspension claims evaluation ownership. -/
abbrev evaluationWorkValuation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault} :
    Valuation (Event Cell Origin Value StableFault RetryableFault) :=
  additive Event.evaluationCount

/-- Count cached outcome observations independently of evaluation work. -/
abbrev outcomeObservationValuation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault} :
    Valuation (Event Cell Origin Value StableFault RetryableFault) :=
  additive Event.outcomeObservationCount

/-- Count non-forcing origin inspections independently of outcome demands. -/
abbrev inspectionValuation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault} :
    Valuation (Event Cell Origin Value StableFault RetryableFault) :=
  additive Event.inspectionCount

/-- Retain the chronological operator provenance of every event. -/
abbrev operatorHistoryValuation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault} :
    Valuation (Event Cell Origin Value StableFault RetryableFault) :=
  chronological Event.operation

theorem operatorHistoryValuation_isTotal
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault} :
    (operatorHistoryValuation :
      Valuation (Event Cell Origin Value StableFault RetryableFault)).IsTotal :=
  chronological_isTotal Event.operation

/-- The non-provenance structural coordinates.  Naming this product makes the
provenance erasure law explicit rather than relying on tuple projection by
convention. -/
abbrev structuralBaseValuation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault} :
    Valuation (Event Cell Origin Value StableFault RetryableFault) :=
  (evaluationWorkValuation.prod outcomeObservationValuation).prod
    inspectionValuation

/-- The standard structural observation keeps work, cached observations,
inspections, and operator provenance as four independent coordinates. -/
abbrev structuralValuation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault} :
    Valuation (Event Cell Origin Value StableFault RetryableFault) :=
  structuralBaseValuation.prod operatorHistoryValuation

/-- A valuation on the maximal event family restricts mechanically to any
selected operator fragment. -/
def restrictValuation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault}
    (operators : OperatorSet)
    (valuation : Valuation
      (Event Cell Origin Value StableFault RetryableFault)) :
    Valuation
      (AdmittedEvent operators Cell Origin Value StableFault RetryableFault) :=
  valuation.pullback Subtype.val

/-- A language-specific evidence or PLN valuation can select an arbitrary
partial algebra.  Undefined event grades or incompatible compositions fail
closed as `none`. -/
def evidenceValuation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault}
    (Grade : Type uGrade) (algebra : Mettapedia.GSLT.PartialMonoid Grade)
    (evidence : Event Cell Origin Value StableFault RetryableFault ->
      Option Grade) :
    Valuation (Event Cell Origin Value StableFault RetryableFault) where
  Grade := Grade
  algebra := algebra
  grade := evidence

/-! ## Positive and negative canaries -/

namespace ValuationCanary

open Canary

theorem successful_work_grade :
    successfulTrace.grade evaluationWorkValuation = some 1 := by
  decide

theorem retry_work_grade :
    retryTrace.grade evaluationWorkValuation = some 2 := by
  decide

theorem successful_structural_grade :
    successfulTrace.grade structuralValuation =
      some (((1, 1), 1),
        [Operation.allocate, Operation.beginEvaluation, Operation.commitValue,
          Operation.observeValue, Operation.inspectOrigin]) := by
  decide

/-- Provenance is a total coordinate, so erasing it recovers the other
structural grades exactly; it cannot reject an otherwise accepted trace. -/
theorem provenance_erasure_recovers_structural_base :
    Option.map Prod.fst (successfulTrace.grade structuralValuation) =
      successfulTrace.grade structuralBaseValuation := by
  exact Valuation.map_fst_prod_historyGrade_of_right_total
    structuralBaseValuation operatorHistoryValuation
    operatorHistoryValuation_isTotal successfulTrace.events

/-- Endpoint equality alone still cannot recover the chosen valuation:
inspection and cached observation are different equal-endpoint events. -/
theorem equal_endpoints_have_distinct_structural_grades :
    structuralValuation.grade
        (Event.observeValue (Cell := Nat) (Origin := Nat) (Value := Nat)
          (StableFault := Nat) (RetryableFault := Nat) 0 7 11) ≠
      structuralValuation.grade (Event.inspectOrigin (Cell := Nat)
        (Value := Nat) (StableFault := Nat) (RetryableFault := Nat) 0 7) := by
  decide

end ValuationCanary

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed
