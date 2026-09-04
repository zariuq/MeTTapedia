import Mettapedia.Evidence.SourceScoped
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency

/-!
# Source separation is not stochastic independence

Finite source scopes answer a provenance question: did two packets reuse the
same recorded source occurrence?  Stochastic independence answers a semantic
question in a probability space: do the events denoted by two packets
factorize?  Neither question determines the other without a declared
realization from source records to random events.

The negative control below gives two packets disjoint source labels while both
denote the same nontrivial fair event.  Their provenance is source-independent,
but their events are not probabilistically independent.  The positive control
uses the product-coordinate realization from `PLNMultiPathDependency`: packets
supported by different Bernoulli coordinates then do denote independent
events.

This is the precise boundary needed by provenance-aware PLN.  A disjoint-stamp
check licenses non-reuse bookkeeping.  Product rules additionally require a
probabilistic realization theorem, a Bayesian-network separation certificate,
or another explicit stochastic-independence authority.
-/

set_option autoImplicit false

namespace Mettapedia.Evidence.SourceScopeProbabilityBoundary

open MeasureTheory ProbabilityTheory
open Mettapedia.Evidence
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency

noncomputable section

/-- Evidence metadata paired with its independently declared semantic event.
The source scope does not define the event. -/
structure EventPacket where
  sourceScope : Finset Nat
  event : Set (Nat -> Bool)

instance : SourceScoped EventPacket Nat where
  sourceScope := EventPacket.sourceScope

/-- Every coordinate in the controls is a fair Bernoulli source. -/
def fairProbability (_source : Nat) : NNReal := 1 / 2

theorem fairProbability_le_one (source : Nat) : fairProbability source <= 1 := by
  norm_num [fairProbability]

abbrev fairWorldMeasure : Measure (Nat -> Bool) :=
  infiniteFactMeasure fairProbability fairProbability_le_one

/-- A common latent event that two differently labelled reports may both
describe. -/
def commonLatentEvent : Set (Nat -> Bool) := sourceEvent {2}

def correlatedLeft : EventPacket :=
  { sourceScope := {0}
    event := commonLatentEvent }

def correlatedRight : EventPacket :=
  { sourceScope := {1}
    event := commonLatentEvent }

/-- The retained provenance records no reused occurrence. -/
theorem correlated_packets_sourceIndependent :
    SourceScoped.Independent correlatedLeft correlatedRight := by
  decide

theorem commonLatentEvent_measurable : MeasurableSet commonLatentEvent := by
  exact sourceEvent_measurable {2}

theorem fairWorldMeasure_commonLatentEvent :
    fairWorldMeasure commonLatentEvent = (1 / 2 : ENNReal) := by
  change (infiniteFactMeasure fairProbability fairProbability_le_one)
    (sourceEvent {2}) = (1 / 2 : ENNReal)
  rw [sourceEvent_measure]
  norm_num [fairProbability]

/-- Negative control: disjoint provenance labels do not force stochastic
independence.  Here both packets denote the same fair event, whose probability
is `1/2` rather than its square `1/4`. -/
theorem correlated_packets_not_stochasticallyIndependent :
    Not (_root_.ProbabilityTheory.IndepSet
      correlatedLeft.event correlatedRight.event fairWorldMeasure) := by
  intro independent
  have factorization :=
    (_root_.ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
      commonLatentEvent_measurable commonLatentEvent_measurable
      fairWorldMeasure).mp independent
  change fairWorldMeasure (commonLatentEvent ∩ commonLatentEvent) =
      fairWorldMeasure commonLatentEvent * fairWorldMeasure commonLatentEvent
    at factorization
  rw [Set.inter_self, fairWorldMeasure_commonLatentEvent] at factorization
  have realFactorization := congrArg ENNReal.toReal factorization
  norm_num at realFactorization

/-! ## Positive control: a declared product-coordinate realization -/

def productLeft : EventPacket :=
  { sourceScope := {0}
    event := sourceEvent {0} }

def productRight : EventPacket :=
  { sourceScope := {1}
    event := sourceEvent {1} }

theorem product_packets_sourceIndependent :
    SourceScoped.Independent productLeft productRight := by
  decide

/-- Under the declared independent-coordinate world model, the semantic
events corresponding to the two disjoint singleton supports are genuinely
stochastically independent. -/
theorem product_packets_stochasticallyIndependent :
    _root_.ProbabilityTheory.IndepSet
      productLeft.event productRight.event fairWorldMeasure := by
  change _root_.ProbabilityTheory.IndepSet
    (sourceEvent {0}) (sourceEvent {1}) fairWorldMeasure
  rw [_root_.ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
    (sourceEvent_measurable {0}) (sourceEvent_measurable {1})
    fairWorldMeasure]
  change fairWorldMeasure (sourceEvent {0} ∩ sourceEvent {1}) =
    fairWorldMeasure (sourceEvent {0}) * fairWorldMeasure (sourceEvent {1})
  rw [sourceEvent_inter]
  repeat' rw [sourceEvent_measure]
  norm_num [fairProbability, pow_two]

/-- The two controls together refute any model-free implication from source
separation to stochastic independence, while exhibiting one explicit model in
which such a bridge is valid. -/
theorem sourceIndependence_requires_semantic_bridge :
    SourceScoped.Independent correlatedLeft correlatedRight ∧
      Not (_root_.ProbabilityTheory.IndepSet
        correlatedLeft.event correlatedRight.event fairWorldMeasure) ∧
      SourceScoped.Independent productLeft productRight ∧
      _root_.ProbabilityTheory.IndepSet
        productLeft.event productRight.event fairWorldMeasure :=
  ⟨correlated_packets_sourceIndependent,
    correlated_packets_not_stochasticallyIndependent,
    product_packets_sourceIndependent,
    product_packets_stochasticallyIndependent⟩

#print axioms correlated_packets_sourceIndependent
#print axioms correlated_packets_not_stochasticallyIndependent
#print axioms product_packets_sourceIndependent
#print axioms product_packets_stochasticallyIndependent
#print axioms sourceIndependence_requires_semantic_bridge

end

end Mettapedia.Evidence.SourceScopeProbabilityBoundary
