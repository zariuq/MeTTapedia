import Mettapedia.KR.ConceptGeometry.Bridges.ProbabilityTheory.EmpiricalIntensionalFactorGraphBridge
import Mettapedia.KR.ConceptOntology.Formation
import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility

/-!
# Formed Concept ↔ Fixpoint Closure Bridge

This module connects the new public formed-concept inheritance surface to the
generic WM fixpoint-closure calculus.

The bridge is intentionally narrow:

- formed concepts contribute a supported exact extensional inheritance slice,
- an external query encoding may expose that slice to a `BinaryWorldModel`,
- least-rule closure then transports threshold obligations over those queries.

This gives the first honest preservation theorem saying that exact
formed-concept inheritance obligations survive WM consequence closure.
-/

namespace Mettapedia.PLN.Bridges.KR.ConceptClosure.FormedConceptFixpointClosureBridge

open Mettapedia.KR.ConceptGeometry
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
open Mettapedia.Hyperseed
open scoped ENNReal

universe u v w x y

section FormedConceptClosure

variable {State : Type u} {Query : Type v} {Obj : Type w} {Attr : Type x} {Q : Type y}
variable [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State] [BinaryWorldModel State Query]
variable [Preorder Q] [Fintype Obj] [Nonempty Obj] [Fintype Attr]

/-- A seed family of formed-concept inheritance obligations, viewed as ordered
pairs of subconcept and superconcept. -/
abbrev FormedConceptPair
    (G : _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q) :=
  AbstractInheritance.FormedConcept G M × AbstractInheritance.FormedConcept G M

/-- Query set obtained by encoding a seed family of formed-concept inheritance
obligations into a world-model query language. -/
def formedConceptQuerySet
    (G : _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M → Query)
    (seed : Set (FormedConceptPair G M)) :
    Set Query :=
  { q | ∃ p : FormedConceptPair G M, p ∈ seed ∧ q = encode p.1 p.2 }

omit [Nonempty Obj] in
@[simp] theorem mem_formedConceptQuerySet_iff
    (G : _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M → Query)
    (seed : Set (FormedConceptPair G M))
    (q : Query) :
    q ∈ formedConceptQuerySet G M encode seed ↔
      ∃ p : FormedConceptPair G M, p ∈ seed ∧ q = encode p.1 p.2 := by
  rfl

/-- If a query encoding exposes the supported formed-concept extensional slice
at strength level, and every seed obligation is above threshold according to
the exact generated-table semantics, then the encoded seed query set is
threshold-valid in the world model. -/
theorem thresholdValid_formedConceptQuerySet_of_exactTableStrength
    (G : _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M → Query)
    (seed : Set (FormedConceptPair G M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (IntensionalInheritance.Interpretation.finiteInheritanceStrength
              (AbstractInheritance.formedConceptInterpretation G M)
              subConcept superConcept))
    (hSeed :
      ∀ p : FormedConceptPair G M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
            (IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
              G M p.1 p.2))) :
    thresholdValid (State := State) (Query := Query) W τ
      (formedConceptQuerySet G M encode seed) := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  have hExact :
      IntensionalInheritance.Interpretation.finiteInheritanceStrength
          (AbstractInheritance.formedConceptInterpretation G M) p.1 p.2 =
        IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
          (IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
            G M p.1 p.2) :=
    (IntensionalInheritance.AbstractInheritance.formedConceptInheritance_exact_via_table
      (G := G) (M := M) p.1 p.2).2.1
  have hSeed' :
      τ ≤ ENNReal.ofReal
        (IntensionalInheritance.Interpretation.finiteInheritanceStrength
          (AbstractInheritance.formedConceptInterpretation G M) p.1 p.2) := by
    simpa [hExact.symm] using hSeed p hp
  simpa [hEncode p.1 p.2] using hSeed'

/-- The same exact formed-concept seed obligations remain threshold-valid after
closing under any state-indexed WM consequence rule set. -/
theorem leastRuleClosure_thresholdValid_of_exactTableStrength
    (R : RuleSet State Query)
    (G : _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M → Query)
    (seed : Set (FormedConceptPair G M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (IntensionalInheritance.Interpretation.finiteInheritanceStrength
              (AbstractInheritance.formedConceptInterpretation G M)
              subConcept superConcept))
    (hSeed :
      ∀ p : FormedConceptPair G M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
            (IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
              G M p.1 p.2))) :
    thresholdValid (State := State) (Query := Query) W τ
      (leastRuleClosure (State := State) (Query := Query) R W
        (formedConceptQuerySet G M encode seed)) := by
  apply leastRuleClosure_thresholdValid
  exact thresholdValid_formedConceptQuerySet_of_exactTableStrength
    (State := State) (Query := Query) G M W τ encode seed hEncode hSeed

section Admissibility

variable {Signal : Type*} {Cost : Type*} [Preorder Cost]

/-- If the available region is covered by the least WM closure of exact
formed-concept inheritance obligations, then every available query becomes
WM-admissible at threshold `τ`. -/
theorem availableRegionAt_subset_wmAdmissibleRegionAt_of_exactTableStrength
    (P : StatefulPerspective State Query Signal Cost)
    (R : RuleSet State Query)
    (G : _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M → Query)
    (seed : Set (FormedConceptPair G M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (IntensionalInheritance.Interpretation.finiteInheritanceStrength
              (AbstractInheritance.formedConceptInterpretation G M)
              subConcept superConcept))
    (hSeed :
      ∀ p : FormedConceptPair G M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
            (IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
              G M p.1 p.2)))
    (hAvail :
      availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (formedConceptQuerySet G M encode seed)) :
    availableRegionAt P W B guard ⊆
      Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Query) P W B guard τ := by
  apply Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.availableRegionAt_subset_wmAdmissibleRegionAt_of_thresholdValid
    (S := leastRuleClosure (State := State) (Query := Query) R W
      (formedConceptQuerySet G M encode seed))
  · exact leastRuleClosure_thresholdValid_of_exactTableStrength
      (State := State) (Query := Query) R G M W τ encode seed hEncode hSeed
  · exact hAvail

/-- If the available region is exactly covered by the least WM closure of exact
formed-concept inheritance obligations, the admissible region collapses back to
the available region. -/
theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_exactTableStrength
    (P : StatefulPerspective State Query Signal Cost)
    (R : RuleSet State Query)
    (G : _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M → Query)
    (seed : Set (FormedConceptPair G M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (IntensionalInheritance.Interpretation.finiteInheritanceStrength
              (AbstractInheritance.formedConceptInterpretation G M)
              subConcept superConcept))
    (hSeed :
      ∀ p : FormedConceptPair G M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
            (IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
              G M p.1 p.2)))
    (hAvail :
      availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (formedConceptQuerySet G M encode seed)) :
    Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Query) P W B guard τ =
      availableRegionAt P W B guard := by
  apply Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt_eq_availableRegionAt_of_thresholdValid
  exact thresholdValid_mono
    (State := State) (Query := Query) (W := W) (τ := τ)
    hAvail
    (leastRuleClosure_thresholdValid_of_exactTableStrength
      (State := State) (Query := Query) R G M W τ encode seed hEncode hSeed)

end Admissibility

end FormedConceptClosure

end Mettapedia.PLN.Bridges.KR.ConceptClosure.FormedConceptFixpointClosureBridge
