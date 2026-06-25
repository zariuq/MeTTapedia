import Mettapedia.KR.ConceptGeometry.Bridges.ProbabilityTheory.EmpiricalIntensionalFactorGraphBridge
import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility

/-!
# Credal Lower-Formed Concept ↔ Fixpoint Closure Bridge

This module transports the first robust credal inheritance query family through
the generic WM fixpoint-closure calculus.

The bridge stays deliberately narrow:

- the query carrier is the lower credal concept family,
- the semantic slice is the exact robust extensional inheritance strength,
- generic WM closure then preserves threshold obligations over encoded robust
  inheritance queries.
-/

namespace Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFixpointClosureBridge

open Mettapedia.KR.ConceptGeometry
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
open Mettapedia.Hyperseed
open scoped ENNReal

universe u v w x y z

section LowerFormedConceptClosure

variable {State : Type u} {Query : Type v} {Obj : Type w} {Attr : Type x}
variable {Q : Type y} {Gate : Type z}
variable [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State] [BinaryWorldModel State Query]
variable [Preorder Q] [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Nonempty Obj] [Fintype Attr]

/-- A seed family of robust credal inheritance obligations, viewed as ordered
pairs of lower formed subconcepts and superconcepts. -/
abbrev LowerFormedConceptPair
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q) :=
  _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M × _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M

/-- Query set obtained by encoding a robust credal seed family into a
world-model query language. -/
def lowerFormedConceptQuerySet
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M)) :
    Set Query :=
  { q | ∃ p : LowerFormedConceptPair Γ M, p ∈ seed ∧ q = encode p.1 p.2 }

omit [Nonempty Obj] in
omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem mem_lowerFormedConceptQuerySet_iff
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (q : Query) :
    q ∈ lowerFormedConceptQuerySet Γ M encode seed ↔
      ∃ p : LowerFormedConceptPair Γ M, p ∈ seed ∧ q = encode p.1 p.2 := by
  rfl

/- If a query encoding exposes the supported robust lower-formed extensional
inheritance slice at strength level, and every seed obligation is above
threshold according to the exact generated-table semantics, then the encoded
seed query set is threshold-valid in the world model. -/
omit [Fintype Gate] [Nonempty Gate] in
theorem thresholdValid_lowerFormedConceptQuerySet_of_exactTableStrength
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (IntensionalInheritance.Interpretation.finiteInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
            (IntensionalInheritance.lowerCredalConceptInheritanceTable
              Γ M p.1 p.2))) :
    thresholdValid (State := State) (Query := Query) W τ
      (lowerFormedConceptQuerySet Γ M encode seed) := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  have hExact :
      IntensionalInheritance.Interpretation.finiteInheritanceStrength
          (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M) p.1 p.2 =
        IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
          (IntensionalInheritance.lowerCredalConceptInheritanceTable
            Γ M p.1 p.2) :=
    (IntensionalInheritance.lowerFormedConceptInheritance_exact_via_table
      (Γ := Γ) (M := M) p.1 p.2).2.1
  have hSeed' :
      τ ≤ ENNReal.ofReal
        (IntensionalInheritance.Interpretation.finiteInheritanceStrength
          (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M) p.1 p.2) := by
    simpa [hExact.symm] using hSeed p hp
  simpa [hEncode p.1 p.2] using hSeed'

/- The same exact robust seed obligations remain threshold-valid after
closing under any state-indexed WM consequence rule set. -/
omit [Fintype Gate] [Nonempty Gate] in
theorem leastRuleClosure_thresholdValid_of_exactTableStrength
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (IntensionalInheritance.Interpretation.finiteInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
            (IntensionalInheritance.lowerCredalConceptInheritanceTable
              Γ M p.1 p.2))) :
    thresholdValid (State := State) (Query := Query) W τ
      (leastRuleClosure (State := State) (Query := Query) R W
        (lowerFormedConceptQuerySet Γ M encode seed)) := by
  apply leastRuleClosure_thresholdValid
  exact thresholdValid_lowerFormedConceptQuerySet_of_exactTableStrength
    (State := State) (Query := Query) Γ M W τ encode seed hEncode hSeed

section Admissibility

variable {Signal : Type*} {Cost : Type*} [Preorder Cost]

/- If the available region is covered by the least WM closure of exact robust
lower-formed inheritance obligations, then every available query becomes
WM-admissible at threshold `τ`. -/
omit [Fintype Gate] [Nonempty Gate] in
theorem availableRegionAt_subset_wmAdmissibleRegionAt_of_exactTableStrength
    (P : StatefulPerspective State Query Signal Cost)
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (IntensionalInheritance.Interpretation.finiteInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
            (IntensionalInheritance.lowerCredalConceptInheritanceTable
              Γ M p.1 p.2)))
    (hAvail :
      availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (lowerFormedConceptQuerySet Γ M encode seed)) :
    availableRegionAt P W B guard ⊆
      Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Query) P W B guard τ := by
  apply Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.availableRegionAt_subset_wmAdmissibleRegionAt_of_thresholdValid
    (S := leastRuleClosure (State := State) (Query := Query) R W
      (lowerFormedConceptQuerySet Γ M encode seed))
  · exact leastRuleClosure_thresholdValid_of_exactTableStrength
      (State := State) (Query := Query) R Γ M W τ encode seed hEncode hSeed
  · exact hAvail

/- If the available region is exactly covered by the least WM closure of
exact robust lower-formed inheritance obligations, the admissible region
collapses back to the available region. -/
omit [Fintype Gate] [Nonempty Gate] in
theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_exactTableStrength
    (P : StatefulPerspective State Query Signal Cost)
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (IntensionalInheritance.Interpretation.finiteInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
            (IntensionalInheritance.lowerCredalConceptInheritanceTable
              Γ M p.1 p.2)))
    (hAvail :
      availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (lowerFormedConceptQuerySet Γ M encode seed)) :
    Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Query) P W B guard τ =
      availableRegionAt P W B guard := by
  apply Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt_eq_availableRegionAt_of_thresholdValid
  exact thresholdValid_mono
    (State := State) (Query := Query) (W := W) (τ := τ)
    hAvail
    (leastRuleClosure_thresholdValid_of_exactTableStrength
      (State := State) (Query := Query) R Γ M W τ encode seed hEncode hSeed)

end Admissibility

end LowerFormedConceptClosure

end Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFixpointClosureBridge
