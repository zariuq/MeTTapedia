import Mettapedia.KR.ConceptOntology.CredalFormation
import Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence
import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility

/-!
# Credal Lower-Formed Concept ↔ Full-Inheritance Fixpoint Closure Bridge

This module is the full-strength analogue of
`CredalConceptFixpointClosureBridge`.

The older bridge transports the exact extensional proxy already present in the
generated-table infrastructure. This file instead transports the new
`fullInheritanceStrength` directly through the same WM fixpoint-closure
calculus, so credal concept formation can drive closure/admissibility results
without collapsing back to the older extensional-only slice.
-/

namespace Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge

open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
open Mettapedia.Hyperseed
open scoped ENNReal

universe u v w x y z

section LowerFormedConceptClosure

variable {State : Type u} {Query : Type v} {Obj : Type w} {Attr : Type x}
variable {Q : Type y} {Gate : Type z}
variable [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State] [BinaryWorldModel State Query]
variable [Preorder Q] [Fintype Obj] [Fintype Attr]

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

/-- If a query encoding exposes the supported robust lower-formed inheritance
slice at the new full-strength level, and every seed obligation is already
above threshold in that exact full-strength semantics, then the encoded seed
query set is threshold-valid in the world model. -/
theorem thresholdValid_lowerFormedConceptQuerySet_of_exactFullInheritanceStrength
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
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) :
    thresholdValid (State := State) (Query := Query) W τ
      (lowerFormedConceptQuerySet Γ M encode seed) := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  simpa [hEncode p.1 p.2] using hSeed p hp

/-- The same exact robust seed obligations remain threshold-valid after
closing under any state-indexed WM consequence rule set. -/
theorem leastRuleClosure_thresholdValid_of_exactFullInheritanceStrength
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
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) :
    thresholdValid (State := State) (Query := Query) W τ
      (leastRuleClosure (State := State) (Query := Query) R W
        (lowerFormedConceptQuerySet Γ M encode seed)) := by
  apply leastRuleClosure_thresholdValid
  exact thresholdValid_lowerFormedConceptQuerySet_of_exactFullInheritanceStrength
    (State := State) (Query := Query) Γ M W τ encode seed hEncode hSeed

section Admissibility

variable {Signal : Type*} {Cost : Type*} [Preorder Cost]

/-- If the available region is covered by the least WM closure of exact robust
lower-formed full-inheritance obligations, then every available query becomes
WM-admissible at threshold `τ`. -/
theorem availableRegionAt_subset_wmAdmissibleRegionAt_of_exactFullInheritanceStrength
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
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2))
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
  · exact leastRuleClosure_thresholdValid_of_exactFullInheritanceStrength
      (State := State) (Query := Query) R Γ M W τ encode seed hEncode hSeed
  · exact hAvail

/-- If the available region is exactly covered by the least WM closure of
exact robust lower-formed full-inheritance obligations, the admissible region
collapses back to the available region. -/
theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_exactFullInheritanceStrength
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
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2))
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
    (leastRuleClosure_thresholdValid_of_exactFullInheritanceStrength
      (State := State) (Query := Query) R Γ M W τ encode seed hEncode hSeed)

end Admissibility

end LowerFormedConceptClosure

end Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge
