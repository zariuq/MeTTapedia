import Mettapedia.Logic.ConceptOntology.BenchmarkControl
import Mettapedia.Logic.ConceptOntology.CredalFormation
import Mettapedia.Logic.ConceptOntology.Generated.MizarConlat1

/-!
# Mizar Concept-Formation Benchmark

This module instantiates the benchmark-control surface on a small extracted
slice of `conlat_1.miz`.

The exact lane is tied explicitly to the classical FCA concept lattice via the
FCA recovery order isomorphism. A threshold-gate family then witnesses a real
credal split: the `ObjectDerivation` base concept is formed under the loose
gate but not robust under the stricter one.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic.AbstractInheritance
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.ConceptOntology.Generated.MizarConlat1
open scoped ENNReal

namespace MizarBenchmark

abbrev articleContext : BinaryFcaBenchmarkContext Item Attribute := context

abbrev articleThresholds : Bool → ℝ≥0∞ := thresholds

abbrev articleGateFamily : Bool → EvidenceGate BinaryEvidence := gateFamily

abbrev articleExactGate : EvidenceGate BinaryEvidence := exactGate

inductive MizarGate where
  | loose
  | strict
  deriving DecidableEq, Repr, Fintype

instance : Nonempty MizarGate := ⟨.loose⟩

def mizarGateFamily : MizarGate → EvidenceGate BinaryEvidence
  | .loose => articleExactGate
  | .strict => EvidenceGate.positiveThreshold 2

abbrev upperMizarConceptFamily :=
  upperConceptFamily mizarGateFamily articleContext.evidence

abbrev lowerMizarConceptFamily :=
  lowerConceptFamily mizarGateFamily articleContext.evidence

abbrev upperThresholdConceptFamily :=
  BinaryFcaBenchmarkContext.upperThresholdConceptFamily
    articleContext articleThresholds

abbrev lowerThresholdConceptFamily :=
  BinaryFcaBenchmarkContext.lowerThresholdConceptFamily
    articleContext articleThresholds

/-- The exact extracted Mizar context is exactly the classical FCA concept
lattice for the same article-local incidence relation. -/
noncomputable def exactOrderIso :
    AbstractInheritance.FormedConcept articleExactGate articleContext.evidence ≃o
      CrispConcept articleExactGate articleContext.evidence :=
  BinaryFcaBenchmarkContext.exactOrderIso articleContext

/-- The exact `ObjectDerivation` base concept in the extracted article context. -/
def objectDerivationLooseConcept : DualConcept Item Attribute :=
  ofCrispBaseConcept
    articleExactGate articleContext.evidence Attribute.ObjectDerivation

theorem definition_5_mem_objectDerivationLooseConcept_extent :
    Item.definition_5 ∈ objectDerivationLooseConcept.extent := by
  change Item.definition_5 ∈
    crispExtent articleExactGate articleContext.evidence
      Attribute.ObjectDerivation
  exact (mem_crispExtent_iff
    articleExactGate articleContext.evidence
    Item.definition_5 Attribute.ObjectDerivation).2 <| by
      change 1 ≤ (evidence Item.definition_5 Attribute.ObjectDerivation).pos
      simp [evidence, BinaryFcaBenchmarkContext.supportToken]

theorem objectDerivationLooseConcept_not_closed_strict :
    ¬ DualConcept.IsClosed
      (crispRelation (mizarGateFamily .strict) articleContext.evidence)
      objectDerivationLooseConcept := by
  intro hClosed
  have hObjIntent :
      Attribute.ObjectDerivation ∈ objectDerivationLooseConcept.intent := by
    simpa [objectDerivationLooseConcept] using
      self_mem_intent_ofCrispBaseConcept
        articleExactGate articleContext.evidence Attribute.ObjectDerivation
  have hObjUpper :
      Attribute.ObjectDerivation ∈
        _root_.upperPolar
          (crispRelation (mizarGateFamily .strict) articleContext.evidence)
          objectDerivationLooseConcept.extent := by
    rw [hClosed.1]
    exact hObjIntent
  have hStrict :
      crispRelation (mizarGateFamily .strict) articleContext.evidence
        Item.definition_5 Attribute.ObjectDerivation := by
    exact hObjUpper definition_5_mem_objectDerivationLooseConcept_extent
  have hNotStrict :
      ¬ crispRelation (mizarGateFamily .strict) articleContext.evidence
          Item.definition_5 Attribute.ObjectDerivation := by
    change ¬ 2 ≤ (evidence Item.definition_5 Attribute.ObjectDerivation).pos
    simp [evidence, BinaryFcaBenchmarkContext.supportToken]
  exact hNotStrict hStrict

theorem objectDerivationLooseConcept_mem_upper_raw :
    objectDerivationLooseConcept ∈
      upperMizarConceptFamily := by
  show ∃ g : MizarGate,
      objectDerivationLooseConcept ∈
        AbstractInheritance.finiteConceptFamily
          (mizarGateFamily g) articleContext.evidence
  exact ⟨.loose, by
    change objectDerivationLooseConcept ∈
      AbstractInheritance.finiteConceptFamily
        articleExactGate articleContext.evidence
    rw [mem_finiteConceptFamily_iff]
    unfold objectDerivationLooseConcept
    exact DualConcept.isClosed_ofConcept
      (crispBaseConcept
        articleExactGate articleContext.evidence Attribute.ObjectDerivation)⟩

theorem objectDerivationLooseConcept_mem_upper :
    objectDerivationLooseConcept ∈ upperMizarConceptFamily :=
  objectDerivationLooseConcept_mem_upper_raw

theorem objectDerivationLooseConcept_not_mem_strict :
    objectDerivationLooseConcept ∉
      AbstractInheritance.finiteConceptFamily
        (mizarGateFamily .strict) articleContext.evidence := by
  rw [not_mem_finiteConceptFamily_iff]
  exact objectDerivationLooseConcept_not_closed_strict

theorem objectDerivationLooseConcept_not_mem_lower :
    objectDerivationLooseConcept ∉ lowerMizarConceptFamily := by
  exact not_mem_lowerConceptFamily_of_not_mem_at
    (Γ := mizarGateFamily)
    (M := articleContext.evidence)
    (A := objectDerivationLooseConcept)
    .strict
    objectDerivationLooseConcept_not_mem_strict

theorem objectDerivationLooseConcept_width :
    (gateCredalProjectiveSpec (Gate := MizarGate)).globalEnvelopeWidth
        (conceptFormationGamble mizarGateFamily articleContext.evidence
          objectDerivationLooseConcept) = 1 := by
  have hUpper := objectDerivationLooseConcept_mem_upper
  have hNotLower := objectDerivationLooseConcept_not_mem_lower
  simpa [hUpper, hNotLower] using
    (globalEnvelopeWidth_conceptFormationGamble_eq
      (Gate := MizarGate)
      mizarGateFamily
      articleContext.evidence
      objectDerivationLooseConcept)

theorem objectDerivationLooseConcept_widthComplement :
    (gateCredalProjectiveSpec (Gate := MizarGate)).globalEnvelopeWidthComplement
        (conceptFormationGamble mizarGateFamily articleContext.evidence
          objectDerivationLooseConcept) = 0 := by
  have hUpper := objectDerivationLooseConcept_mem_upper
  have hNotLower := objectDerivationLooseConcept_not_mem_lower
  simpa [hUpper, hNotLower] using
    (globalEnvelopeWidthComplement_conceptFormationGamble_eq
      (Gate := MizarGate)
      mizarGateFamily
      articleContext.evidence
      objectDerivationLooseConcept)

theorem objectDerivationLooseConcept_midpoint :
    (gateCredalProjectiveSpec (Gate := MizarGate)).globalEnvelopeMidpoint
        (conceptFormationGamble mizarGateFamily articleContext.evidence
          objectDerivationLooseConcept) = (1 / 2 : ℝ) := by
  have hUpper := objectDerivationLooseConcept_mem_upper
  have hNotLower := objectDerivationLooseConcept_not_mem_lower
  simpa [hUpper, hNotLower] using
    (globalEnvelopeMidpoint_conceptFormationGamble_eq
      (Gate := MizarGate)
      mizarGateFamily
      articleContext.evidence
      objectDerivationLooseConcept)

end MizarBenchmark

end Mettapedia.Logic.ConceptOntology
