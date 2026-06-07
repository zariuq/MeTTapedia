import Mettapedia.Ethics.Core
import Mettapedia.Logic.BinaryEvidence
import Mettapedia.Logic.EmpiricalIntensionalFactorGraphBridge

/-!
# Credal Value Attribution from Case Tables

Tiny reusable interface for case-driven moral-value attribution over the
uncertainty-native credal concept-formation surface.
-/

namespace Mettapedia.Ethics

open Mettapedia.Logic
open Mettapedia.Logic.ConceptOntology
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.AbstractInheritance

universe u v

deriving instance Fintype for MoralValueAttribute

/-- A direct case/value evidence table for value attribution. -/
structure CredalValueAttributionCaseTable (Case : Type u) where
  evidence : Case → MoralValueAttribute → BinaryEvidence

namespace CredalValueAttributionCaseTable

variable {Case : Type u} {Gate : Type v}
variable [Fintype Gate] [Nonempty Gate] [Fintype Case] [Nonempty Case]

/-- Lower credal concept family induced by a finite gate family. -/
def lowerConceptFamily
    (T : CredalValueAttributionCaseTable Case)
    (Γ : Gate → EvidenceGate BinaryEvidence) :
    Set (DualConcept Case MoralValueAttribute) :=
  ConceptOntology.lowerConceptFamily Γ T.evidence

/-- Upper credal concept family induced by a finite gate family. -/
def upperConceptFamily
    (T : CredalValueAttributionCaseTable Case)
    (Γ : Gate → EvidenceGate BinaryEvidence) :
    Set (DualConcept Case MoralValueAttribute) :=
  ConceptOntology.upperConceptFamily Γ T.evidence

/-- Robust lower-formed concepts induced by the case table. -/
abbrev LowerFormedConcept
    (T : CredalValueAttributionCaseTable Case)
    (Γ : Gate → EvidenceGate BinaryEvidence) :=
  ConceptOntology.LowerFormedConcept Γ T.evidence

/-- Permissive upper-formed concepts induced by the case table. -/
abbrev UpperFormedConcept
    (T : CredalValueAttributionCaseTable Case)
    (Γ : Gate → EvidenceGate BinaryEvidence) :=
  ConceptOntology.UpperFormedConcept Γ T.evidence

/-- Canonical interpretation of robust lower-formed case concepts. -/
noncomputable def lowerFormedConceptInterpretation
    (T : CredalValueAttributionCaseTable Case)
    (Γ : Gate → EvidenceGate BinaryEvidence) :
    AbstractInheritance.Interpretation (LowerFormedConcept T Γ)
      Case MoralValueAttribute :=
  ConceptOntology.lowerFormedConceptInterpretation Γ T.evidence

/-- Robust lower-formed inheritance table for case-level value attribution. -/
noncomputable def lowerInheritanceTable
    (T : CredalValueAttributionCaseTable Case)
    (Γ : Gate → EvidenceGate BinaryEvidence)
    (subConcept superConcept : LowerFormedConcept T Γ) :
    IntensionalInheritance.FiniteWitnessFeatureTable :=
  IntensionalInheritance.lowerCredalConceptInheritanceTable Γ T.evidence
    subConcept superConcept

/- Exact robust lower-formed inheritance slice, specialized to case tables. -/
omit [Fintype Gate] [Nonempty Gate] in
theorem lowerInheritance_exact_via_table
    (T : CredalValueAttributionCaseTable Case)
    (Γ : Gate → EvidenceGate BinaryEvidence)
    (subConcept superConcept : LowerFormedConcept T Γ) :
    IntensionalInheritance.Interpretation.finiteInheritancePrior
        (lowerFormedConceptInterpretation T Γ) superConcept =
      IntensionalInheritance.FiniteWitnessFeatureTable.witnessPrior
        (lowerInheritanceTable T Γ subConcept superConcept)
    ∧
    IntensionalInheritance.Interpretation.finiteInheritanceStrength
        (lowerFormedConceptInterpretation T Γ) subConcept superConcept =
      IntensionalInheritance.FiniteWitnessFeatureTable.featureToWitnessStrength
        (lowerInheritanceTable T Γ subConcept superConcept)
    ∧
    IntensionalInheritance.Interpretation.finiteInheritanceLogRatioBits
        (lowerFormedConceptInterpretation T Γ) subConcept superConcept =
      IntensionalInheritance.FiniteWitnessFeatureTable.logRatioBits
        (lowerInheritanceTable T Γ subConcept superConcept) := by
  simpa [lowerFormedConceptInterpretation, lowerInheritanceTable] using
    IntensionalInheritance.lowerFormedConceptInheritance_exact_via_table
      (Γ := Γ) (M := T.evidence) subConcept superConcept

/-- The singleton case/value dual concept. -/
def caseValueConcept
    (c : Case) (v : MoralValueAttribute) :
    DualConcept Case MoralValueAttribute where
  extent := {c}
  intent := {v}

omit [Fintype Case] [Nonempty Case] in
@[simp] theorem caseValueConcept_extent
    (c : Case) (v : MoralValueAttribute) :
    (caseValueConcept c v).extent = ({c} : Set Case) := rfl

omit [Fintype Case] [Nonempty Case] in
@[simp] theorem caseValueConcept_intent
    (c : Case) (v : MoralValueAttribute) :
    (caseValueConcept c v).intent = ({v} : Set MoralValueAttribute) := rfl

end CredalValueAttributionCaseTable

end Mettapedia.Ethics
