import Mettapedia.Logic.ConceptOntology.FCARecovery
import Mettapedia.Logic.ConceptOntology.CredalFormation

/-!
# Concept-Formation Benchmark Control

This module provides a small reusable benchmark surface for exact FCA contexts
and a tiny control dataset with both exact and credal gate variation.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic.AbstractInheritance
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

universe u v

/-- Benchmark-friendly binary evidence table for finite FCA-style contexts. -/
structure BinaryFcaBenchmarkContext (Obj : Type u) (Attr : Type v) where
  evidence : Obj → Attr → BinaryEvidence

namespace BinaryFcaBenchmarkContext

variable {Obj : Type u} {Attr : Type v}

def supportToken (n : Nat) : BinaryEvidence :=
  BinaryEvidence.mk (n : ℝ≥0∞) 0

@[simp] theorem supportToken_pos (n : Nat) :
    (supportToken n).pos = (n : ℝ≥0∞) := rfl

@[simp] theorem supportToken_neg (n : Nat) :
    (supportToken n).neg = 0 := rfl

/-- The default exact FCA gate: any positive support counts as presence. -/
def exactGate : EvidenceGate BinaryEvidence :=
  EvidenceGate.positiveThreshold 1

/-- A finite family of threshold gates, useful for credal perturbations of the
same exact observation table. -/
def thresholdGateFamily {Gate : Type} (thresholds : Gate → ℝ≥0∞) :
    Gate → EvidenceGate BinaryEvidence :=
  fun g => EvidenceGate.positiveThreshold (thresholds g)

section Exact

variable [Fintype Obj] [Fintype Attr]

/-- Exact formed-concept family induced by the benchmark context. -/
noncomputable def exactConceptFamily
    (B : BinaryFcaBenchmarkContext Obj Attr) :
    Finset (DualConcept Obj Attr) :=
  AbstractInheritance.finiteConceptFamily (Q := BinaryEvidence) exactGate B.evidence

/-- Classical FCA carrier recovered from the exact benchmark context. -/
abbrev exactCrispConcept
    (B : BinaryFcaBenchmarkContext Obj Attr) :=
  CrispConcept (Q := BinaryEvidence) exactGate B.evidence

/-- The exact benchmark lane is order-isomorphic to the classical FCA concept
lattice of the same context. -/
noncomputable def exactOrderIso
    (B : BinaryFcaBenchmarkContext Obj Attr) :
    AbstractInheritance.FormedConcept exactGate B.evidence ≃o exactCrispConcept B :=
  formedConceptOrderIsoCrispConcept (Q := BinaryEvidence) exactGate B.evidence

/-- Credal lower concept family over threshold-gate perturbations of the same
benchmark evidence table. -/
def lowerThresholdConceptFamily
    {Gate : Type} [Fintype Gate] [Nonempty Gate]
    (B : BinaryFcaBenchmarkContext Obj Attr)
    (thresholds : Gate → ℝ≥0∞) :
    Set (DualConcept Obj Attr) :=
  lowerConceptFamily (Q := BinaryEvidence) (thresholdGateFamily thresholds) B.evidence

/-- Credal upper concept family over threshold-gate perturbations of the same
benchmark evidence table. -/
def upperThresholdConceptFamily
    {Gate : Type} [Fintype Gate] [Nonempty Gate]
    (B : BinaryFcaBenchmarkContext Obj Attr)
    (thresholds : Gate → ℝ≥0∞) :
    Set (DualConcept Obj Attr) :=
  upperConceptFamily (Q := BinaryEvidence) (thresholdGateFamily thresholds) B.evidence

end Exact

end BinaryFcaBenchmarkContext

namespace ControlExample

inductive Animal where
  | robin
  | penguin
  | bat
  deriving DecidableEq, Repr, Fintype

inductive Trait where
  | winged
  | warmBlooded
  | flies
  deriving DecidableEq, Repr, Fintype

def context : BinaryFcaBenchmarkContext Animal Trait where
  evidence
    | .robin, .winged => BinaryFcaBenchmarkContext.supportToken 2
    | .robin, .warmBlooded => BinaryFcaBenchmarkContext.supportToken 2
    | .robin, .flies => BinaryFcaBenchmarkContext.supportToken 2
    | .penguin, .winged => BinaryFcaBenchmarkContext.supportToken 2
    | .penguin, .warmBlooded => BinaryFcaBenchmarkContext.supportToken 2
    | .bat, .winged => BinaryFcaBenchmarkContext.supportToken 1
    | .bat, .warmBlooded => BinaryFcaBenchmarkContext.supportToken 2
    | .bat, .flies => BinaryFcaBenchmarkContext.supportToken 1
    | _, _ => (0 : BinaryEvidence)

def thresholds : Bool → ℝ≥0∞
  | false => 1
  | true => 2

def gateFamily : Bool → EvidenceGate BinaryEvidence :=
  BinaryFcaBenchmarkContext.thresholdGateFamily thresholds

def flyingFamilyConcept : DualConcept Animal Trait where
  extent := {x | x = .robin ∨ x = .bat}
  intent := {t | t = .winged ∨ t = .warmBlooded ∨ t = .flies}

def batOnlyFlyingConcept : DualConcept Animal Trait where
  extent := {Animal.bat}
  intent := {Trait.flies}

theorem flyingFamilyConcept_closed_exact :
    DualConcept.IsClosed
      (crispRelation BinaryFcaBenchmarkContext.exactGate context.evidence)
      flyingFamilyConcept := by
  constructor
  · ext t
    cases t with
    | winged =>
        constructor
        · intro _
          simp [flyingFamilyConcept]
        · intro _ x hx
          cases x <;>
            simp [flyingFamilyConcept, crispRelation,
              BinaryFcaBenchmarkContext.exactGate, EvidenceGate.positiveThreshold,
              context, BinaryFcaBenchmarkContext.supportToken] at hx ⊢
    | warmBlooded =>
        constructor
        · intro _
          simp [flyingFamilyConcept]
        · intro _ x hx
          cases x <;>
            simp [flyingFamilyConcept, crispRelation,
              BinaryFcaBenchmarkContext.exactGate, EvidenceGate.positiveThreshold,
              context, BinaryFcaBenchmarkContext.supportToken] at hx ⊢
    | flies =>
        constructor
        · intro _
          simp [flyingFamilyConcept]
        · intro _ x hx
          cases x <;>
            simp [flyingFamilyConcept, crispRelation,
              BinaryFcaBenchmarkContext.exactGate, EvidenceGate.positiveThreshold,
              context, BinaryFcaBenchmarkContext.supportToken] at hx ⊢
  · ext a
    cases a with
    | robin =>
        constructor
        · intro _
          simp [flyingFamilyConcept]
        · intro _ t ht
          cases t <;>
            simp [flyingFamilyConcept, crispRelation,
              BinaryFcaBenchmarkContext.exactGate, EvidenceGate.positiveThreshold,
              context, BinaryFcaBenchmarkContext.supportToken] at ht ⊢
    | penguin =>
        constructor
        · intro h
          have hFly := h (by simp [flyingFamilyConcept] : Trait.flies ∈ flyingFamilyConcept.intent)
          exfalso
          simp [crispRelation, BinaryFcaBenchmarkContext.exactGate,
            EvidenceGate.positiveThreshold, context,
            BinaryFcaBenchmarkContext.supportToken] at hFly
          change 1 ≤ (0 : ℝ≥0∞) at hFly
          simp at hFly
        · intro h
          simp [flyingFamilyConcept] at h
    | bat =>
        constructor
        · intro _
          simp [flyingFamilyConcept]
        · intro _ t ht
          cases t <;>
            simp [flyingFamilyConcept, crispRelation,
              BinaryFcaBenchmarkContext.exactGate, EvidenceGate.positiveThreshold,
              context, BinaryFcaBenchmarkContext.supportToken] at ht ⊢

theorem batOnlyFlyingConcept_not_closed_exact :
    ¬ DualConcept.IsClosed
      (crispRelation BinaryFcaBenchmarkContext.exactGate context.evidence)
      batOnlyFlyingConcept := by
  intro hClosed
  have hRobinLower :
      Animal.robin ∈
        _root_.lowerPolar
          (crispRelation BinaryFcaBenchmarkContext.exactGate context.evidence)
          batOnlyFlyingConcept.intent := by
    intro t ht
    have ht' : t = Trait.flies := by simpa [batOnlyFlyingConcept] using ht
    subst t
    simp [crispRelation, BinaryFcaBenchmarkContext.exactGate,
      EvidenceGate.positiveThreshold, context, BinaryFcaBenchmarkContext.supportToken]
  have hRobinExtent :
      Animal.robin ∈ batOnlyFlyingConcept.extent := by
    rw [← hClosed.2]
    exact hRobinLower
  simp [batOnlyFlyingConcept] at hRobinExtent

theorem batOnlyFlyingConcept_not_closed_strict :
    ¬ DualConcept.IsClosed
      (crispRelation (EvidenceGate.positiveThreshold 2) context.evidence)
      batOnlyFlyingConcept := by
  intro hClosed
  have hRobinLower :
      Animal.robin ∈
        _root_.lowerPolar
          (crispRelation (EvidenceGate.positiveThreshold 2) context.evidence)
          batOnlyFlyingConcept.intent := by
    intro t ht
    have ht' : t = Trait.flies := by simpa [batOnlyFlyingConcept] using ht
    subst t
    simp [crispRelation, EvidenceGate.positiveThreshold,
      context, BinaryFcaBenchmarkContext.supportToken]
  have hRobinExtent :
      Animal.robin ∈ batOnlyFlyingConcept.extent := by
    rw [← hClosed.2]
    exact hRobinLower
  simp [batOnlyFlyingConcept] at hRobinExtent

theorem flyingFamilyConcept_not_closed_strict :
    ¬ DualConcept.IsClosed
      (crispRelation (EvidenceGate.positiveThreshold 2) context.evidence)
      flyingFamilyConcept := by
  intro hClosed
  have hFlyUpper :
      Trait.flies ∈
        _root_.upperPolar
          (crispRelation (EvidenceGate.positiveThreshold 2) context.evidence)
          flyingFamilyConcept.extent := by
    rw [hClosed.1]
    simp [flyingFamilyConcept]
  have hBat :
      crispRelation (EvidenceGate.positiveThreshold 2) context.evidence
        Animal.bat Trait.flies := by
    exact hFlyUpper (by simp [flyingFamilyConcept])
  simp [crispRelation, EvidenceGate.positiveThreshold, context,
    BinaryFcaBenchmarkContext.supportToken] at hBat

theorem flyingFamilyConcept_mem_exact :
    flyingFamilyConcept ∈
      BinaryFcaBenchmarkContext.exactConceptFamily context := by
  exact (AbstractInheritance.mem_finiteConceptFamily_iff
    (G := BinaryFcaBenchmarkContext.exactGate)
    (M := context.evidence)
    flyingFamilyConcept).2 flyingFamilyConcept_closed_exact

theorem batOnlyFlyingConcept_not_mem_exact :
    batOnlyFlyingConcept ∉
      BinaryFcaBenchmarkContext.exactConceptFamily context := by
  simpa [BinaryFcaBenchmarkContext.exactConceptFamily] using
    (not_mem_finiteConceptFamily_iff
      (G := BinaryFcaBenchmarkContext.exactGate)
      (M := context.evidence)
      batOnlyFlyingConcept).2 batOnlyFlyingConcept_not_closed_exact

theorem flyingFamilyConcept_mem_upper :
    flyingFamilyConcept ∈
      BinaryFcaBenchmarkContext.upperThresholdConceptFamily context thresholds := by
  change ∃ b : Bool,
      flyingFamilyConcept ∈
        AbstractInheritance.finiteConceptFamily (gateFamily b) context.evidence
  refine ⟨false, ?_⟩
  exact flyingFamilyConcept_mem_exact

theorem flyingFamilyConcept_not_mem_lower :
    flyingFamilyConcept ∉
      BinaryFcaBenchmarkContext.lowerThresholdConceptFamily context thresholds := by
  intro hLower
  have hLower' :
      ∀ b : Bool,
        flyingFamilyConcept ∈
          AbstractInheritance.finiteConceptFamily (gateFamily b) context.evidence := by
    simpa [BinaryFcaBenchmarkContext.lowerThresholdConceptFamily,
      lowerConceptFamily, gateFamily] using hLower
  have hStrict :
      flyingFamilyConcept ∈
        AbstractInheritance.finiteConceptFamily (gateFamily true) context.evidence :=
    hLower' true
  have hNot :
      flyingFamilyConcept ∉
        AbstractInheritance.finiteConceptFamily (gateFamily true) context.evidence := by
    exact (not_mem_finiteConceptFamily_iff
        (G := EvidenceGate.positiveThreshold 2)
        (M := context.evidence)
        flyingFamilyConcept).2 flyingFamilyConcept_not_closed_strict
  exact hNot hStrict

theorem batOnlyFlyingConcept_not_mem_upper :
    batOnlyFlyingConcept ∉
      BinaryFcaBenchmarkContext.upperThresholdConceptFamily context thresholds := by
  intro hUpper
  change ∃ b : Bool,
      batOnlyFlyingConcept ∈
        AbstractInheritance.finiteConceptFamily (gateFamily b) context.evidence at hUpper
  rcases hUpper with ⟨b, hb⟩
  cases b with
  | false =>
      have hNot :
          batOnlyFlyingConcept ∉
            AbstractInheritance.finiteConceptFamily (gateFamily false) context.evidence := by
        exact batOnlyFlyingConcept_not_mem_exact
      exact hNot hb
  | true =>
      have hNot :
          batOnlyFlyingConcept ∉
            AbstractInheritance.finiteConceptFamily (gateFamily true) context.evidence := by
        exact (not_mem_finiteConceptFamily_iff
            (G := EvidenceGate.positiveThreshold 2)
            (M := context.evidence)
            batOnlyFlyingConcept).2 batOnlyFlyingConcept_not_closed_strict
      exact hNot hb

/-- The exact control benchmark really is the classical FCA lattice of the same
context, not a parallel invention. -/
noncomputable def exactOrderIso :
    AbstractInheritance.FormedConcept
        BinaryFcaBenchmarkContext.exactGate context.evidence ≃o
      CrispConcept BinaryFcaBenchmarkContext.exactGate context.evidence :=
  BinaryFcaBenchmarkContext.exactOrderIso context

end ControlExample

end Mettapedia.Logic.ConceptOntology
