import Mettapedia.Ethics.CredalValueAttributionCaseTable

/-!
# Credal Value Attribution from Cases

This file is a tiny downstream consumer of the credal concept-formation layer.

The setup is intentionally small:

- cases are the object domain
- moral-value tags are the concept domain
- evidence assigns case/value support directly
- two admissible gates represent lenient vs strict acceptance thresholds

The resulting example shows both a stable attribution and a genuinely ambiguous
one, giving the first ethics-facing target for uncertainty-native concept
formation.
-/

namespace Mettapedia.Ethics

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.ConceptOntology
open Mettapedia.Logic.AbstractInheritance

inductive CaseStudy where
  | returningWallet
  | betrayal
  deriving DecidableEq, Repr, Fintype

def yes : BinaryEvidence := ⟨1, 0⟩

def strongYes : BinaryEvidence := ⟨2, 0⟩

@[simp] theorem binaryEvidence_pos_zero : BinaryEvidence.pos (0 : BinaryEvidence) = 0 := rfl

/-- Direct value-attribution evidence extracted from a tiny case table. -/
def valueAttributionFromCasesEvidence :
    CaseStudy → MoralValueAttribute → BinaryEvidence
  | .returningWallet, .MorallyGood => yes
  | .betrayal, .MorallyBad => strongYes
  | _, _ => (0 : BinaryEvidence)

def looseGate : EvidenceGate BinaryEvidence :=
  EvidenceGate.positiveThreshold 1

def strictGate : EvidenceGate BinaryEvidence :=
  EvidenceGate.positiveThreshold 2

def valueGateFamily : Bool → EvidenceGate BinaryEvidence
  | false => looseGate
  | true => strictGate

def valueCaseTable : CredalValueAttributionCaseTable CaseStudy where
  evidence := valueAttributionFromCasesEvidence

def returningWalletGoodConcept : DualConcept CaseStudy MoralValueAttribute where
  extent := {CaseStudy.returningWallet}
  intent := {MoralValueAttribute.MorallyGood}

def betrayalBadConcept : DualConcept CaseStudy MoralValueAttribute where
  extent := {CaseStudy.betrayal}
  intent := {MoralValueAttribute.MorallyBad}

theorem returningWalletGoodConcept_closed_loose :
    DualConcept.IsClosed
      (crispRelation looseGate valueAttributionFromCasesEvidence)
      returningWalletGoodConcept := by
  constructor
  · ext m
    cases m with
    | MorallyGood =>
        constructor
        · intro _
          simp [returningWalletGoodConcept]
        · intro _ x hx
          have hx' : x = CaseStudy.returningWallet := by
            simpa [returningWalletGoodConcept] using hx
          subst x
          simp [crispRelation, looseGate, valueAttributionFromCasesEvidence, yes]
    | MorallyBad =>
        constructor
        · intro h
          simp [returningWalletGoodConcept]
          have hbad :=
            h (by simp : CaseStudy.returningWallet ∈ ({CaseStudy.returningWallet} : Set CaseStudy))
          simp [crispRelation, looseGate, valueAttributionFromCasesEvidence] at hbad
        · intro h
          simp [returningWalletGoodConcept] at h
    | MorallyPermissible =>
        constructor
        · intro h
          simp [returningWalletGoodConcept]
          have hperm :=
            h (by simp : CaseStudy.returningWallet ∈ ({CaseStudy.returningWallet} : Set CaseStudy))
          simp [crispRelation, looseGate, valueAttributionFromCasesEvidence] at hperm
        · intro h
          simp [returningWalletGoodConcept] at h
  · ext c
    cases c with
    | returningWallet =>
        constructor
        · intro _
          simp [returningWalletGoodConcept]
        · intro _ m hm
          have hm' : m = MoralValueAttribute.MorallyGood := by
            simpa [returningWalletGoodConcept] using hm
          subst m
          simp [crispRelation, looseGate, valueAttributionFromCasesEvidence, yes]
    | betrayal =>
        constructor
        · intro h
          simp [returningWalletGoodConcept]
          have hbad :=
            h (by simp :
              MoralValueAttribute.MorallyGood ∈
                ({MoralValueAttribute.MorallyGood} : Set MoralValueAttribute))
          simp [crispRelation, looseGate, valueAttributionFromCasesEvidence] at hbad
        · intro h
          simp [returningWalletGoodConcept] at h

theorem betrayalBadConcept_closed_loose :
    DualConcept.IsClosed
      (crispRelation looseGate valueAttributionFromCasesEvidence)
      betrayalBadConcept := by
  constructor
  · ext m
    cases m with
    | MorallyGood =>
        constructor
        · intro h
          simp [betrayalBadConcept]
          have hgood := h (by simp : CaseStudy.betrayal ∈ ({CaseStudy.betrayal} : Set CaseStudy))
          simp [crispRelation, looseGate, valueAttributionFromCasesEvidence] at hgood
        · intro h
          simp [betrayalBadConcept] at h
    | MorallyBad =>
        constructor
        · intro _
          simp [betrayalBadConcept]
        · intro _ x hx
          have hx' : x = CaseStudy.betrayal := by
            simpa [betrayalBadConcept] using hx
          subst x
          simp [crispRelation, looseGate, valueAttributionFromCasesEvidence, strongYes]
    | MorallyPermissible =>
        constructor
        · intro h
          simp [betrayalBadConcept]
          have hperm := h (by simp : CaseStudy.betrayal ∈ ({CaseStudy.betrayal} : Set CaseStudy))
          simp [crispRelation, looseGate, valueAttributionFromCasesEvidence] at hperm
        · intro h
          simp [betrayalBadConcept] at h
  · ext c
    cases c with
    | returningWallet =>
        constructor
        · intro h
          simp [betrayalBadConcept]
          have hret := h (by simp :
            MoralValueAttribute.MorallyBad ∈
              ({MoralValueAttribute.MorallyBad} : Set MoralValueAttribute))
          simp [crispRelation, looseGate, valueAttributionFromCasesEvidence] at hret
        · intro h
          simp [betrayalBadConcept] at h
    | betrayal =>
        constructor
        · intro _
          simp [betrayalBadConcept]
        · intro _ m hm
          have hm' : m = MoralValueAttribute.MorallyBad := by
            simpa [betrayalBadConcept] using hm
          subst m
          simp [crispRelation, looseGate, valueAttributionFromCasesEvidence, strongYes]

theorem betrayalBadConcept_closed_strict :
    DualConcept.IsClosed
      (crispRelation strictGate valueAttributionFromCasesEvidence)
      betrayalBadConcept := by
  constructor
  · ext m
    cases m with
    | MorallyGood =>
        constructor
        · intro h
          simp [betrayalBadConcept]
          have hgood := h (by simp : CaseStudy.betrayal ∈ ({CaseStudy.betrayal} : Set CaseStudy))
          simp [crispRelation, strictGate, valueAttributionFromCasesEvidence] at hgood
        · intro h
          simp [betrayalBadConcept] at h
    | MorallyBad =>
        constructor
        · intro _
          simp [betrayalBadConcept]
        · intro _ x hx
          have hx' : x = CaseStudy.betrayal := by
            simpa [betrayalBadConcept] using hx
          subst x
          simp [crispRelation, strictGate, valueAttributionFromCasesEvidence, strongYes]
    | MorallyPermissible =>
        constructor
        · intro h
          simp [betrayalBadConcept]
          have hperm := h (by simp : CaseStudy.betrayal ∈ ({CaseStudy.betrayal} : Set CaseStudy))
          simp [crispRelation, strictGate, valueAttributionFromCasesEvidence] at hperm
        · intro h
          simp [betrayalBadConcept] at h
  · ext c
    cases c with
    | returningWallet =>
        constructor
        · intro h
          simp [betrayalBadConcept]
          have hret := h (by simp :
            MoralValueAttribute.MorallyBad ∈
              ({MoralValueAttribute.MorallyBad} : Set MoralValueAttribute))
          simp [crispRelation, strictGate, valueAttributionFromCasesEvidence] at hret
        · intro h
          simp [betrayalBadConcept] at h
    | betrayal =>
        constructor
        · intro _
          simp [betrayalBadConcept]
        · intro _ m hm
          have hm' : m = MoralValueAttribute.MorallyBad := by
            simpa [betrayalBadConcept] using hm
          subst m
          simp [crispRelation, strictGate, valueAttributionFromCasesEvidence, strongYes]

theorem returningWalletGoodConcept_not_closed_strict :
    ¬ DualConcept.IsClosed
      (crispRelation strictGate valueAttributionFromCasesEvidence)
      returningWalletGoodConcept := by
  intro hClosed
  have hmem :
      MoralValueAttribute.MorallyGood ∈
        _root_.upperPolar
          (crispRelation strictGate valueAttributionFromCasesEvidence)
          returningWalletGoodConcept.extent := by
    have hEq := hClosed.1
    rw [hEq]
    simp [returningWalletGoodConcept]
  have hgood :
      crispRelation strictGate valueAttributionFromCasesEvidence
        CaseStudy.returningWallet MoralValueAttribute.MorallyGood := by
    exact hmem (by simp [returningWalletGoodConcept])
  have : False := by
    simp [strictGate, crispRelation, valueAttributionFromCasesEvidence, yes] at hgood
  exact this.elim

theorem returningWalletGoodConcept_mem_upper :
    returningWalletGoodConcept ∈
      valueCaseTable.upperConceptFamily (Gate := Bool) valueGateFamily := by
  refine ⟨false, ?_⟩
  exact (AbstractInheritance.mem_finiteConceptFamily_iff
    looseGate valueAttributionFromCasesEvidence returningWalletGoodConcept).2
      returningWalletGoodConcept_closed_loose

theorem returningWalletGoodConcept_not_mem_lower :
    returningWalletGoodConcept ∉
      valueCaseTable.lowerConceptFamily (Gate := Bool) valueGateFamily := by
  intro hLower
  change
    ∀ b : Bool,
      returningWalletGoodConcept ∈
        AbstractInheritance.finiteConceptFamily
          (valueGateFamily b) valueAttributionFromCasesEvidence at hLower
  exact returningWalletGoodConcept_not_closed_strict
    ((AbstractInheritance.mem_finiteConceptFamily_iff strictGate
      valueAttributionFromCasesEvidence returningWalletGoodConcept).mp
        (by simpa [valueGateFamily] using hLower true))

theorem betrayalBadConcept_mem_lower :
    betrayalBadConcept ∈
      valueCaseTable.lowerConceptFamily (Gate := Bool) valueGateFamily := by
  change
    ∀ b : Bool,
      betrayalBadConcept ∈
        AbstractInheritance.finiteConceptFamily
          (valueGateFamily b) valueAttributionFromCasesEvidence
  intro b
  cases b with
  | false =>
      simpa [valueGateFamily] using
        (AbstractInheritance.mem_finiteConceptFamily_iff
          looseGate valueAttributionFromCasesEvidence betrayalBadConcept).2
          betrayalBadConcept_closed_loose
  | true =>
      simpa [valueGateFamily] using
        (AbstractInheritance.mem_finiteConceptFamily_iff
          strictGate valueAttributionFromCasesEvidence betrayalBadConcept).2
          betrayalBadConcept_closed_strict

theorem returningWalletGoodConcept_globalEnvelopeMidpoint_eq_half :
    (gateCredalProjectiveSpec (Gate := Bool)).globalEnvelopeMidpoint
        (conceptFormationGamble valueGateFamily
          valueAttributionFromCasesEvidence returningWalletGoodConcept) =
      (1 / 2 : ℝ) := by
  have h :=
    Mettapedia.Logic.ConceptOntology.globalEnvelopeMidpoint_conceptFormationGamble_eq
      (Gate := Bool) valueGateFamily valueAttributionFromCasesEvidence
      returningWalletGoodConcept
  have hLower :
      returningWalletGoodConcept ∉
        Mettapedia.Logic.ConceptOntology.lowerConceptFamily
          (Gate := Bool) valueGateFamily valueAttributionFromCasesEvidence := by
    exact returningWalletGoodConcept_not_mem_lower
  have hUpper :
      returningWalletGoodConcept ∈
        Mettapedia.Logic.ConceptOntology.upperConceptFamily
          (Gate := Bool) valueGateFamily valueAttributionFromCasesEvidence := by
    exact returningWalletGoodConcept_mem_upper
  rw [if_neg hLower, if_pos hUpper] at h
  simpa using h

theorem betrayalBadConcept_globalEnvelopeWidthComplement_eq_one :
    (gateCredalProjectiveSpec (Gate := Bool)).globalEnvelopeWidthComplement
        (conceptFormationGamble valueGateFamily
          valueAttributionFromCasesEvidence betrayalBadConcept) = 1 := by
  have hNotMixed :
      ¬ (betrayalBadConcept ∈
            Mettapedia.Logic.ConceptOntology.upperConceptFamily
              (Gate := Bool) valueGateFamily valueAttributionFromCasesEvidence ∧
          betrayalBadConcept ∉
            Mettapedia.Logic.ConceptOntology.lowerConceptFamily
              (Gate := Bool) valueGateFamily valueAttributionFromCasesEvidence) := by
    intro hMixed
    exact hMixed.2 betrayalBadConcept_mem_lower
  have h :=
    Mettapedia.Logic.ConceptOntology.globalEnvelopeWidthComplement_conceptFormationGamble_eq
      (Gate := Bool) valueGateFamily valueAttributionFromCasesEvidence
      betrayalBadConcept
  rw [if_neg hNotMixed] at h
  simpa using h

end Mettapedia.Ethics
