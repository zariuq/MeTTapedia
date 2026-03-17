import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Framework.VertexTemporalRewriteRules

/-!
# Probabilistic Event Calculus (WM- and Rewrite-Grounded)

This module adds a compact, evidence-valued event-calculus layer over the
existing PLN world-model calculus.

Core ideas:
- Event predicates (`hold`, `initiate`, `terminate`) return `BinaryEvidence`.
- Interval operators are lattice aggregations (`iInf`/`iSup`) over time sets.
- WM grounding is via query encoders and `BinaryWorldModel.evidence`.
- Rewrite integration is explicit via `WMRewriteRule` / `WMRewriteRuleSigma`.
-/

namespace Mettapedia.Logic.PLNProbabilisticEventCalculus

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped ENNReal

/-! ## BinaryEvidence-Valued Event Calculus -/

structure ProbEventCalculus (Event Time : Type*) where
  hold : Event → Time → BinaryEvidence
  initiate : Event → Time → BinaryEvidence
  terminate : Event → Time → BinaryEvidence

namespace ProbEventCalculus

variable {Event Time : Type*}

def holdsAt (E : ProbEventCalculus Event Time) (e : Event) (t : Time) : BinaryEvidence :=
  E.hold e t

def initiatedAt (E : ProbEventCalculus Event Time) (e : Event) (t : Time) : BinaryEvidence :=
  E.initiate e t

def terminatedAt (E : ProbEventCalculus Event Time) (e : Event) (t : Time) : BinaryEvidence :=
  E.terminate e t

noncomputable def holdsThroughout (E : ProbEventCalculus Event Time) (e : Event) (I : Set Time) : BinaryEvidence :=
  ⨅ t : I, E.hold e t.1

noncomputable def initiatedThroughout (E : ProbEventCalculus Event Time) (e : Event) (I : Set Time) : BinaryEvidence :=
  ⨅ t : I, E.initiate e t.1

noncomputable def terminatedThroughout (E : ProbEventCalculus Event Time) (e : Event) (I : Set Time) : BinaryEvidence :=
  ⨅ t : I, E.terminate e t.1

noncomputable def holdsSometimeIn (E : ProbEventCalculus Event Time) (e : Event) (I : Set Time) : BinaryEvidence :=
  ⨆ t : I, E.hold e t.1

noncomputable def initiatedSometimeIn (E : ProbEventCalculus Event Time) (e : Event) (I : Set Time) : BinaryEvidence :=
  ⨆ t : I, E.initiate e t.1

noncomputable def terminatedSometimeIn (E : ProbEventCalculus Event Time) (e : Event) (I : Set Time) : BinaryEvidence :=
  ⨆ t : I, E.terminate e t.1

theorem holdsThroughout_le_holdsAt
    (E : ProbEventCalculus Event Time) (e : Event) (I : Set Time)
    {t : Time} (ht : t ∈ I) :
    holdsThroughout E e I ≤ holdsAt E e t := by
  unfold holdsThroughout holdsAt
  exact iInf_le (fun x : I => E.hold e x.1) ⟨t, ht⟩

theorem holdsAt_le_holdsSometimeIn
    (E : ProbEventCalculus Event Time) (e : Event) (I : Set Time)
    {t : Time} (ht : t ∈ I) :
    holdsAt E e t ≤ holdsSometimeIn E e I := by
  unfold holdsAt holdsSometimeIn
  exact le_iSup (fun x : I => E.hold e x.1) ⟨t, ht⟩

theorem holdsThroughout_le_holdsSometimeIn
    (E : ProbEventCalculus Event Time) (e : Event) (I : Set Time)
    {t : Time} (ht : t ∈ I) :
    holdsThroughout E e I ≤ holdsSometimeIn E e I := by
  exact (holdsThroughout_le_holdsAt E e I ht).trans (holdsAt_le_holdsSometimeIn E e I ht)

def PersistentOn (E : ProbEventCalculus Event Time) (e : Event) (I : Set Time) : Prop :=
  ∀ ⦃t₁ t₂ : Time⦄, t₁ ∈ I → t₂ ∈ I → E.initiate e t₁ ≤ E.hold e t₂

def ActionInitiates (E : ProbEventCalculus Event Time) (action event : Event) : Prop :=
  ∀ t : Time, E.hold action t ≤ E.initiate event t

def ActionTerminates (E : ProbEventCalculus Event Time) (action event : Event) : Prop :=
  ∀ t : Time, E.hold action t ≤ E.terminate event t

end ProbEventCalculus

/-! ## WM Query Encoding -/

structure EventQueryEncoder (Event Time Query : Type*) where
  holdsAt : Event → Time → Query
  initiatedAt : Event → Time → Query
  terminatedAt : Event → Time → Query

namespace EventQueryEncoder

variable {State Event Time Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

def holdsAtEvidence (W : State) (enc : EventQueryEncoder Event Time Query)
    (e : Event) (t : Time) : BinaryEvidence :=
  BinaryWorldModel.evidence (State := State) (Query := Query) W (enc.holdsAt e t)

def initiatedAtEvidence (W : State) (enc : EventQueryEncoder Event Time Query)
    (e : Event) (t : Time) : BinaryEvidence :=
  BinaryWorldModel.evidence (State := State) (Query := Query) W (enc.initiatedAt e t)

def terminatedAtEvidence (W : State) (enc : EventQueryEncoder Event Time Query)
    (e : Event) (t : Time) : BinaryEvidence :=
  BinaryWorldModel.evidence (State := State) (Query := Query) W (enc.terminatedAt e t)

noncomputable def holdsAtStrength (W : State) (enc : EventQueryEncoder Event Time Query)
    (e : Event) (t : Time) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (holdsAtEvidence (State := State) W enc e t)

theorem holdsAtEvidence_add (W₁ W₂ : State)
    (enc : EventQueryEncoder Event Time Query) (e : Event) (t : Time) :
    holdsAtEvidence (State := State) (W₁ + W₂) enc e t =
      holdsAtEvidence (State := State) W₁ enc e t +
        holdsAtEvidence (State := State) W₂ enc e t := by
  simpa [holdsAtEvidence] using
    (BinaryWorldModel.evidence_add (State := State) (Query := Query) W₁ W₂ (enc.holdsAt e t))

theorem initiatedAtEvidence_add (W₁ W₂ : State)
    (enc : EventQueryEncoder Event Time Query) (e : Event) (t : Time) :
    initiatedAtEvidence (State := State) (W₁ + W₂) enc e t =
      initiatedAtEvidence (State := State) W₁ enc e t +
        initiatedAtEvidence (State := State) W₂ enc e t := by
  simpa [initiatedAtEvidence] using
    (BinaryWorldModel.evidence_add (State := State) (Query := Query) W₁ W₂ (enc.initiatedAt e t))

theorem terminatedAtEvidence_add (W₁ W₂ : State)
    (enc : EventQueryEncoder Event Time Query) (e : Event) (t : Time) :
    terminatedAtEvidence (State := State) (W₁ + W₂) enc e t =
      terminatedAtEvidence (State := State) W₁ enc e t +
        terminatedAtEvidence (State := State) W₂ enc e t := by
  simpa [terminatedAtEvidence] using
    (BinaryWorldModel.evidence_add (State := State) (Query := Query) W₁ W₂ (enc.terminatedAt e t))

def temporalRewriteOfQueryEq
    (Side : Prop) (qDerived qConclusion : Query)
    (hEq : Side → WMQueryEq (State := State) (Query := Query) qDerived qConclusion) :
    WMRewriteRule State Query :=
  { side := Side
    conclusion := qConclusion
    derive := fun W => BinaryWorldModel.evidence (State := State) (Query := Query) W qDerived
    sound := by
      intro hSide W
      exact hEq hSide W }

def holdsAtRewriteOfQueryEq
    (Side : Prop) (enc : EventQueryEncoder Event Time Query)
    (e : Event) (t : Time) (qDerived : Query)
    (hEq : Side →
      WMQueryEq (State := State) (Query := Query) qDerived (enc.holdsAt e t)) :
    WMRewriteRule State Query :=
  temporalRewriteOfQueryEq (State := State) (Query := Query)
    Side qDerived (enc.holdsAt e t) hEq

def initiatedAtRewriteOfQueryEq
    (Side : Prop) (enc : EventQueryEncoder Event Time Query)
    (e : Event) (t : Time) (qDerived : Query)
    (hEq : Side →
      WMQueryEq (State := State) (Query := Query) qDerived (enc.initiatedAt e t)) :
    WMRewriteRule State Query :=
  temporalRewriteOfQueryEq (State := State) (Query := Query)
    Side qDerived (enc.initiatedAt e t) hEq

def terminatedAtRewriteOfQueryEq
    (Side : Prop) (enc : EventQueryEncoder Event Time Query)
    (e : Event) (t : Time) (qDerived : Query)
    (hEq : Side →
      WMQueryEq (State := State) (Query := Query) qDerived (enc.terminatedAt e t)) :
    WMRewriteRule State Query :=
  temporalRewriteOfQueryEq (State := State) (Query := Query)
    Side qDerived (enc.terminatedAt e t) hEq

end EventQueryEncoder

/-! ## Typed (Sort-Indexed) Query Encoding -/

structure EventQueryEncoderSigma (Event Time Srt : Type*) (Query : Srt → Type*) where
  holdsAt : Event → Time → Sigma Query
  initiatedAt : Event → Time → Sigma Query
  terminatedAt : Event → Time → Sigma Query

namespace EventQueryEncoderSigma

variable {State Event Time Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

def holdsAtEvidence (W : State) (enc : EventQueryEncoderSigma Event Time Srt Query)
    (e : Event) (t : Time) : BinaryEvidence :=
  WorldModelSigma.evidence W (enc.holdsAt e t)

def temporalRewriteOfQueryEq
    (Side : Prop) (qDerived qConclusion : Sigma Query)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := Srt) (Query := Query) qDerived qConclusion) :
    WorldModelSigma.WMRewriteRuleSigma State Srt Query :=
  { side := Side
    conclusion := qConclusion
    derive := fun W => WorldModelSigma.evidence W qDerived
    sound := by
      intro hSide W
      exact hEq hSide W }

def holdsAtRewriteOfQueryEq
    (Side : Prop) (enc : EventQueryEncoderSigma Event Time Srt Query)
    (e : Event) (t : Time) (qDerived : Sigma Query)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := Srt) (Query := Query) qDerived (enc.holdsAt e t)) :
    WorldModelSigma.WMRewriteRuleSigma State Srt Query :=
  temporalRewriteOfQueryEq (State := State) (Srt := Srt) (Query := Query)
    Side qDerived (enc.holdsAt e t) hEq

def initiatedAtRewriteOfQueryEq
    (Side : Prop) (enc : EventQueryEncoderSigma Event Time Srt Query)
    (e : Event) (t : Time) (qDerived : Sigma Query)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := Srt) (Query := Query) qDerived (enc.initiatedAt e t)) :
    WorldModelSigma.WMRewriteRuleSigma State Srt Query :=
  temporalRewriteOfQueryEq (State := State) (Srt := Srt) (Query := Query)
    Side qDerived (enc.initiatedAt e t) hEq

def terminatedAtRewriteOfQueryEq
    (Side : Prop) (enc : EventQueryEncoderSigma Event Time Srt Query)
    (e : Event) (t : Time) (qDerived : Sigma Query)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := Srt) (Query := Query) qDerived (enc.terminatedAt e t)) :
    WorldModelSigma.WMRewriteRuleSigma State Srt Query :=
  temporalRewriteOfQueryEq (State := State) (Srt := Srt) (Query := Query)
    Side qDerived (enc.terminatedAt e t) hEq

end EventQueryEncoderSigma

/-! ## Pattern-Level Event Query Syntax -/

def patternEventQueryEncoder : EventQueryEncoder Pattern Pattern Pattern where
  holdsAt e t := Pattern.apply "holdsAt" [e, t]
  initiatedAt e t := Pattern.apply "initiatedAt" [e, t]
  terminatedAt e t := Pattern.apply "terminatedAt" [e, t]

inductive EventCalcSort where
  | holds
  | initiated
  | terminated
  deriving DecidableEq, Repr

def PatternEventQueryFamily : EventCalcSort → Type
  | .holds => Pattern
  | .initiated => Pattern
  | .terminated => Pattern

def patternEventQueryEncoderSigma :
    EventQueryEncoderSigma Pattern Pattern EventCalcSort PatternEventQueryFamily where
  holdsAt e t := ⟨.holds, Pattern.apply "holdsAt" [e, t]⟩
  initiatedAt e t := ⟨.initiated, Pattern.apply "initiatedAt" [e, t]⟩
  terminatedAt e t := ⟨.terminated, Pattern.apply "terminatedAt" [e, t]⟩

/-- Native event-sort-indexed WMΣ instance induced from untyped pattern WM evidence. -/
def worldModelSigmaPatternEventFromUntyped
    (State : Type*)
    [EvidenceType State] [BinaryWorldModel State Pattern] :
    WorldModelSigma State EventCalcSort PatternEventQueryFamily where
  evidence W q := by
    cases q with
    | mk s qs =>
        cases s <;>
          exact BinaryWorldModel.evidence (State := State) (Query := Pattern) W qs
  evidence_add W₁ W₂ q := by
    cases q with
    | mk s qs =>
        cases s <;>
          simpa using
            (BinaryWorldModel.evidence_add (State := State) (Query := Pattern) W₁ W₂ qs)

instance instWorldModelSigmaPatternEvent
    (State : Type*)
    [EvidenceType State] [BinaryWorldModel State Pattern] :
    WorldModelSigma State EventCalcSort PatternEventQueryFamily :=
  worldModelSigmaPatternEventFromUntyped (State := State)

/-- Pattern-level atom encoder for event-holds queries. -/
def patternEventQueryOfAtom_holds :
    String → Pattern → Sigma PatternEventQueryFamily :=
  fun a p => patternEventQueryEncoderSigma.holdsAt (.fvar a) p

/-- Pattern-level atom encoder for event-initiation queries. -/
def patternEventQueryOfAtom_initiated :
    String → Pattern → Sigma PatternEventQueryFamily :=
  fun a p => patternEventQueryEncoderSigma.initiatedAt (.fvar a) p

/-- Pattern-level atom encoder for event-termination queries. -/
def patternEventQueryOfAtom_terminated :
    String → Pattern → Sigma PatternEventQueryFamily :=
  fun a p => patternEventQueryEncoderSigma.terminatedAt (.fvar a) p

section PatternTypedRules

variable {State : Type*}
variable [EvidenceType State] [BinaryWorldModel State Pattern]

local instance : WorldModelSigma State EventCalcSort PatternEventQueryFamily :=
  worldModelSigmaPatternEventFromUntyped (State := State)

/-- Typed event-calculus rewrite constructor for `holdsAt` conclusions. -/
def holdsAtRewriteOfQueryEqSigmaPattern
    (Side : Prop)
    (event time : Pattern)
    (qDerived : Sigma PatternEventQueryFamily)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        qDerived (patternEventQueryEncoderSigma.holdsAt event time)) :
    WorldModelSigma.WMRewriteRuleSigma State EventCalcSort PatternEventQueryFamily :=
  EventQueryEncoderSigma.holdsAtRewriteOfQueryEq
    (State := State) (Event := Pattern) (Time := Pattern)
    (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
    Side patternEventQueryEncoderSigma event time qDerived hEq

/-- Typed event-calculus rewrite constructor for `initiatedAt` conclusions. -/
def initiatedAtRewriteOfQueryEqSigmaPattern
    (Side : Prop)
    (event time : Pattern)
    (qDerived : Sigma PatternEventQueryFamily)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        qDerived (patternEventQueryEncoderSigma.initiatedAt event time)) :
    WorldModelSigma.WMRewriteRuleSigma State EventCalcSort PatternEventQueryFamily :=
  EventQueryEncoderSigma.initiatedAtRewriteOfQueryEq
    (State := State) (Event := Pattern) (Time := Pattern)
    (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
    Side patternEventQueryEncoderSigma event time qDerived hEq

/-- Typed event-calculus rewrite constructor for `terminatedAt` conclusions. -/
def terminatedAtRewriteOfQueryEqSigmaPattern
    (Side : Prop)
    (event time : Pattern)
    (qDerived : Sigma PatternEventQueryFamily)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        qDerived (patternEventQueryEncoderSigma.terminatedAt event time)) :
    WorldModelSigma.WMRewriteRuleSigma State EventCalcSort PatternEventQueryFamily :=
  EventQueryEncoderSigma.terminatedAtRewriteOfQueryEq
    (State := State) (Event := Pattern) (Time := Pattern)
    (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
    Side patternEventQueryEncoderSigma event time qDerived hEq

end PatternTypedRules

/-! ## OSLF Temporal Rule Correspondence (Chapter 14 Grounding) -/

section OSLFTemporalCorrespondence

open Mettapedia.OSLF.Framework.VertexTemporalRewriteRules

/-- Erase the event sort tag, keeping the underlying pattern. -/
def sigmaEventQueryPattern : Sigma PatternEventQueryFamily → Pattern
  | ⟨.holds, p⟩ => p
  | ⟨.initiated, p⟩ => p
  | ⟨.terminated, p⟩ => p

@[simp] theorem sigmaEventQueryPattern_holds (e t : Pattern) :
    sigmaEventQueryPattern (patternEventQueryEncoderSigma.holdsAt e t) =
      pHoldsAt e t := rfl

@[simp] theorem sigmaEventQueryPattern_initiated (e t : Pattern) :
    sigmaEventQueryPattern (patternEventQueryEncoderSigma.initiatedAt e t) =
      pInitiatedAt e t := rfl

@[simp] theorem sigmaEventQueryPattern_terminated (e t : Pattern) :
    sigmaEventQueryPattern (patternEventQueryEncoderSigma.terminatedAt e t) =
      pTerminatedAt e t := rfl

section TypedConstructors

variable {State : Type*}
variable [EvidenceType State] [BinaryWorldModel State Pattern]

local instance : WorldModelSigma State EventCalcSort PatternEventQueryFamily :=
  worldModelSigmaPatternEventFromUntyped (State := State)

/-- Canonical WMΣ constructor matching the OSLF rule
`initiatedAt(e,t) → holdsAt(e,t)`. -/
def initiatedImpliesHoldsRewriteSigmaPattern
    (Side : Prop)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        (patternEventQueryEncoderSigma.initiatedAt (.fvar "e") (.fvar "t"))
        (patternEventQueryEncoderSigma.holdsAt (.fvar "e") (.fvar "t"))) :
    WorldModelSigma.WMRewriteRuleSigma State EventCalcSort PatternEventQueryFamily :=
  holdsAtRewriteOfQueryEqSigmaPattern
    (State := State)
    Side (.fvar "e") (.fvar "t")
    (patternEventQueryEncoderSigma.initiatedAt (.fvar "e") (.fvar "t")) hEq

/-- Canonical WMΣ constructor matching the OSLF persistence rule
`holdsAt(e,t) → holdsAt(e,next(t))`. -/
def holdsPersistenceRewriteSigmaPattern
    (Side : Prop)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        (patternEventQueryEncoderSigma.holdsAt (.fvar "e") (.fvar "t"))
        (patternEventQueryEncoderSigma.holdsAt (.fvar "e") (pNext (.fvar "t")))) :
    WorldModelSigma.WMRewriteRuleSigma State EventCalcSort PatternEventQueryFamily :=
  holdsAtRewriteOfQueryEqSigmaPattern
    (State := State)
    Side (.fvar "e") (pNext (.fvar "t"))
    (patternEventQueryEncoderSigma.holdsAt (.fvar "e") (.fvar "t")) hEq

/-- Canonical WMΣ constructor matching the OSLF rule
`terminatedAt(e,t) → terminatedAt(e,next(t))`. -/
def terminatedStepRewriteSigmaPattern
    (Side : Prop)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        (patternEventQueryEncoderSigma.terminatedAt (.fvar "e") (.fvar "t"))
        (patternEventQueryEncoderSigma.terminatedAt (.fvar "e") (pNext (.fvar "t")))) :
    WorldModelSigma.WMRewriteRuleSigma State EventCalcSort PatternEventQueryFamily :=
  terminatedAtRewriteOfQueryEqSigmaPattern
    (State := State)
    Side (.fvar "e") (pNext (.fvar "t"))
    (patternEventQueryEncoderSigma.terminatedAt (.fvar "e") (.fvar "t")) hEq

theorem initiatedImpliesHolds_constructor_corresponds
    (v : Mettapedia.ProbabilityTheory.Hypercube.ProbabilityVertex)
    (Side : Prop)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        (patternEventQueryEncoderSigma.initiatedAt (.fvar "e") (.fvar "t"))
        (patternEventQueryEncoderSigma.holdsAt (.fvar "e") (.fvar "t"))) :
    sigmaEventQueryPattern
      (patternEventQueryEncoderSigma.initiatedAt (.fvar "e") (.fvar "t")) =
        ruleEventInitiatedImpliesHolds.left ∧
    sigmaEventQueryPattern (initiatedImpliesHoldsRewriteSigmaPattern
      (State := State) Side hEq).conclusion =
        ruleEventInitiatedImpliesHolds.right ∧
    ruleEventInitiatedImpliesHolds ∈ (vertexTemporalLanguageDef v).rewrites := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sigmaEventQueryPattern, patternEventQueryEncoderSigma,
      ruleEventInitiatedImpliesHolds, pInitiatedAt]
  · simp [initiatedImpliesHoldsRewriteSigmaPattern,
      holdsAtRewriteOfQueryEqSigmaPattern,
      EventQueryEncoderSigma.holdsAtRewriteOfQueryEq,
      EventQueryEncoderSigma.temporalRewriteOfQueryEq,
      sigmaEventQueryPattern, patternEventQueryEncoderSigma,
      ruleEventInitiatedImpliesHolds, pHoldsAt]
  simp [vertexTemporalLanguageDef, activeRulesWithTemporal, temporalEventRules]

theorem holdsPersistence_constructor_corresponds
    (v : Mettapedia.ProbabilityTheory.Hypercube.ProbabilityVertex)
    (Side : Prop)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        (patternEventQueryEncoderSigma.holdsAt (.fvar "e") (.fvar "t"))
        (patternEventQueryEncoderSigma.holdsAt (.fvar "e") (pNext (.fvar "t")))) :
    sigmaEventQueryPattern
      (patternEventQueryEncoderSigma.holdsAt (.fvar "e") (.fvar "t")) =
        ruleEventPersistenceStep.left ∧
    sigmaEventQueryPattern (holdsPersistenceRewriteSigmaPattern
      (State := State) Side hEq).conclusion =
        ruleEventPersistenceStep.right ∧
    ruleEventPersistenceStep ∈ (vertexTemporalLanguageDef v).rewrites := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sigmaEventQueryPattern, patternEventQueryEncoderSigma,
      ruleEventPersistenceStep, pHoldsAt]
  · simp [holdsPersistenceRewriteSigmaPattern,
      holdsAtRewriteOfQueryEqSigmaPattern,
      EventQueryEncoderSigma.holdsAtRewriteOfQueryEq,
      EventQueryEncoderSigma.temporalRewriteOfQueryEq,
      sigmaEventQueryPattern, patternEventQueryEncoderSigma,
      ruleEventPersistenceStep, pHoldsAt, pNext]
  simp [vertexTemporalLanguageDef, activeRulesWithTemporal, temporalEventRules]

theorem terminatedStep_constructor_corresponds
    (v : Mettapedia.ProbabilityTheory.Hypercube.ProbabilityVertex)
    (Side : Prop)
    (hEq : Side →
      WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        (patternEventQueryEncoderSigma.terminatedAt (.fvar "e") (.fvar "t"))
        (patternEventQueryEncoderSigma.terminatedAt (.fvar "e") (pNext (.fvar "t")))) :
    sigmaEventQueryPattern
      (patternEventQueryEncoderSigma.terminatedAt (.fvar "e") (.fvar "t")) =
        ruleEventTerminationStep.left ∧
    sigmaEventQueryPattern (terminatedStepRewriteSigmaPattern
      (State := State) Side hEq).conclusion =
        ruleEventTerminationStep.right ∧
    ruleEventTerminationStep ∈ (vertexTemporalLanguageDef v).rewrites := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sigmaEventQueryPattern, patternEventQueryEncoderSigma,
      ruleEventTerminationStep, pTerminatedAt]
  · simp [terminatedStepRewriteSigmaPattern,
      terminatedAtRewriteOfQueryEqSigmaPattern,
      EventQueryEncoderSigma.terminatedAtRewriteOfQueryEq,
      EventQueryEncoderSigma.temporalRewriteOfQueryEq,
      sigmaEventQueryPattern, patternEventQueryEncoderSigma,
      ruleEventTerminationStep, pTerminatedAt, pNext]
  simp [vertexTemporalLanguageDef, activeRulesWithTemporal, temporalEventRules]

end TypedConstructors
end OSLFTemporalCorrespondence

end Mettapedia.Logic.PLNProbabilisticEventCalculus
