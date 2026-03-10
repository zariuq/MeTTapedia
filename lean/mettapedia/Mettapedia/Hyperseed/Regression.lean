import Mettapedia.Hyperseed.Basic

/-!
# Hyperseed Regression

Golden PoC for the new Hyperseed front door:

- a nonempty observation trace seeds a perception query,
- Hyperseed closure derives readiness and then self-awareness,
- the underlying sufficient-statistics world model is provably nontrivial.

Positive example:
- nonempty trace ⇒ `awareReady` is discovered and the WM state has nonzero count.

Negative example:
- empty trace ⇒ `awareReady` is not in closure.
-/

namespace Mettapedia.Hyperseed.Regression

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelAdditive
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open Mettapedia.Logic.PLNWorldModelFixpointCascade
open Mettapedia.Logic.SufficientStatisticSurface
open Mettapedia.Hyperseed
open scoped ENNReal

inductive AgentObservation where
  | pulse
  deriving DecidableEq, Fintype

inductive AgentQuery where
  | sensedSignal
  | readyToAct
  | awareReady
  deriving DecidableEq, Fintype

def unitPositiveEvidence : Evidence :=
  { pos := 1, neg := 0 }

/-- The PoC surface uses the same one-unit positive evidence for every query.
This keeps the Hyperseed example focused on observation ingestion and closure,
while still living entirely on the additive WM foundations. -/
def agentSurface : SufficientStatisticSurface AgentObservation AgentQuery Evidence :=
  SufficientStatisticSurface.ofObservationMap (fun _ => unitPositiveEvidence)

theorem agentSurface_unitObservation :
    UnitObservation agentSurface := by
  intro o q
  change (unitPositiveEvidence : Evidence).total = 1
  simp [unitPositiveEvidence, Evidence.total]

noncomputable instance : EvidenceType (Multiset AgentObservation) :=
  multisetEvidenceType AgentObservation

noncomputable instance : WorldModel (Multiset AgentObservation) AgentQuery :=
  worldModelOfAtomicEvidence agentSurface.observe

noncomputable instance : GenericWorldModel (Multiset AgentObservation) AgentQuery Evidence :=
  agentSurface.inducedWorldModel

def agentFrontier (_ : AgentObservation) : Set AgentQuery :=
  { AgentQuery.sensedSignal }

theorem sensedSignal_mem_traceSeed_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.sensedSignal ∈ traceSeed agentFrontier σ := by
  obtain ⟨o, ho⟩ := Multiset.exists_mem_of_ne_zero hσ
  exact ⟨o, ho, by simp [agentFrontier]⟩

theorem agentSurface_aggregate_independent
    (σ : Multiset AgentObservation) (q₁ q₂ : AgentQuery) :
    aggregate agentSurface σ q₁ = aggregate agentSurface σ q₂ := by
  rfl

theorem agentWorldModel_evidence_eq_aggregate
    (σ : Multiset AgentObservation) (q : AgentQuery) :
    WorldModel.evidence (State := Multiset AgentObservation) (Query := AgentQuery) σ q =
      aggregate agentSurface σ q := by
  change additiveExtension agentSurface.observe σ q = aggregate agentSurface σ q
  exact (aggregate_eq_additiveExtension (S := agentSurface) σ q).symm

theorem agentQueryEq
    (q₁ q₂ : AgentQuery) :
    WMQueryEq (State := Multiset AgentObservation) (Query := AgentQuery) q₁ q₂ := by
  intro σ
  calc
    WorldModel.evidence (State := Multiset AgentObservation) (Query := AgentQuery) σ q₁
        = aggregate agentSurface σ q₁ :=
          agentWorldModel_evidence_eq_aggregate σ q₁
    _ = aggregate agentSurface σ q₂ :=
          agentSurface_aggregate_independent σ q₁ q₂
    _ = WorldModel.evidence (State := Multiset AgentObservation) (Query := AgentQuery) σ q₂ := by
          symm
          exact agentWorldModel_evidence_eq_aggregate σ q₂

abbrev sensedSignalToReadyRule : WMConsequenceRuleOn (Multiset AgentObservation) AgentQuery where
  side := fun σ => σ ≠ 0
  premise := AgentQuery.sensedSignal
  conclusion := AgentQuery.readyToAct
  sound := by
    intro σ hσ
    have hEq :=
      WMQueryEq.to_queryStrength
        (State := Multiset AgentObservation) (Query := AgentQuery)
        (agentQueryEq AgentQuery.sensedSignal AgentQuery.readyToAct) σ
    simp [hEq]

abbrev readyToAwareRule : WMConsequenceRuleOn (Multiset AgentObservation) AgentQuery where
  side := fun σ => σ ≠ 0
  premise := AgentQuery.readyToAct
  conclusion := AgentQuery.awareReady
  sound := by
    intro σ hσ
    have hEq :=
      WMQueryEq.to_queryStrength
        (State := Multiset AgentObservation) (Query := AgentQuery)
        (agentQueryEq AgentQuery.readyToAct AgentQuery.awareReady) σ
    simp [hEq]

def agentRules : RuleSet (Multiset AgentObservation) AgentQuery :=
  { r | r = sensedSignalToReadyRule ∨ r = readyToAwareRule }

theorem sensedSignalToReadyRule_mem_agentRules :
    sensedSignalToReadyRule ∈ agentRules := by
  simp [agentRules]

theorem readyToAwareRule_mem_agentRules :
    readyToAwareRule ∈ agentRules := by
  simp [agentRules]

theorem sensedSignal_in_closure_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.sensedSignal ∈
      closureFromTrace agentSurface agentFrontier agentRules σ := by
  exact
    seed_subset_closureFromTrace agentSurface agentFrontier agentRules σ
      (sensedSignal_mem_traceSeed_of_nonempty hσ)

theorem readyToAct_in_closure_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.readyToAct ∈
      closureFromTrace agentSurface agentFrontier agentRules σ := by
  have hprem := sensedSignal_in_closure_of_nonempty hσ
  exact
    leastRuleClosure_rule_closed
      (R := agentRules) (W := σ) (seed := traceSeed agentFrontier σ)
      (r := sensedSignalToReadyRule)
      sensedSignalToReadyRule_mem_agentRules hσ hprem

theorem awareReady_in_closure_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∈
      closureFromTrace agentSurface agentFrontier agentRules σ := by
  have hprem := readyToAct_in_closure_of_nonempty hσ
  exact
    leastRuleClosure_rule_closed
      (R := agentRules) (W := σ) (seed := traceSeed agentFrontier σ)
      (r := readyToAwareRule)
      readyToAwareRule_mem_agentRules hσ hprem

theorem awareReady_not_in_closure_of_empty :
    AgentQuery.awareReady ∉
      closureFromTrace agentSurface agentFrontier agentRules (0 : Multiset AgentObservation) := by
  have hSub :
      closureFromTrace agentSurface agentFrontier agentRules (0 : Multiset AgentObservation) ⊆
        (∅ : Set AgentQuery) := by
    exact
      leastRuleClosure_least_of_seed_and_rules
        (R := agentRules)
        (W := (0 : Multiset AgentObservation))
        (seed := traceSeed agentFrontier (0 : Multiset AgentObservation))
        (S := (∅ : Set AgentQuery))
        (by simp)
        (by
          intro r hr hside
          rcases hr with rfl | rfl <;> simp at hside)
  intro hmem
  exact hSub hmem

/-- Golden PoC:
nonempty observation traces give bounded Hyperseed discovery of a self-aware
query, and the underlying induced WM state is certifiably nontrivial. -/
theorem selfAware_golden_poc_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∈
        closureFromTrace agentSurface agentFrontier agentRules σ ∧
      AgentQuery.awareReady ∈
        cascadeFromTrace agentSurface agentFrontier agentRules σ (Fintype.card AgentQuery) ∧
      GenericWorldModel.queryObservationCount
          (State := Multiset AgentObservation) (Query := AgentQuery) (Ev := Evidence)
          σ AgentQuery.awareReady ≠ 0 ∧
      (σ + σ : Multiset AgentObservation) ≠ σ := by
  have hClosure := awareReady_in_closure_of_nonempty hσ
  have hCascade :
      AgentQuery.awareReady ∈
        cascadeFromTrace agentSurface agentFrontier agentRules σ (Fintype.card AgentQuery) := by
    exact
      (mem_closureFromTrace_iff_mem_cascade_card_of_finite
        agentSurface agentFrontier agentRules σ AgentQuery.awareReady).mp hClosure
  have hNontrivial :=
    wm_nonempty_implies_nontrivial
      (S := agentSurface) agentSurface_unitObservation hσ AgentQuery.awareReady
  exact ⟨hClosure, hCascade, hNontrivial.1, hNontrivial.2⟩

/-- Trivial converse packaging for the same PoC fixture:
empty observation traces are exactly the count-zero / revision-idempotent case. -/
theorem selfAware_triviality_iff
    (σ : Multiset AgentObservation) :
    letI : EvidenceType (Multiset AgentObservation) := multisetEvidenceType AgentObservation
    letI : GenericWorldModel (Multiset AgentObservation) AgentQuery Evidence := agentSurface.inducedWorldModel
    ((σ + σ : Multiset AgentObservation) = σ ↔ σ = 0) ∧
      (GenericWorldModel.queryObservationCount
          (State := Multiset AgentObservation) (Query := AgentQuery) (Ev := Evidence)
          σ AgentQuery.awareReady = 0 ↔ σ = 0) := by
  exact wm_trivial_iff (S := agentSurface) agentSurface_unitObservation σ AgentQuery.awareReady

end Mettapedia.Hyperseed.Regression
