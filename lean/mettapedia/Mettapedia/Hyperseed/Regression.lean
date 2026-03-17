import Mettapedia.Hyperseed.Basic

/-!
# Hyperseed Regression

Golden PoC for the new Hyperseed front door:

- a nonempty observation trace seeds a perception query,
- Hyperseed closure derives readiness and then self-awareness,
- the underlying sufficient-statistics world model is provably nontrivial.

Positive example:
- nonempty trace => `awareReady` is discovered and the WM state has nonzero count.

Negative example:
- empty trace => `awareReady` is not in closure.
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

inductive AgentSignal where
  | surface
  | introspection
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

/-- Grounded perspective on the query space: ordinary surface access reaches the
seed and first derived action query, but not the introspective one. -/
def groundedQueryPerspective : Perspective AgentQuery AgentSignal ℕ where
  signalClass := {AgentSignal.surface}
  reaches s q :=
    match s, q with
    | .surface, .sensedSignal => True
    | .surface, .readyToAct => True
    | _, _ => False
  effort q :=
    match q with
    | .sensedSignal => 1
    | .readyToAct => 2
    | .awareReady => 3

/-- Expanded perspective: introspective access now reaches `awareReady`. -/
def expansiveQueryPerspective : Perspective AgentQuery AgentSignal ℕ where
  signalClass := {AgentSignal.surface, AgentSignal.introspection}
  reaches s q :=
    match s, q with
    | .surface, .sensedSignal => True
    | .surface, .readyToAct => True
    | .introspection, .awareReady => True
    | _, _ => False
  effort := groundedQueryPerspective.effort

/-- Stage filtration for query accessibility by increasing effort. -/
def agentQueryStageView : StagedView (World := AgentQuery) ℕ where
  region n := { q | groundedQueryPerspective.effort q ≤ n + 1 }
  mono := by
    intro i j hij q hq
    exact le_trans hq (Nat.add_le_add_right hij 1)

/-- Regime-sensitive perspective: introspective access appears only once the
trace is nonempty, so the available region genuinely depends on state. -/
def regimeSensitiveQueryPerspective :
    StatefulPerspective (Multiset AgentObservation) AgentQuery AgentSignal ℕ where
  signalClass σ :=
    if σ = 0 then
      {AgentSignal.surface}
    else
      {AgentSignal.surface, AgentSignal.introspection}
  reaches σ s q :=
    match s, q with
    | .surface, .sensedSignal => True
    | .surface, .readyToAct => True
    | .introspection, .awareReady => σ ≠ 0
    | _, _ => False
  effort _ := groundedQueryPerspective.effort

theorem sensedSignalToReadyRule_mem_agentRules :
    sensedSignalToReadyRule ∈ agentRules := by
  simp [agentRules]

theorem readyToAwareRule_mem_agentRules :
    readyToAwareRule ∈ agentRules := by
  simp [agentRules]

theorem readyToAct_mem_availableRegion_grounded_budget2 :
    AgentQuery.readyToAct ∈
      availableRegion groundedQueryPerspective 2 Set.univ := by
  refine ⟨?_, ?_, by simp⟩
  · exact
      ⟨AgentSignal.surface, by simp [groundedQueryPerspective],
        by simp [groundedQueryPerspective]⟩
  · simp [nearEurycosm, sublevelRegion, groundedQueryPerspective]

theorem awareReady_not_mem_availableRegion_grounded_budget2 :
    AgentQuery.awareReady ∉
      availableRegion groundedQueryPerspective 2 Set.univ := by
  intro h
  have hNear :
      AgentQuery.awareReady ∈ nearEurycosm groundedQueryPerspective 2 := by
    exact availableRegion_subset_nearEurycosm groundedQueryPerspective 2 Set.univ h
  simp [nearEurycosm, sublevelRegion, groundedQueryPerspective] at hNear

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

theorem readyToAct_in_availableClosure_grounded_budget2_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.readyToAct ∈
      availableClosureFromTrace
        agentSurface agentFrontier agentRules σ groundedQueryPerspective 2 Set.univ := by
  exact ⟨readyToAct_in_closure_of_nonempty hσ, readyToAct_mem_availableRegion_grounded_budget2⟩

theorem awareReady_not_in_availableClosure_grounded_budget2
    {σ : Multiset AgentObservation} :
    AgentQuery.awareReady ∉
      availableClosureFromTrace
        agentSurface agentFrontier agentRules σ groundedQueryPerspective 2 Set.univ := by
  intro h
  have hAvail :
      AgentQuery.awareReady ∈
        availableRegion groundedQueryPerspective 2 Set.univ := by
    exact
      availableClosureFromTrace_subset_availableRegion
        agentSurface agentFrontier agentRules σ groundedQueryPerspective 2 Set.univ h
  exact awareReady_not_mem_availableRegion_grounded_budget2 hAvail

theorem closure_eq_availableClosure_expansive_budget3
    {σ : Multiset AgentObservation} :
    closureFromTrace agentSurface agentFrontier agentRules σ =
      availableClosureFromTrace
        agentSurface agentFrontier agentRules σ expansiveQueryPerspective 3 Set.univ := by
  apply
    closureFromTrace_eq_availableClosureFromTrace_of_subset_availableRegion
      agentSurface agentFrontier agentRules σ expansiveQueryPerspective 3 Set.univ
  intro q _hq
  cases q <;> simp [availableRegion, observableUniverse, nearEurycosm,
    sublevelRegion, expansiveQueryPerspective, groundedQueryPerspective]

theorem awareReady_not_mem_availableRegionAt_regimeSensitive_empty_budget3 :
    AgentQuery.awareReady ∉
      availableRegionAt
        regimeSensitiveQueryPerspective (0 : Multiset AgentObservation) 3 Set.univ := by
  intro h
  have hObs :
      AgentQuery.awareReady ∈
        observableUniverseAt regimeSensitiveQueryPerspective (0 : Multiset AgentObservation) := by
    exact
      availableRegionAt_subset_observableUniverseAt
        regimeSensitiveQueryPerspective (0 : Multiset AgentObservation) 3 Set.univ h
  rcases hObs with ⟨s, hs, hreach⟩
  cases s <;> simp [freezePerspective, regimeSensitiveQueryPerspective] at hs hreach

theorem awareReady_in_availableRegionAt_regimeSensitive_nonempty_budget3
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∈
      availableRegionAt regimeSensitiveQueryPerspective σ 3 Set.univ := by
  refine ⟨?_, ?_, by simp⟩
  · exact
      ⟨AgentSignal.introspection, by simp [freezePerspective, regimeSensitiveQueryPerspective, hσ],
        by simp [freezePerspective, regimeSensitiveQueryPerspective, hσ]⟩
  · simp [nearEurycosm, sublevelRegion,
      freezePerspective, regimeSensitiveQueryPerspective, groundedQueryPerspective]

theorem awareReady_in_availableCascade_expansive_budget3_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∈
      availableCascadeFromTrace
        agentSurface agentFrontier agentRules σ expansiveQueryPerspective 3 Set.univ
          (Fintype.card AgentQuery) := by
  have hClosure : AgentQuery.awareReady ∈
      closureFromTrace agentSurface agentFrontier agentRules σ := by
    exact awareReady_in_closure_of_nonempty hσ
  have hAvailableClosure :
      AgentQuery.awareReady ∈
        availableClosureFromTrace
          agentSurface agentFrontier agentRules σ expansiveQueryPerspective 3 Set.univ := by
    rw [← closure_eq_availableClosure_expansive_budget3 (σ := σ)]
    exact hClosure
  exact
    (mem_availableClosureFromTrace_iff_mem_availableCascade_card_of_finite
      agentSurface agentFrontier agentRules σ expansiveQueryPerspective 3 Set.univ
      AgentQuery.awareReady).mp hAvailableClosure

theorem stateAvailableClosure_eq_frozenAvailableClosure_regimeSensitive
    (σ : Multiset AgentObservation) :
    stateAvailableClosureFromTrace
      agentSurface agentFrontier agentRules σ regimeSensitiveQueryPerspective 3 Set.univ =
        availableClosureFromTrace
          agentSurface agentFrontier agentRules σ
            (freezePerspective regimeSensitiveQueryPerspective σ) 3 Set.univ := by
  rfl

theorem awareReady_in_stateAvailableClosure_regimeSensitive_budget3_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∈
      stateAvailableClosureFromTrace
        agentSurface agentFrontier agentRules σ regimeSensitiveQueryPerspective 3 Set.univ := by
  exact
    ⟨awareReady_in_closure_of_nonempty hσ,
      awareReady_in_availableRegionAt_regimeSensitive_nonempty_budget3 hσ⟩

theorem awareReady_not_in_stateAvailableClosure_regimeSensitive_budget3_of_empty :
    AgentQuery.awareReady ∉
      stateAvailableClosureFromTrace
        agentSurface agentFrontier agentRules
          (0 : Multiset AgentObservation) regimeSensitiveQueryPerspective 3 Set.univ := by
  intro h
  have hAvail :
      AgentQuery.awareReady ∈
        availableRegionAt
          regimeSensitiveQueryPerspective (0 : Multiset AgentObservation) 3 Set.univ := by
    exact
      stateAvailableClosureFromTrace_subset_availableRegionAt
        agentSurface agentFrontier agentRules
        (0 : Multiset AgentObservation) regimeSensitiveQueryPerspective 3 Set.univ h
  exact awareReady_not_mem_availableRegionAt_regimeSensitive_empty_budget3 hAvail

theorem awareReady_in_stateAvailableCascade_regimeSensitive_budget3_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∈
      stateAvailableCascadeFromTrace
        agentSurface agentFrontier agentRules σ regimeSensitiveQueryPerspective 3 Set.univ
          (Fintype.card AgentQuery) := by
  exact
    (mem_stateAvailableClosureFromTrace_iff_mem_stateAvailableCascade_card_of_finite
      agentSurface agentFrontier agentRules σ regimeSensitiveQueryPerspective 3 Set.univ
      AgentQuery.awareReady).mp
      (awareReady_in_stateAvailableClosure_regimeSensitive_budget3_of_nonempty hσ)

theorem readyToAct_in_stagedClosure_stage1_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.readyToAct ∈
      stagedClosureFromTrace agentSurface agentFrontier agentRules σ agentQueryStageView 1 := by
  exact ⟨readyToAct_in_closure_of_nonempty hσ, by simp [agentQueryStageView, groundedQueryPerspective]⟩

theorem awareReady_not_in_stagedClosure_stage1
    {σ : Multiset AgentObservation} :
    AgentQuery.awareReady ∉
      stagedClosureFromTrace agentSurface agentFrontier agentRules σ agentQueryStageView 1 := by
  intro h
  have hStage :
      AgentQuery.awareReady ∈ agentQueryStageView.region 1 := by
    exact stagedClosureFromTrace_subset_region
      agentSurface agentFrontier agentRules σ agentQueryStageView 1 h
  simp [agentQueryStageView, groundedQueryPerspective] at hStage

theorem awareReady_in_stagedClosure_stage2_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∈
      stagedClosureFromTrace agentSurface agentFrontier agentRules σ agentQueryStageView 2 := by
  exact ⟨awareReady_in_closure_of_nonempty hσ, by simp [agentQueryStageView, groundedQueryPerspective]⟩

theorem awareReady_in_stagedCascade_stage2_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∈
      stagedCascadeFromTrace agentSurface agentFrontier agentRules σ agentQueryStageView 2
        (Fintype.card AgentQuery) := by
  exact
    (mem_stagedClosureFromTrace_iff_mem_stagedCascade_card_of_finite
      agentSurface agentFrontier agentRules σ agentQueryStageView 2
      AgentQuery.awareReady).mp
      (awareReady_in_stagedClosure_stage2_of_nonempty hσ)

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
    σ = 0 ↔
      GenericWorldModel.queryObservationCount
          (State := Multiset AgentObservation) (Query := AgentQuery) (Ev := Evidence)
          σ AgentQuery.awareReady = 0 ∧
      (σ + σ : Multiset AgentObservation) = σ := by
  letI : EvidenceType (Multiset AgentObservation) := multisetEvidenceType AgentObservation
  letI : GenericWorldModel (Multiset AgentObservation) AgentQuery Evidence := agentSurface.inducedWorldModel
  constructor
  · intro hσ
    constructor
    · exact
        (queryObservationCount_inducedWorldModel_eq_zero_iff_empty_of_unit
          (S := agentSurface) agentSurface_unitObservation σ AgentQuery.awareReady).2 hσ
    · simpa [hσ]
  · intro h
    exact
      (revision_idempotent_inducedWorldModel_iff_empty_of_unit
        (S := agentSurface) agentSurface_unitObservation σ AgentQuery.awareReady).1 h.2

end Mettapedia.Hyperseed.Regression
