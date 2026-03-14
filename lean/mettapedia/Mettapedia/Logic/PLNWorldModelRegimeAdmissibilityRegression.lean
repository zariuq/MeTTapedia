import Mettapedia.Logic.PLNWorldModelRegimeAdmissibility
import Mettapedia.Hyperseed.Regression

/-!
# WM Regime Admissibility Regression

Concrete finite fixture showing that the same induced WM can support different
admissible discoveries under different Hyperseed-style regimes.

Positive examples:
- nonempty states make threshold `1` valid for the whole query space;
- `readyToAct` is WM-admissible under the grounded regime;
- `awareReady` is WM-admissible under the regime-sensitive perspective.

Negative examples:
- `awareReady` is not WM-admissible under the grounded regime;
- `awareReady` is not WM-admissible in the empty regime-sensitive state.
-/

namespace Mettapedia.Logic.PLNWorldModelRegimeAdmissibilityRegression

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open Mettapedia.Logic.PLNWorldModelRegimeAdmissibility
open Mettapedia.Logic.SufficientStatisticSurface
open Mettapedia.Hyperseed
open Mettapedia.Hyperseed.Regression
open scoped ENNReal

/-- Freeze the grounded query perspective uniformly across states so it can be
compared directly with the state-sensitive regime. -/
def groundedStatefulQueryPerspective :
    StatefulPerspective (Multiset AgentObservation) AgentQuery AgentSignal ℕ where
  signalClass _ := groundedQueryPerspective.signalClass
  reaches _ := groundedQueryPerspective.reaches
  effort _ := groundedQueryPerspective.effort

theorem agentSurface_aggregate_eq_card_unitPositiveEvidence
    (σ : Multiset AgentObservation) (q : AgentQuery) :
    aggregate agentSurface σ q = { pos := σ.card, neg := 0 } := by
  induction σ using Multiset.induction_on with
  | empty =>
      rw [aggregate_zero]
      apply Evidence.ext'
      · change Evidence.pos Evidence.zero = ((0 : ℕ) : ℝ≥0∞)
        simp [Evidence.zero]
      · change Evidence.neg Evidence.zero = (0 : ℝ≥0∞)
        simp [Evidence.zero]
  | @cons o σ ih =>
      rw [aggregate_cons]
      rw [ih]
      apply Evidence.ext'
      · simp [agentSurface, SufficientStatisticSurface.ofObservationMap,
          unitPositiveEvidence, Evidence.hplus_def, add_comm]
      · simp [agentSurface, SufficientStatisticSurface.ofObservationMap,
          unitPositiveEvidence, Evidence.hplus_def]

theorem agentWorldModel_queryStrength_eq_zero_of_empty
    (q : AgentQuery) :
    WorldModel.queryStrength
        (State := Multiset AgentObservation) (Query := AgentQuery)
        (0 : Multiset AgentObservation) q = 0 := by
  unfold WorldModel.queryStrength
  rw [agentWorldModel_evidence_eq_aggregate]
  rw [agentSurface_aggregate_eq_card_unitPositiveEvidence]
  simp [Evidence.toStrength, Evidence.total]

theorem agentWorldModel_queryStrength_eq_one_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) (q : AgentQuery) :
    WorldModel.queryStrength
        (State := Multiset AgentObservation) (Query := AgentQuery)
        σ q = 1 := by
  unfold WorldModel.queryStrength
  rw [agentWorldModel_evidence_eq_aggregate]
  rw [agentSurface_aggregate_eq_card_unitPositiveEvidence]
  have hcard : (σ.card : ℝ≥0∞) ≠ 0 := by
    have hcardNat : σ.card ≠ 0 := by
      simpa [Multiset.card_eq_zero] using hσ
    exact_mod_cast hcardNat
  simp [Evidence.toStrength, Evidence.total, hcard]
  exact ENNReal.div_self hcard (ENNReal.natCast_ne_top _)

theorem agent_thresholdValid_univ_one_of_nonempty
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    thresholdValid
      (State := Multiset AgentObservation) (Query := AgentQuery)
      σ 1 Set.univ := by
  intro q _hq
  simp [agentWorldModel_queryStrength_eq_one_of_nonempty hσ q]

theorem availableRegionAt_thresholdValid_one_of_nonempty
    (P : StatefulPerspective (Multiset AgentObservation) AgentQuery AgentSignal ℕ)
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) (B : ℕ) (guard : Set AgentQuery) :
    thresholdValid
      (State := Multiset AgentObservation) (Query := AgentQuery)
      σ 1 (availableRegionAt P σ B guard) := by
  exact
    thresholdValid_mono
      (State := Multiset AgentObservation) (Query := AgentQuery)
      (W := σ) (τ := 1)
      (hS := by
        intro q _hq
        simp)
      (hV := agent_thresholdValid_univ_one_of_nonempty hσ)

theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_nonempty
    (P : StatefulPerspective (Multiset AgentObservation) AgentQuery AgentSignal ℕ)
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) (B : ℕ) (guard : Set AgentQuery) :
    wmAdmissibleRegionAt
        (State := Multiset AgentObservation) (Query := AgentQuery)
        P σ B guard 1 =
      availableRegionAt P σ B guard := by
  exact
    wmAdmissibleRegionAt_eq_availableRegionAt_of_thresholdValid
      (State := Multiset AgentObservation) (Query := AgentQuery)
      P σ B guard 1
      (availableRegionAt_thresholdValid_one_of_nonempty P hσ B guard)

theorem readyToAct_in_availableRegionAt_groundedStateful_budget2
    (σ : Multiset AgentObservation) :
    AgentQuery.readyToAct ∈
      availableRegionAt groundedStatefulQueryPerspective σ 2 Set.univ := by
  simpa [groundedStatefulQueryPerspective, freezePerspective] using
    readyToAct_mem_availableRegion_grounded_budget2

theorem awareReady_not_mem_availableRegionAt_groundedStateful_budget3
    (σ : Multiset AgentObservation) :
    AgentQuery.awareReady ∉
      availableRegionAt groundedStatefulQueryPerspective σ 3 Set.univ := by
  intro h
  have hObs :
      AgentQuery.awareReady ∈
        observableUniverseAt groundedStatefulQueryPerspective σ := by
    exact
      availableRegionAt_subset_observableUniverseAt
        groundedStatefulQueryPerspective σ 3 Set.univ h
  rcases hObs with ⟨s, hs, hreach⟩
  cases s
  · simp [groundedStatefulQueryPerspective, groundedQueryPerspective, freezePerspective] at hreach
  · simp [groundedStatefulQueryPerspective, groundedQueryPerspective, freezePerspective] at hs

theorem readyToAct_in_wmAdmissibleRegionAt_grounded_nonempty_budget2_threshold1
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.readyToAct ∈
      wmAdmissibleRegionAt
        (State := Multiset AgentObservation) (Query := AgentQuery)
        groundedStatefulQueryPerspective σ 2 Set.univ 1 := by
  rw [wmAdmissibleRegionAt_eq_availableRegionAt_of_nonempty
    groundedStatefulQueryPerspective hσ 2 Set.univ]
  exact readyToAct_in_availableRegionAt_groundedStateful_budget2 σ

theorem awareReady_not_mem_wmAdmissibleRegionAt_grounded_nonempty_budget3_threshold1
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∉
      wmAdmissibleRegionAt
        (State := Multiset AgentObservation) (Query := AgentQuery)
        groundedStatefulQueryPerspective σ 3 Set.univ 1 := by
  rw [wmAdmissibleRegionAt_eq_availableRegionAt_of_nonempty
    groundedStatefulQueryPerspective hσ 3 Set.univ]
  exact awareReady_not_mem_availableRegionAt_groundedStateful_budget3 σ

theorem awareReady_in_wmAdmissibleRegionAt_regimeSensitive_nonempty_budget3_threshold1
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∈
      wmAdmissibleRegionAt
        (State := Multiset AgentObservation) (Query := AgentQuery)
        regimeSensitiveQueryPerspective σ 3 Set.univ 1 := by
  rw [wmAdmissibleRegionAt_eq_availableRegionAt_of_nonempty
    regimeSensitiveQueryPerspective hσ 3 Set.univ]
  exact awareReady_in_availableRegionAt_regimeSensitive_nonempty_budget3 hσ

theorem awareReady_not_mem_wmAdmissibleRegionAt_regimeSensitive_empty_budget3_threshold1 :
    AgentQuery.awareReady ∉
      wmAdmissibleRegionAt
        (State := Multiset AgentObservation) (Query := AgentQuery)
        regimeSensitiveQueryPerspective (0 : Multiset AgentObservation) 3 Set.univ 1 := by
  intro h
  exact awareReady_not_mem_availableRegionAt_regimeSensitive_empty_budget3 h.1

/-- Same induced WM, same nonempty state, different regimes: the grounded
regime blocks introspective discovery, while the regime-sensitive one admits it. -/
theorem sameWM_differentRegimes_differentAdmissibleDiscoveries
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∉
        wmAdmissibleRegionAt
          (State := Multiset AgentObservation) (Query := AgentQuery)
          groundedStatefulQueryPerspective σ 3 Set.univ 1 ∧
      AgentQuery.awareReady ∈
        wmAdmissibleRegionAt
          (State := Multiset AgentObservation) (Query := AgentQuery)
          regimeSensitiveQueryPerspective σ 3 Set.univ 1 := by
  exact
    ⟨awareReady_not_mem_wmAdmissibleRegionAt_grounded_nonempty_budget3_threshold1 hσ,
      awareReady_in_wmAdmissibleRegionAt_regimeSensitive_nonempty_budget3_threshold1 hσ⟩

/-- The same query is derivable in Hyperseed closure for a nonempty trace, but
regime choice still controls WM admissibility. -/
theorem awareReady_in_closure_but_regime_sensitive_for_wm_admissibility
    {σ : Multiset AgentObservation}
    (hσ : σ ≠ 0) :
    AgentQuery.awareReady ∈
        closureFromTrace agentSurface agentFrontier agentRules σ ∧
      AgentQuery.awareReady ∉
        wmAdmissibleRegionAt
          (State := Multiset AgentObservation) (Query := AgentQuery)
          groundedStatefulQueryPerspective σ 3 Set.univ 1 ∧
      AgentQuery.awareReady ∈
        wmAdmissibleRegionAt
          (State := Multiset AgentObservation) (Query := AgentQuery)
          regimeSensitiveQueryPerspective σ 3 Set.univ 1 := by
  exact
    ⟨awareReady_in_closure_of_nonempty hσ,
      awareReady_not_mem_wmAdmissibleRegionAt_grounded_nonempty_budget3_threshold1 hσ,
      awareReady_in_wmAdmissibleRegionAt_regimeSensitive_nonempty_budget3_threshold1 hσ⟩

end Mettapedia.Logic.PLNWorldModelRegimeAdmissibilityRegression
