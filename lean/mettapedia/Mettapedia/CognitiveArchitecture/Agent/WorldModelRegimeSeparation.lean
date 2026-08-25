import Mettapedia.CognitiveArchitecture.Agent.ChronologicalWorldModel
import Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo
import Mettapedia.Logic.WorldModel.Basic
import Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

/-!
# Separation of Operational, Additive, and Contextual World Models

Source provenance: adapted from GödelClaw commit
`3a52d481c13b23926fcc42c9d171f33823d1f1c0`; only module packaging and
taxonomy-facing names were changed during integration.

The minimal world-model interface is broader than a probabilistic belief
state.  This file records three regimes needed by an autonomous coding agent:

* chronological operational state, whose updates may be order-sensitive;
* additive evidence, whose revision and extracted answers are commutative;
* contextual local charts, which may be answerable without admitting one
  classical global joint distribution.

The regimes may coexist as typed projections of one agent state.  They should
not be silently collapsed into one revision algebra.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.CognitiveArchitecture.Agent.ChronologicalWorldModel
open Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo

/-- Additive WM-PLN evidence revision is observationally commutative. -/
theorem additive_answers_commute
    {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev]
    [AdditiveWorldModel State Query Ev]
    (left right : State) (query : Query) :
    AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) (left + right) query =
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) (right + left) query := by
  rw [add_comm]

/-- A chronological operational world model can observably distinguish the
order of two updates, so it is not an additive-evidence model in disguise. -/
theorem chronological_answers_need_not_commute :
    let wm := chronologicalWorldModel natSemantics
    ∃ left right : List (Update Nat NatPatch),
      wm.extract (wm.revise left right) () ≠
        wm.extract (wm.revise right left) () := by
  refine ⟨[incrementUpdate], [doubleUpdate], ?_⟩
  decide

/-! ## Contextual local evidence without a forced global object -/

inductive PairContext where
  | xy
  | xz
  | yz
deriving DecidableEq, Repr

abbrev LocalChartState := PairContext → PairChart

def zeroChart : PairChart := ⟨0, 0, 0, 0⟩

/-- A deliberately weak world model for query-indexed local charts.  Revision
replaces the current materialized family; the interface imposes no claim that
all query answers are marginals of one global probability object. -/
@[reducible] def contextualChartWorldModel :
    WorldModel LocalChartState PairContext PairChart where
  revise _ newer := newer
  empty := fun _ => zeroChart
  extract charts query := charts query

def antiFamily : LocalChartState := fun _ => antiChart

@[simp] theorem antiFamily_extract (query : PairContext) :
    contextualChartWorldModel.extract antiFamily query = antiChart := by
  rfl

/-- A local chart family is globally realizable only when one classical joint
distribution has all three charts as its marginals. -/
def GloballyRealizable (charts : LocalChartState) : Prop :=
  ∃ joint : Joint3,
    joint.xy = charts .xy ∧ joint.xz = charts .xz ∧ joint.yz = charts .yz

/-- The generic world-model interface can retain and answer the compatible
local charts even though no classical global joint state realizes them. -/
theorem antiFamily_is_not_globally_realizable :
    ¬ GloballyRealizable antiFamily := by
  intro realizable
  apply antiChart_has_no_global_joint
  obtain ⟨joint, hxy, hxz, hyz⟩ := realizable
  exact ⟨joint, hxy, hxz, hyz⟩

/-- Local coherence checks normalization and every one-variable overlap, but
does not assume the existence of a joint object. -/
def LocallyCoherent (charts : LocalChartState) : Prop :=
  ∀ query,
    (charts query).leftMinus = 1 / 2 ∧
    (charts query).leftPlus = 1 / 2 ∧
    (charts query).rightMinus = 1 / 2 ∧
    (charts query).rightPlus = 1 / 2 ∧
    (charts query).total = 1

theorem antiFamily_is_locally_coherent :
    LocallyCoherent antiFamily := by
  intro query
  exact antiChart_has_uniform_overlaps

/-- **Multi-agent global-fusion no-go.** No total sound function can turn
every locally coherent family of pairwise reports into one classical global
joint distribution. -/
theorem no_total_global_fuser_from_local_coherence :
    ¬ Nonempty
      ((charts : LocalChartState) →
        LocallyCoherent charts → GloballyRealizable charts) := by
  rintro ⟨fuser⟩
  exact antiFamily_is_not_globally_realizable
    (fuser antiFamily antiFamily_is_locally_coherent)

/-- A sound joiner can expose either a realization witness or the retained
contextual family.  The second constructor is not a failure: it is the honest
answer when gluing is impossible. -/
inductive FusionResult (charts : LocalChartState) where
  | global (witness : GloballyRealizable charts)
  | contextual

def FusionResult.isContextual {charts : LocalChartState} :
    FusionResult charts → Prop
  | .global _ => False
  | .contextual => True

/-- Every sound result for the counterexample must take the contextual branch. -/
theorem antiFamily_forces_contextual
    (result : FusionResult antiFamily) :
    result.isContextual := by
  cases result with
  | global witness => exact False.elim (antiFamily_is_not_globally_realizable witness)
  | contextual => trivial

end Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation

#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation.additive_answers_commute
#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation.chronological_answers_need_not_commute
#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation.antiFamily_is_not_globally_realizable
#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation.no_total_global_fuser_from_local_coherence
#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation.antiFamily_forces_contextual
