import Mettapedia.Hyperseed.ObservationTrace
import Mettapedia.Logic.PLNWorldModelFixpointCascade

/-!
# Hyperseed: Closure Wrappers

Thin wrappers over the existing `PLNWorldModelFixpointClosure` machinery,
specialized to a `HyperseedKernel`.

Does not invent new closure semantics — just repackages `leastRuleClosure`,
`immediateIter`, and threshold transport using the kernel's rule pool and
seed queries.
-/

namespace Mettapedia.Hyperseed

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open Mettapedia.Logic.PLNWorldModelFixpointCascade
open scoped ENNReal

variable {Obs State Query : Type*}
variable [EvidenceType State] [WorldModel State Query]

/-- Least rule closure of the kernel's seed queries under its rule pool,
evaluated at WM state `W`. -/
noncomputable def hyperseedClosure
    (k : HyperseedKernel Obs State Query) (W : State) : Set Query :=
  leastRuleClosure k.rules W k.seedQueries

/-- One step of the kernel's immediate consequence operator. -/
def hyperseedImmediateIter
    (k : HyperseedKernel Obs State Query) (W : State) (n : ℕ) : Set Query :=
  immediateIter k.rules W k.seedQueries n

/-- Query strength in the kernel's closure at state `W`. -/
noncomputable def hyperseedQueryStrength
    (_k : HyperseedKernel Obs State Query) (W : State) (q : Query) : ℝ≥0∞ :=
  WorldModel.queryStrength (State := State) (Query := Query) W q

/-- Seed queries are contained in the Hyperseed closure. -/
theorem seed_subset_hyperseedClosure
    (k : HyperseedKernel Obs State Query) (W : State) :
    k.seedQueries ⊆ hyperseedClosure k W :=
  seed_subset_leastRuleClosure k.rules W k.seedQueries

/-- If seed obligations hold at threshold `τ`, all closure members inherit `τ`. -/
theorem hyperseedClosure_thresholdValid
    (k : HyperseedKernel Obs State Query) (W : State) (τ : ℝ≥0∞)
    (hSeed : thresholdValid (State := State) (Query := Query) W τ k.seedQueries) :
    thresholdValid (State := State) (Query := Query) W τ (hyperseedClosure k W) :=
  leastRuleClosure_thresholdValid k.rules W k.seedQueries τ hSeed

/-- On finite query spaces, the Hyperseed closure is reached by time `card(Query)`. -/
theorem hyperseedImmediateIter_eq_closure_at_card [Fintype Query]
    (k : HyperseedKernel Obs State Query) (W : State) :
    hyperseedImmediateIter k W (Fintype.card Query) = hyperseedClosure k W :=
  immediateIter_eq_leastRuleClosure_at_card_of_finite
    k.rules W k.seedQueries

end Mettapedia.Hyperseed
