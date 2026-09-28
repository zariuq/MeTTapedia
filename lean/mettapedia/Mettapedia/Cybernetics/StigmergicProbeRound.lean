import Mettapedia.ProbabilityTheory.IndependentFiniteSampling

/-!
# A synchronous stigmergic probe round

This is a discrete synchronous algorithm, not a continuous-time chemical
simulation. A round first receives a finite batch of emitted probes, then moves
every old and emitted probe using one frozen snapshot. Independent per-identity
sampling gives the product distribution. Rendezvous enumerates all matching
pairs without consuming either population. Deposits change the next snapshot.

The finite-batch theorem is conditional on the emitted batch. An unbounded
Poisson emission process, or a random shared trail field, requires a further
mixture; the fixed-snapshot product law must not be applied after forgetting
that conditioning.
-/

namespace Mettapedia.Cybernetics.StigmergicProbeRound

open scoped BigOperators ENNReal NNReal
open Mettapedia.ProbabilityTheory.IndependentFiniteSampling

noncomputable section

variable {I J E A B V S : Type*}

/-- Multiplicity of a state in an indexed population. Identities, not values,
distinguish probes, so duplicate values still count separately. -/
def count [Fintype I] [DecidableEq A] (xs : I → A) (a : A) : ℕ :=
  (Finset.univ.filter fun i => xs i = a).card

/-- A real-valued histogram, convenient for finite expectations. -/
def density [Fintype I] [DecidableEq A] (xs : I → A) (a : A) : ℝ :=
  ∑ i, if xs i = a then 1 else 0

theorem density_eq_count [Fintype I] [DecidableEq A] (xs : I → A) (a : A) :
    density xs a = count xs a := by
  simp only [density, count, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- The finite step matrix acts on a population's expected density. -/
def pushDensity [Fintype A] (n : A → ℝ) (kernel : A → PMF B) (b : B) : ℝ :=
  ∑ a, n a * mass (kernel a) b

/-- Every newly emitted probe participates in this round's step. -/
def roundLaw [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    [Fintype B] (snapshot : S) (kernel : S → A → PMF B)
    (old : I → A) (emitted : E → A) : PMF ((I ⊕ E) → B) :=
  independent fun i => kernel snapshot (Sum.elim old emitted i)

theorem expectation_indicator [Fintype A] [DecidableEq A] (p : PMF A) (a : A) :
    expectation p (fun x => if x = a then 1 else 0) = mass p a := by
  simp [expectation]

theorem expectation_density [Fintype I] [DecidableEq I] [Fintype A]
    [DecidableEq A] (p : I → PMF A) (a : A) :
    expectation (independent p) (fun xs => density xs a) = ∑ i, mass (p i) a := by
  unfold density
  rw [expectation_independent_sum p (fun _ x => if x = a then 1 else 0)]
  simp_rw [expectation_indicator]

theorem sum_kernel_eq_pushDensity [Fintype I] [Fintype A] [DecidableEq A]
    (xs : I → A) (kernel : A → PMF B) (b : B) :
    (∑ i, mass (kernel (xs i)) b) = pushDensity (density xs) kernel b := by
  unfold pushDensity density
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- Correct emission-before-step density equation: `(old + emitted) * K`.
The emitted density is pushed through the same kernel as the old population. -/
theorem round_expected_density [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (snapshot : S) (kernel : S → A → PMF B)
    (old : I → A) (emitted : E → A) (b : B) :
    expectation (roundLaw snapshot kernel old emitted) (fun xs => density xs b) =
      pushDensity (fun a => density old a + density emitted a) (kernel snapshot) b := by
  rw [roundLaw, expectation_density, Fintype.sum_sum_type]
  rw [sum_kernel_eq_pushDensity, sum_kernel_eq_pushDensity]
  simp [pushDensity, add_mul, Finset.sum_add_distrib]

/-- Nonconsuming rendezvous at a vertex, preserving both input identities. -/
def rendezvousAt [Fintype I] [Fintype J] [DecidableEq V]
    (forward : I → V) (backward : J → V) (v : V) : Finset (I × J) :=
  (Finset.univ.filter fun i => forward i = v) ×ˢ
    (Finset.univ.filter fun j => backward j = v)

@[simp] theorem mem_rendezvousAt [Fintype I] [Fintype J] [DecidableEq V]
    (forward : I → V) (backward : J → V) (v : V) (i : I) (j : J) :
    (i, j) ∈ rendezvousAt forward backward v ↔ forward i = v ∧ backward j = v := by
  simp [rendezvousAt]

theorem rendezvousAt_card [Fintype I] [Fintype J] [DecidableEq V]
    (forward : I → V) (backward : J → V) (v : V) :
    (rendezvousAt forward backward v).card = count forward v * count backward v := by
  simp [rendezvousAt, count]

theorem rendezvousAt_real_card [Fintype I] [Fintype J] [DecidableEq V]
    (forward : I → V) (backward : J → V) (v : V) :
    ((rendezvousAt forward backward v).card : ℝ) = density forward v * density backward v := by
  rw [rendezvousAt_card, Nat.cast_mul, density_eq_count, density_eq_count]

/-- Expected rendezvous multiplicity for independent populations at a fixed
snapshot. This counts every identity pair, including duplicates. -/
theorem expected_rendezvousAt [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    (forward : I → PMF V) (backward : J → PMF V) (v : V) :
    expectation (pair (independent forward) (independent backward))
      (fun xs => ((rendezvousAt xs.1 xs.2 v).card : ℝ)) =
      (∑ i, mass (forward i) v) * (∑ j, mass (backward j) v) := by
  simp_rw [rendezvousAt_real_card]
  rw [expectation_pair_product (independent forward) (independent backward)
    (fun xs => density xs v) (fun xs => density xs v),
    expectation_density, expectation_density]

/-- Summing per-node rendezvous counts retains the fixed-snapshot product law. -/
theorem expected_total_rendezvous [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    (forward : I → PMF V) (backward : J → PMF V) :
    expectation (pair (independent forward) (independent backward))
      (fun xs => ∑ v, ((rendezvousAt xs.1 xs.2 v).card : ℝ)) =
      ∑ v, (∑ i, mass (forward i) v) * (∑ j, mass (backward j) v) := by
  rw [expectation_sum]
  simp_rw [expected_rendezvousAt]

/-- Dead slots are excluded from the endpoint join, even though they remain in
the indexed sample space to keep probe identities stable. -/
def liveRendezvousAt [Fintype I] [Fintype J] [DecidableEq V]
    (forward : I → Option V) (backward : J → Option V) (v : V) : Finset (I × J) :=
  rendezvousAt forward backward (some v)

theorem expected_live_rendezvous [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    (forward : I → PMF (Option V)) (backward : J → PMF (Option V)) :
    expectation (pair (independent forward) (independent backward))
      (fun xs => ∑ v, ((liveRendezvousAt xs.1 xs.2 v).card : ℝ)) =
      ∑ v, (∑ i, mass (forward i) (some v)) * (∑ j, mass (backward j) (some v)) := by
  rw [expectation_sum]
  simp_rw [liveRendezvousAt, expected_rendezvousAt]

theorem nnExpectation_count [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (p : I → PMF A) (a : A) :
    nnExpectation (independent p) (fun xs => (count xs a : ℝ≥0∞)) = ∑ i, p i a := by
  have hc (xs : I → A) : (count xs a : ℝ≥0∞) = ∑ i, if xs i = a then 1 else 0 := by
    simp only [count, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  simp_rw [hc]
  rw [nnExpectation_sum]
  simp_rw [nnExpectation_coordinate p _ (fun x => if x = a then 1 else 0)]
  simp [nnExpectation, mul_ite]

theorem nn_expected_rendezvousAt [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    (forward : I → PMF V) (backward : J → PMF V) (v : V) :
    nnExpectation (pair (independent forward) (independent backward))
      (fun xs => ((rendezvousAt xs.1 xs.2 v).card : ℝ≥0∞)) =
      (∑ i, forward i v) * (∑ j, backward j v) := by
  simp_rw [rendezvousAt_card, Nat.cast_mul]
  rw [nnExpectation_pair_product (independent forward) (independent backward)
    (fun xs => (count xs v : ℝ≥0∞)) (fun xs => (count xs v : ℝ≥0∞)),
    nnExpectation_count, nnExpectation_count]

/-- The exact unconditional formula averages the *conditional* overlap. The
snapshot type may contain real-valued trail fields and need not be finite.
No product of unconditional mean densities is asserted. -/
theorem nn_expected_live_rendezvous_mixture [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    (snapshots : PMF S) (forward : S → I → PMF (Option V))
    (backward : S → J → PMF (Option V)) :
    nnExpectation (snapshots.bind fun s => pair (independent (forward s)) (independent (backward s)))
      (fun xs => ∑ v, ((liveRendezvousAt xs.1 xs.2 v).card : ℝ≥0∞)) =
      nnExpectation snapshots (fun s =>
        ∑ v, (∑ i, forward s i (some v)) * (∑ j, backward s j (some v))) := by
  rw [nnExpectation_bind]
  simp_rw [nnExpectation_sum, liveRendezvousAt, nn_expected_rendezvousAt]

/-! ## A bounded graph walker -/

/-- The depth bound is part of the state space. `none` denotes death. -/
abbrev Position (Vertex : Type*) (depthBound : ℕ) := Vertex × Fin (depthBound + 1)

/-- A frozen finite graph kernel. This definition does not refresh weights
between probes. Depth-limit death precedes the next graph transition. -/
def boundedStep {Vertex : Type*} (depthBound : ℕ) (edgeStep : Vertex → PMF (Option Vertex)) :
    Option (Position Vertex depthBound) → PMF (Option (Position Vertex depthBound))
  | none => PMF.pure none
  | some (v, d) =>
      if h : d.val < depthBound then
        (edgeStep v).map (Option.map fun v' => (v', ⟨d.val + 1, by omega⟩))
      else PMF.pure none

@[simp] theorem boundedStep_dead {Vertex : Type*} (depthBound : ℕ)
    (edgeStep : Vertex → PMF (Option Vertex)) :
    boundedStep depthBound edgeStep none = PMF.pure none := rfl

theorem boundedStep_at_limit {Vertex : Type*} (depthBound : ℕ)
    (edgeStep : Vertex → PMF (Option Vertex)) (v : Vertex) :
    boundedStep depthBound edgeStep (some (v, ⟨depthBound, by omega⟩)) = PMF.pure none := by
  simp [boundedStep]

theorem boundedStep_below_limit {Vertex : Type*} (depthBound : ℕ)
    (edgeStep : Vertex → PMF (Option Vertex)) (v : Vertex) (d : Fin (depthBound + 1))
    (h : d.val < depthBound) :
    boundedStep depthBound edgeStep (some (v, d)) =
      (edgeStep v).map (Option.map fun v' => (v', ⟨d.val + 1, by omega⟩)) := by
  simp [boundedStep, h]

inductive Side where
  | forward
  | backward
  deriving DecidableEq

/-- Persistent graph data and the selection weights frozen for this round.
Weights may already include heuristic factors and snapshot funding gates. -/
structure WeightedGraph (Vertex Edge : Type*) where
  source : Edge → Vertex
  target : Edge → Vertex
  weight : Edge → ℝ≥0

def WeightedGraph.start {Vertex Edge : Type*} (graph : WeightedGraph Vertex Edge) :
    Side → Edge → Vertex
  | .forward => graph.source
  | .backward => graph.target

def WeightedGraph.finish {Vertex Edge : Type*} (graph : WeightedGraph Vertex Edge) :
    Side → Edge → Vertex
  | .forward => graph.target
  | .backward => graph.source

/-- Parallel edges retain their separate identities in the categorical draw. -/
def WeightedGraph.eligibleWeight {Vertex Edge : Type*} [DecidableEq Vertex]
    (graph : WeightedGraph Vertex Edge) (side : Side) (v : Vertex) (e : Edge) : ℝ≥0 :=
  if graph.start side e = v then graph.weight e else 0

def WeightedGraph.chooseEdge {Vertex Edge : Type*} [Fintype Edge] [DecidableEq Vertex]
    (graph : WeightedGraph Vertex Edge) (side : Side) (v : Vertex) : PMF (Option Edge) :=
  weightedChoice (graph.eligibleWeight side v)

theorem WeightedGraph.chooseEdge_probability {Vertex Edge : Type*}
    [Fintype Edge] [DecidableEq Vertex] (graph : WeightedGraph Vertex Edge)
    (side : Side) (v : Vertex) (e : Edge)
    (enabled : ∑ e, graph.eligibleWeight side v e ≠ 0) :
    graph.chooseEdge side v (some e) =
      (graph.eligibleWeight side v e : ℝ≥0∞) *
        (∑ e, (graph.eligibleWeight side v e : ℝ≥0∞))⁻¹ :=
  weightedChoice_some _ enabled _

/-- An edge outside the current oriented adjacency has probability zero,
including the no-enabled-edge case. -/
theorem WeightedGraph.chooseEdge_foreign_zero {Vertex Edge : Type*}
    [Fintype Edge] [DecidableEq Vertex] (graph : WeightedGraph Vertex Edge)
    (side : Side) (v : Vertex) (e : Edge) (foreign : graph.start side e ≠ v) :
    graph.chooseEdge side v (some e) = 0 := by
  by_cases enabled : ∑ e, graph.eligibleWeight side v e = 0
  · simp [WeightedGraph.chooseEdge, weightedChoice_zero _ enabled, PMF.pure_apply]
  · rw [graph.chooseEdge_probability side v e enabled]
    simp [WeightedGraph.eligibleWeight, foreign]

/-- Actual weighted, bounded movement. No enabled edge or an exhausted depth
budget produces death. Both directions read the same frozen graph. -/
def WeightedGraph.step {Vertex Edge : Type*} [Fintype Edge] [DecidableEq Vertex]
    (graph : WeightedGraph Vertex Edge) (side : Side) (depthBound : ℕ) :
    Option (Position Vertex depthBound) → PMF (Option (Position Vertex depthBound)) :=
  boundedStep depthBound fun v => (graph.chooseEdge side v).map (Option.map (graph.finish side))

theorem WeightedGraph.step_at_limit {Vertex Edge : Type*}
    [Fintype Edge] [DecidableEq Vertex] (graph : WeightedGraph Vertex Edge)
    (side : Side) (depthBound : ℕ) (v : Vertex) :
    graph.step side depthBound (some (v, ⟨depthBound, by omega⟩)) = PMF.pure none := by
  simp [WeightedGraph.step, boundedStep]

theorem WeightedGraph.step_dead_end {Vertex Edge : Type*}
    [Fintype Edge] [DecidableEq Vertex] (graph : WeightedGraph Vertex Edge)
    (side : Side) (depthBound : ℕ) (v : Vertex) (d : Fin (depthBound + 1))
    (disabled : ∑ e, graph.eligibleWeight side v e = 0) :
    graph.step side depthBound (some (v, d)) = PMF.pure none := by
  by_cases h : d.val < depthBound
  · simp [WeightedGraph.step, boundedStep, h, WeightedGraph.chooseEdge,
      weightedChoice_zero _ disabled, PMF.pure_map]
  · simp [WeightedGraph.step, boundedStep, h]

/-- Deterministic realization after a logical probe's edge choice has been
supplied. No worker identity or scheduling order enters this function. -/
def WeightedGraph.advance {Vertex Edge : Type*} (graph : WeightedGraph Vertex Edge)
    (side : Side) (depthBound : ℕ) (position : Option (Position Vertex depthBound))
    (choice : Option Edge) : Option (Position Vertex depthBound) :=
  match position with
  | none => none
  | some (_, d) => if h : d.val < depthBound then
      choice.map fun e => (graph.finish side e, ⟨d.val + 1, by omega⟩)
    else none

/-- The weighted kernel is exactly the pushforward of the per-probe edge law
through the deterministic realization, including depth-limit death. -/
theorem WeightedGraph.step_eq_map_advance {Vertex Edge : Type*}
    [Fintype Edge] [DecidableEq Vertex] (graph : WeightedGraph Vertex Edge)
    (side : Side) (depthBound : ℕ) (v : Vertex) (d : Fin (depthBound + 1)) :
    graph.step side depthBound (some (v, d)) =
      (graph.chooseEdge side v).map (graph.advance side depthBound (some (v, d))) := by
  change graph.step side depthBound (some (v, d)) =
    (graph.chooseEdge side v).map (fun choice => graph.advance side depthBound (some (v, d)) choice)
  by_cases h : d.val < depthBound
  · simp [WeightedGraph.step, boundedStep, WeightedGraph.advance, h, PMF.map_comp,
      Function.comp_def, Option.map_map]
  · simp only [WeightedGraph.step, boundedStep, WeightedGraph.advance, h]
    exact (PMF.map_const _ _).symm

/-! ## Trail state is not a propensity -/

/-- Trail deposition and evaporation update the stored trail. Selection weights
are computed from the updated trail; they are not themselves the trail. -/
def updateTrail (floor evaporation trail deposit : ℝ) : ℝ :=
  max floor ((1 - evaporation) * trail + deposit)

def propensity (trail heuristic : ℝ) (alpha beta : ℕ) : ℝ :=
  trail ^ alpha * heuristic ^ beta

theorem updateTrail_floor (floor evaporation trail deposit : ℝ) :
    floor ≤ updateTrail floor evaporation trail deposit := le_max_left _ _

theorem updateTrail_monotone_deposit (floor evaporation trail : ℝ)
    {left right : ℝ} (h : left ≤ right) :
    updateTrail floor evaporation trail left ≤ updateTrail floor evaporation trail right := by
  exact max_le_max le_rfl (by linarith)

/-- End-of-round deposition uses the complete live endpoint join and updates
the trail once. Both probe populations, including their payloads, are retained.
`credit` specifies the per-bridge control deposit. -/
def finishRound [Fintype I] [Fintype J] [Fintype V] [DecidableEq V]
    (forward : I → A) (backward : J → B) (forwardNode : A → Option V)
    (backwardNode : B → Option V) (trail : E → ℝ) (floor evaporation : ℝ)
    (credit : A → B → E → ℝ) : (I → A) × (J → B) × (E → ℝ) :=
  (forward, backward, fun e => updateTrail floor evaporation (trail e)
    (∑ v, ∑ ij ∈ liveRendezvousAt (forwardNode ∘ forward) (backwardNode ∘ backward) v,
      credit (forward ij.1) (backward ij.2) e))

/-- Full fixed-snapshot round law, after emission has chosen the identity sets.
Independent movement is followed by nonconsuming joins and one trail update. -/
def completeRound [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype A] [Fintype B] [Fintype V] [DecidableEq V]
    (forward : I → PMF A) (backward : J → PMF B) (forwardNode : A → Option V)
    (backwardNode : B → Option V) (trail : E → ℝ) (floor evaporation : ℝ)
    (credit : A → B → E → ℝ) : PMF ((I → A) × (J → B) × (E → ℝ)) :=
  (pair (independent forward) (independent backward)).map fun populations =>
    finishRound populations.1 populations.2 forwardNode backwardNode trail floor evaporation credit

/-- Depositing and publishing all pairs does not consume or resample probes:
the entire joint population law is retained, not merely its cardinality. -/
theorem completeRound_population_law [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype A] [Fintype B] [Fintype V] [DecidableEq V]
    (forward : I → PMF A) (backward : J → PMF B) (forwardNode : A → Option V)
    (backwardNode : B → Option V) (trail : E → ℝ) (floor evaporation : ℝ)
    (credit : A → B → E → ℝ) :
    (completeRound forward backward forwardNode backwardNode trail floor evaporation credit).map
      (fun result => (result.1, result.2.1)) =
      pair (independent forward) (independent backward) := by
  rw [completeRound, PMF.map_comp]
  exact PMF.map_id _

/-! ## Controls distinguishing the repaired semantics -/

namespace Controls

theorem one_forward_two_backward_means_two_bridges :
    (rendezvousAt (fun _ : Fin 1 => false) (fun _ : Fin 2 => false) false).card = 2 := by
  simp [rendezvousAt]

/-- This is a nonconsuming join, so its count exceeds the capacity of a
consuming match in this example. -/
theorem nonconsuming_join_is_not_a_consuming_meet :
    (rendezvousAt (fun _ : Fin 1 => false) (fun _ : Fin 2 => false) false).card >
      min (Fintype.card (Fin 1)) (Fintype.card (Fin 2)) := by
  rw [one_forward_two_backward_means_two_bridges]
  decide

theorem absent_endpoint_has_no_bridge :
    (rendezvousAt (fun _ : Fin 1 => false) (fun _ : Fin 2 => true) false).card = 0 := by
  simp [rendezvousAt]

theorem dead_slots_do_not_rendezvous (v : Bool) :
    (liveRendezvousAt (fun _ : Fin 1 => none) (fun _ : Fin 2 => none) v).card = 0 := by
  simp [liveRendezvousAt, rendezvousAt]

def fairCoin : PMF Bool :=
  PMF.ofFintype (fun _ => (1 / 2 : ℝ≥0∞)) (by
    simp only [Fintype.sum_bool, one_div, ← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by simp))

def indicator (b : Bool) : ℝ := if b then 1 else 0

theorem fairCoin_mean : expectation fairCoin indicator = 1 / 2 := by
  norm_num [expectation, mass, fairCoin, indicator, Fintype.sum_bool, ENNReal.toReal_div]

/-- A shared random environment correlates populations even though they are
independent after fixing that environment. -/
theorem shared_coin_pair_expectation :
    expectation (fairCoin.bind fun b => pair (PMF.pure b) (PMF.pure b))
      (fun ab => indicator ab.1 * indicator ab.2) = 1 / 2 := by
  rw [expectation_shared_environment]
  norm_num [expectation, mass, fairCoin, indicator, Fintype.sum_bool,
    ENNReal.toReal_div, PMF.pure_apply]

theorem shared_coin_not_product_of_unconditional_means :
    expectation (fairCoin.bind fun b => pair (PMF.pure b) (PMF.pure b))
      (fun ab => indicator ab.1 * indicator ab.2) ≠
      expectation fairCoin indicator * expectation fairCoin indicator := by
  rw [shared_coin_pair_expectation, fairCoin_mean]
  norm_num

theorem emission_is_moved_in_its_birth_round :
    expectation (roundLaw () (fun _ b => PMF.pure (!b))
      (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => false))
      (fun xs => density xs true) = 1 := by
  rw [roundLaw, expectation_density]
  norm_num [Fintype.sum_sum_type, mass, PMF.pure_apply]

theorem updating_nonlinear_propensity_is_not_depositing_on_trail :
    propensity (updateTrail 0 0 2 1) 1 2 0 ≠ propensity 2 1 2 0 + 1 := by
  norm_num [propensity, updateTrail]

end Controls
end

end Mettapedia.Cybernetics.StigmergicProbeRound
