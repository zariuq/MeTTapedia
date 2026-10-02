import Mettapedia.Cybernetics.ApproximateAdequacy.BisimulationMetric
import Mettapedia.Cybernetics.ApproximateAdequacy.DefectLaws
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# Worked example: a delivery over a slippery bridge

A delivery agent at the depot reaches the garden either over a wooden bridge
or over a hill.  On the bridge it slips with probability `p` and ends in the
ditch; the hill always succeeds.  The observable is whether the seedlings are
delivered.  A model of the world is the same chain with slip probability `q`.

**The probabilistic metric is the right notion here.**
* The bisimulation metric between the world and a model at the depot is
  exactly `c² (p - q)` for `q ≤ p` (`metric_depot`): pinned between a coupling
  bound (`couplingBound`) and the functional expression "deliver over the
  bridge" (`eval_bridgeDelivery`).  It varies continuously with the
  probabilities, and bounds every prediction.
* **Girard–Pappas approximate bisimulation of the supports misleads both
  ways.**  A model that slips rarely (`0 < q`) has the same supports as the
  world, so the supports are bisimilar at precision `0`
  (`supports_exact`), although the predicted delivery probability is off by
  `p - q`.  A model that never slips (`q = 0`) admits no approximate
  bisimulation of the supports below `1` (`supports_far`), although its
  predictions are off by only `p`, which may be arbitrarily small.
* **The correspondence defect is blind to both.**  The path-probability map
  of any step model is a functor on the free category of the route graph
  (`pathCorrespondence_exact`): defect `0` at every slip probability.  A
  model that caches a stale estimate for the whole bridge route has defect
  `1/5` (`cachedCorrespondence_defect`) even when its step model is the
  world's own.

**Today's goals are not tomorrow's** (`today_average_zero`,
`tomorrow_average`, `cached_conclusion_fails`): weighting the hill route,
today's goal, the average defect of the cached model is `0`; weighting the
bridge route, tomorrow's goal, it is `1/5`, and the cached conclusion "the
bridge route delivers with probability at least `17/20`" fails both by
composition and in the world, where the probability is `7/10`.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy.Delivery

open Finset CategoryTheory
open Mettapedia.Cybernetics.MindWorldApproximation
open Mettapedia.Cybernetics.MindWorldApproximateFunctor
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

/-! ## The chain -/

/-- Places of the delivery. -/
inductive Place
  | depot
  | bridge
  | hill
  | garden
  | slipped
  deriving DecidableEq

instance : Fintype Place where
  elems := {.depot, .bridge, .hill, .garden, .slipped}
  complete x := by cases x <;> simp

theorem sum_place {M : Type*} [AddCommMonoid M] (f : Place → M) :
    ∑ x, f x = f .depot + (f .bridge + (f .hill + (f .garden + f .slipped))) := by
  rw [show (Finset.univ : Finset Place) = {.depot, .bridge, .hill, .garden, .slipped} from rfl]
  simp

/-- The two routes, chosen at the depot. -/
inductive Route
  | viaBridge
  | viaHill
  deriving DecidableEq

instance : Fintype Route where
  elems := {.viaBridge, .viaHill}
  complete x := by cases x <;> simp

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The successor distribution with slip probability `p`. -/
def trans (p : 𝕜) (a : Route) (s : Place) : Place → 𝕜 :=
  match s, a with
  | .depot, .viaBridge => dirac .bridge
  | .depot, .viaHill => dirac .hill
  | .bridge, _ => fun x => if x = .garden then 1 - p else if x = .slipped then p else 0
  | .hill, _ => dirac .garden
  | .garden, _ => dirac .garden
  | .slipped, _ => dirac .slipped

/-- Delivered: `1` in the garden, `0` elsewhere. -/
def delivered (x : Place) : 𝕜 :=
  if x = .garden then 1 else 0

/-- **The delivery chain** with slip probability `p`. -/
def chain (p : 𝕜) (p_nonneg : 0 ≤ p) (p_le : p ≤ 1) : LabelledMarkovChain 𝕜 Route Unit Place where
  trans := trans p
  isDistribution a s := by
    cases s <;> cases a <;>
      first
        | exact isDistribution_dirac _
        | exact ⟨fun x => by cases x <;> simp [trans, p_nonneg, p_le],
            by rw [sum_place]; simp [trans]⟩
  observe _ := delivered

/-! ## The coupling bound and the pinned metric -/

/-- The bound: `c² (p - q)` at the depot, `c (p - q)` on the bridge, `0` on the
other diagonal pairs, `1` elsewhere. -/
def bound (c p q : 𝕜) : Place → Place → 𝕜
  | .depot, .depot => c * (c * (p - q))
  | .bridge, .bridge => c * (p - q)
  | .hill, .hill => 0
  | .garden, .garden => 0
  | .slipped, .slipped => 0
  | _, _ => 1

section Bound

variable {c p q : 𝕜}

theorem bound_le_one (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (q_nonneg : 0 ≤ q) (le : q ≤ p)
    (p_le : p ≤ 1) (s t : Place) : bound c p q s t ≤ 1 := by
  have gap : p - q ≤ 1 := by linarith
  have gap_nonneg : 0 ≤ p - q := sub_nonneg.mpr le
  have first : c * (p - q) ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr c_le) gap_nonneg]
  have second : c * (c * (p - q)) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr c_le) (mul_nonneg c_nonneg gap_nonneg)]
  cases s <;> cases t <;> simp only [bound] <;>
    first | exact le_rfl | exact zero_le_one | exact first | exact second

theorem bound_nonneg (c_nonneg : 0 ≤ c) (le : q ≤ p) (s t : Place) : 0 ≤ bound c p q s t := by
  have gap_nonneg : 0 ≤ p - q := sub_nonneg.mpr le
  cases s <;> cases t <;> simp only [bound] <;>
    first | exact le_rfl | exact zero_le_one | exact mul_nonneg c_nonneg gap_nonneg |
      exact mul_nonneg c_nonneg (mul_nonneg c_nonneg gap_nonneg)

/-- The coupling on the bridge: deliver together, slip together, and move the
excess slip mass of the world onto delivery in the model. -/
def slipCoupling (q_nonneg : 0 ≤ q) (le : q ≤ p) (p_le : p ≤ 1) (a b : Route) :
    Coupling (trans p a .bridge) (trans q b .bridge) where
  weight x y := if x = .garden ∧ y = .garden then 1 - p
    else if x = .slipped ∧ y = .slipped then q
    else if x = .slipped ∧ y = .garden then p - q else 0
  nonneg x y := by
    cases x <;> cases y <;> simp <;> linarith
  sum_right x := by
    cases x <;> simp [sum_place, trans]
  sum_left y := by
    cases y <;> simp [sum_place, trans]

theorem cost_slipCoupling (q_nonneg : 0 ≤ q) (le : q ≤ p) (p_le : p ≤ 1) (a b : Route) :
    (slipCoupling q_nonneg le p_le a b).cost (bound c p q) = p - q := by
  unfold Coupling.cost slipCoupling
  simp [sum_place, bound]

/-- **The coupling bound** between the world with slip probability `p` and the
model with slip probability `q ≤ p`. -/
theorem couplingBound (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (q_nonneg : 0 ≤ q) (le : q ≤ p)
    (p_le : p ≤ 1) :
    CouplingBound (chain p (q_nonneg.trans le) p_le) (chain q q_nonneg (le.trans p_le)) c
      (bound c p q) where
  nonneg := bound_nonneg c_nonneg le
  observe_le _ s t := by
    have gap_nonneg : 0 ≤ p - q := sub_nonneg.mpr le
    cases s <;> cases t <;> simp [chain, delivered, bound] <;>
      first | exact mul_nonneg c_nonneg gap_nonneg |
        exact mul_nonneg c_nonneg (mul_nonneg c_nonneg gap_nonneg)
  step_le a s t := by
    have generic : ∀ (a : Route) (s t : Place), bound c p q s t = 1 →
        ∃ ω : Coupling ((chain p (q_nonneg.trans le) p_le).trans a s)
          ((chain q q_nonneg (le.trans p_le)).trans a t), c * ω.cost (bound c p q) ≤
            bound c p q s t := fun a s t one => by
      let ω := Coupling.independent ((chain p (q_nonneg.trans le) p_le).isDistribution a s)
        ((chain q q_nonneg (le.trans p_le)).isDistribution a t)
      refine ⟨ω, ?_⟩
      have cost_le : ω.cost (bound c p q) ≤ 1 :=
        ω.cost_le_of_le ((chain p (q_nonneg.trans le) p_le).isDistribution a s)
          (bound_le_one c_nonneg c_le q_nonneg le p_le)
      rw [one]
      nlinarith [ω.cost_nonneg (bound_nonneg c_nonneg le)]
    have diagonal : ∀ (x : Place) (a : Route),
        (chain p (q_nonneg.trans le) p_le).trans a x = dirac x →
          (chain q q_nonneg (le.trans p_le)).trans a x = dirac x →
            bound c p q x x = 0 →
              ∃ ω : Coupling ((chain p (q_nonneg.trans le) p_le).trans a x)
                ((chain q q_nonneg (le.trans p_le)).trans a x), c * ω.cost (bound c p q) ≤ 0 := by
      intro x a first second zero
      let ω := Coupling.independent ((chain p (q_nonneg.trans le) p_le).isDistribution a x)
        ((chain q q_nonneg (le.trans p_le)).isDistribution a x)
      have cost : ω.cost (bound c p q) = bound c p q x x :=
        Coupling.cost_of_eq_dirac ω first second _
      refine ⟨ω, ?_⟩
      rw [cost, zero, mul_zero]
    cases s <;> cases t <;> first
      | exact generic a _ _ rfl
      | skip
    · -- depot, depot
      cases a
      · let ω := Coupling.independent
          ((chain p (q_nonneg.trans le) p_le).isDistribution .viaBridge .depot)
          ((chain q q_nonneg (le.trans p_le)).isDistribution .viaBridge .depot)
        have cost : ω.cost (bound c p q) = bound c p q .bridge .bridge :=
          Coupling.cost_of_eq_dirac ω rfl rfl _
        refine ⟨ω, ?_⟩
        rw [cost]
        exact le_rfl
      · let ω := Coupling.independent
          ((chain p (q_nonneg.trans le) p_le).isDistribution .viaHill .depot)
          ((chain q q_nonneg (le.trans p_le)).isDistribution .viaHill .depot)
        have cost : ω.cost (bound c p q) = bound c p q .hill .hill :=
          Coupling.cost_of_eq_dirac ω rfl rfl _
        refine ⟨ω, ?_⟩
        rw [cost]
        simp only [bound, mul_zero]
        exact mul_nonneg c_nonneg (mul_nonneg c_nonneg (sub_nonneg.mpr le))
    · -- bridge, bridge
      have key : c * (slipCoupling q_nonneg le p_le a a).cost (bound c p q) ≤
          bound c p q .bridge .bridge := by
        rw [cost_slipCoupling q_nonneg le p_le]
        exact le_rfl
      exact ⟨slipCoupling q_nonneg le p_le a a, key⟩
    · -- hill, hill
      let ω := Coupling.independent
        ((chain p (q_nonneg.trans le) p_le).isDistribution a .hill)
        ((chain q q_nonneg (le.trans p_le)).isDistribution a .hill)
      have cost : ω.cost (bound c p q) = bound c p q .garden .garden :=
        Coupling.cost_of_eq_dirac ω (by cases a <;> rfl) (by cases a <;> rfl) _
      refine ⟨ω, ?_⟩
      rw [cost]
      simp [bound]
    · -- garden, garden
      exact diagonal .garden a (by cases a <;> rfl) (by cases a <;> rfl) rfl
    · -- slipped, slipped
      exact diagonal .slipped a (by cases a <;> rfl) (by cases a <;> rfl) rfl

end Bound

/-- The functional expression "deliver over the bridge": two discounted steps
along the bridge route, then the delivery observable. -/
def bridgeDelivery : FunctionalExpression 𝕜 Route Unit :=
  .next .viaBridge (.next .viaBridge (.observe ()))

theorem eval_bridgeDelivery (c p : 𝕜) (p_nonneg : 0 ≤ p) (p_le : p ≤ 1) :
    bridgeDelivery.eval (chain p p_nonneg p_le) c .depot = c * (c * (1 - p)) := by
  simp only [bridgeDelivery, FunctionalExpression.eval, chain]
  change c * expect (dirac Place.bridge) _ = _
  rw [expect_dirac]
  simp [expect, trans, delivered]

/-- **The metric at the depot is exactly `c² (p - q)`.** -/
theorem metric_depot {c p q : ℝ} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (q_nonneg : 0 ≤ q) (le : q ≤ p)
    (p_le : p ≤ 1) :
    bisimulationMetric (chain p (q_nonneg.trans le) p_le) (chain q q_nonneg (le.trans p_le)) c
      .depot .depot = c * (c * (p - q)) := by
  apply le_antisymm
  · exact bisimulationMetric_le (couplingBound c_nonneg c_le q_nonneg le p_le) c_nonneg _ _
  · have lower := abs_eval_sub_le_bisimulationMetric (P := chain p (q_nonneg.trans le) p_le)
      (Q := chain q q_nonneg (le.trans p_le)) c_nonneg c_le bridgeDelivery .depot .depot
    rw [eval_bridgeDelivery, eval_bridgeDelivery] at lower
    have value : |c * (c * (1 - p)) - c * (c * (1 - q))| = c * (c * (p - q)) := by
      rw [show c * (c * (1 - p)) - c * (c * (1 - q)) = -(c * (c * (p - q))) by ring, abs_neg,
        abs_of_nonneg (mul_nonneg c_nonneg (mul_nonneg c_nonneg (sub_nonneg.mpr le)))]
    rw [value] at lower
    exact lower

/-- At discount `1/2`, a world slipping with probability `3/10` and a model
slipping with probability `1/100` are `29/400` apart at the depot. -/
theorem metric_depot_rare :
    bisimulationMetric (chain (3 / 10 : ℝ) (by norm_num) (by norm_num))
      (chain (1 / 100 : ℝ) (by norm_num) (by norm_num)) (1 / 2) .depot .depot = 29 / 400 := by
  rw [metric_depot (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- At discount `1/2`, the world and a model that never slips are `3/40` apart
at the depot. -/
theorem metric_depot_never :
    bisimulationMetric (chain (3 / 10 : ℝ) (by norm_num) (by norm_num))
      (chain (0 : ℝ) le_rfl zero_le_one) (1 / 2) .depot .depot = 3 / 40 := by
  rw [metric_depot (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)]
  norm_num

/-! ## Girard–Pappas on the supports misleads both ways -/

section Supports

theorem supportStep_iff {p q : 𝕜} {p_nonneg : 0 ≤ p} {p_le : p ≤ 1} {q_nonneg : 0 ≤ q}
    {q_le : q ≤ 1} (p_pos : 0 < p) (p_lt : p < 1) (q_pos : 0 < q) (q_lt : q < 1) (a : Route)
    (s x : Place) :
    (chain p p_nonneg p_le).supportStep a s x ↔ (chain q q_nonneg q_le).supportStep a s x := by
  have p_ne : (1 : 𝕜) - p ≠ 0 := sub_ne_zero.mpr p_lt.ne'
  have q_ne : (1 : 𝕜) - q ≠ 0 := sub_ne_zero.mpr q_lt.ne'
  cases s <;> cases a <;> cases x <;>
    simp [LabelledMarkovChain.supportStep, chain, trans, dirac, p_ne, q_ne, p_pos.ne', q_pos.ne']

/-- **Rare slips: the supports are bisimilar at precision `0`.** -/
theorem supports_exact {p q : 𝕜} {p_nonneg : 0 ≤ p} {p_le : p ≤ 1} {q_nonneg : 0 ≤ q}
    {q_le : q ≤ 1} (p_pos : 0 < p) (p_lt : p < 1) (q_pos : 0 < q) (q_lt : q < 1) (a : Route) :
    IsApproxBisimulation observationGap ((chain p p_nonneg p_le).supportStep a)
      ((chain q q_nonneg q_le).supportStep a) (chain p p_nonneg p_le).observation
      (chain q q_nonneg q_le).observation 0 Eq := by
  refine ⟨⟨fun x y same => ?_, fun x y same x' moved => ?_⟩,
    ⟨fun y x same => ?_, fun y x same y' moved => ?_⟩⟩
  · subst same
    exact (observationGap_self _).le
  · subst same
    exact ⟨x', (supportStep_iff p_pos p_lt q_pos q_lt a x x').mp moved, rfl⟩
  · change x = y at same
    subst same
    exact (observationGap_self _).le
  · change x = y at same
    subst same
    exact ⟨y', (supportStep_iff p_pos p_lt q_pos q_lt a x y').mpr moved, rfl⟩

/-- **Never slipping: no approximate bisimulation of the supports below `1`**,
whatever the world's slip probability `p > 0`. -/
theorem supports_far {p : 𝕜} {p_nonneg : 0 ≤ p} {p_le : p ≤ 1} (p_pos : 0 < p) {ε : 𝕜}
    (small : ε < 1) :
    ¬ ApproxBisimilar observationGap ((chain p p_nonneg p_le).supportStep .viaBridge)
      ((chain (0 : 𝕜) le_rfl zero_le_one).supportStep .viaBridge)
      (chain p p_nonneg p_le).observation (chain (0 : 𝕜) le_rfl zero_le_one).observation ε
      .depot .depot := by
  rintro ⟨R, bisimulation, related⟩
  obtain ⟨y, movedY, relatedBridge⟩ := bisimulation.1.forth related .bridge
    (by simp [LabelledMarkovChain.supportStep, chain, trans, dirac])
  have bridge : y = .bridge := by
    cases y <;> simp_all [LabelledMarkovChain.supportStep, chain, trans, dirac]
  subst bridge
  obtain ⟨z, movedZ, relatedDitch⟩ := bisimulation.1.forth relatedBridge .slipped
    (by simp [LabelledMarkovChain.supportStep, chain, trans, p_pos.ne'])
  have garden : z = .garden := by
    cases z <;> simp_all [LabelledMarkovChain.supportStep, chain, trans]
  subst garden
  have close := bisimulation.1.close relatedDitch
  have gap := (observationGap_le_iff.mp close).2 ()
  simp [LabelledMarkovChain.observation, chain, delivered] at gap
  linarith

end Supports

/-! ## Correspondence defects on the route graph -/

/-- The edges of the route graph. -/
inductive RouteEdge : Place → Place → Type
  | depotBridge : RouteEdge .depot .bridge
  | bridgeGarden : RouteEdge .bridge .garden
  | bridgeSlipped : RouteEdge .bridge .slipped
  | depotHill : RouteEdge .depot .hill
  | hillGarden : RouteEdge .hill .garden

instance : Quiver Place :=
  ⟨RouteEdge⟩

/-- The step model's success probability of an edge, with slip probability
`q`. -/
def edgeProbability (q : ℝ) : {a b : Place} → RouteEdge a b → ℝ
  | _, _, .depotBridge => 1
  | _, _, .bridgeGarden => 1 - q
  | _, _, .bridgeSlipped => q
  | _, _, .depotHill => 1
  | _, _, .hillGarden => 1

/-- The probability of a path under the step model. -/
def pathProbability (q : ℝ) : {a b : Place} → Quiver.Path a b → ℝ
  | _, _, .nil => 1
  | _, _, .cons path e => edgeProbability q e * pathProbability q path

theorem pathProbability_comp (q : ℝ) {a b : Place} (first : Quiver.Path a b) :
    ∀ {c : Place} (second : Quiver.Path b c),
      pathProbability q (first.comp second) = pathProbability q second * pathProbability q first
  | _, .nil => by simp [pathProbability]
  | _, .cons second e => by
      simp only [Quiver.Path.comp, pathProbability]
      rw [pathProbability_comp q first second]
      ring

theorem pathProbability_nil (q : ℝ) (x : Place) :
    pathProbability q (Quiver.Path.nil : Quiver.Path x x) = 1 := by
  simp [pathProbability]

/-- **The path-probability map of a step model**, into the one-object category
of probabilities under multiplication. -/
noncomputable def pathCorrespondence (q : ℝ) : PathCorrespondence (Paths Place) (SingleObj ℝ) where
  obj _ := SingleObj.star ℝ
  map path := pathProbability q path
  geometry _ _ := ValueGeometry.ofPseudoMetric ℝ

/-- **It is a functor: defect `0` at every slip probability.** -/
theorem pathCorrespondence_exact (q : ℝ) : (pathCorrespondence q).Exact := by
  refine ⟨fun x => ?_, fun first second => ?_⟩
  · rw [SingleObj.id_as_one]
    exact pathProbability_nil q x
  · rw [SingleObj.comp_as_mul]
    exact pathProbability_comp q first second

/-- The whole bridge route, depot to garden. -/
def bridgeRoute : Quiver.Path Place.depot Place.garden :=
  (Quiver.Path.nil.cons RouteEdge.depotBridge).cons RouteEdge.bridgeGarden

/-- Whether a path is the whole bridge route. -/
def isBridgeRoute : {a b : Place} → Quiver.Path a b → Bool
  | _, _, .cons (.cons .nil RouteEdge.depotBridge) RouteEdge.bridgeGarden => true
  | _, _, _ => false

/-- **A model with a stale cache**: the whole bridge route is estimated at
`9/10`, every other path by the step model. -/
noncomputable def cachedCorrespondence (q : ℝ) :
    PathCorrespondence (Paths Place) (SingleObj ℝ) where
  obj _ := SingleObj.star ℝ
  map path := if isBridgeRoute path then (9 / 10 : ℝ) else pathProbability q path
  geometry _ _ := ValueGeometry.ofPseudoMetric ℝ

/-- A place as an object of the free category of the route graph. -/
abbrev node (x : Place) : Paths Place :=
  x

/-- An arrow of the one-object category of probabilities, read as a number. -/
def probability {x y : SingleObj ℝ} (f : x ⟶ y) : ℝ :=
  f

/-- The first leg of the bridge route. -/
def toBridge : node .depot ⟶ node .bridge :=
  (Quiver.Path.nil.cons RouteEdge.depotBridge : Quiver.Path Place.depot Place.bridge)

/-- The second leg of the bridge route. -/
def crossBridge : node .bridge ⟶ node .garden :=
  (Quiver.Path.nil.cons RouteEdge.bridgeGarden : Quiver.Path Place.bridge Place.garden)

/-- The first leg of the hill route. -/
def toHill : node .depot ⟶ node .hill :=
  (Quiver.Path.nil.cons RouteEdge.depotHill : Quiver.Path Place.depot Place.hill)

/-- The second leg of the hill route. -/
def climbDown : node .hill ⟶ node .garden :=
  (Quiver.Path.nil.cons RouteEdge.hillGarden : Quiver.Path Place.hill Place.garden)

theorem isBridgeRoute_bridgeRoute : isBridgeRoute bridgeRoute = true :=
  rfl

theorem isBridgeRoute_crossBridge :
    isBridgeRoute (Quiver.Path.nil.cons RouteEdge.bridgeGarden) = false :=
  rfl

theorem isBridgeRoute_toBridge :
    isBridgeRoute (Quiver.Path.nil.cons RouteEdge.depotBridge) = false :=
  rfl

theorem isBridgeRoute_hillRoute :
    isBridgeRoute ((Quiver.Path.nil.cons RouteEdge.depotHill).cons RouteEdge.hillGarden) = false :=
  rfl

theorem isBridgeRoute_toHill : isBridgeRoute (Quiver.Path.nil.cons RouteEdge.depotHill) = false :=
  rfl

theorem isBridgeRoute_climbDown :
    isBridgeRoute (Quiver.Path.nil.cons RouteEdge.hillGarden) = false :=
  rfl

theorem cached_map_bridgeRoute (q : ℝ) :
    probability ((cachedCorrespondence q).map (toBridge ≫ crossBridge)) = 9 / 10 := by
  change (if isBridgeRoute bridgeRoute then (9 / 10 : ℝ) else pathProbability q bridgeRoute) =
    9 / 10
  rw [if_pos isBridgeRoute_bridgeRoute]

theorem cached_map_legs (q : ℝ) :
    probability ((cachedCorrespondence q).map toBridge ≫ (cachedCorrespondence q).map crossBridge) =
      1 - q := by
  unfold probability
  rw [SingleObj.comp_as_mul]
  change (if isBridgeRoute (Quiver.Path.nil.cons RouteEdge.bridgeGarden) then (9 / 10 : ℝ)
      else pathProbability q (Quiver.Path.nil.cons RouteEdge.bridgeGarden)) *
    (if isBridgeRoute (Quiver.Path.nil.cons RouteEdge.depotBridge) then (9 / 10 : ℝ)
      else pathProbability q (Quiver.Path.nil.cons RouteEdge.depotBridge)) = 1 - q
  rw [isBridgeRoute_crossBridge, isBridgeRoute_toBridge]
  simp [pathProbability, edgeProbability]

/-- **The cached model's defect on the bridge route is `|9/10 - (1 - q)|`.** -/
theorem cachedCorrespondence_defect (q : ℝ) :
    (cachedCorrespondence q).compositionDefect toBridge crossBridge = |9 / 10 - (1 - q)| := by
  change dist (probability ((cachedCorrespondence q).map (toBridge ≫ crossBridge)))
    (probability ((cachedCorrespondence q).map toBridge ≫
      (cachedCorrespondence q).map crossBridge)) = _
  rw [cached_map_bridgeRoute, cached_map_legs, Real.dist_eq]

theorem cachedCorrespondence_hill_defect (q : ℝ) :
    (cachedCorrespondence q).compositionDefect toHill climbDown = 0 := by
  have whole : probability ((cachedCorrespondence q).map (toHill ≫ climbDown)) = 1 := by
    change (if isBridgeRoute ((Quiver.Path.nil.cons RouteEdge.depotHill).cons RouteEdge.hillGarden)
        then (9 / 10 : ℝ) else pathProbability q
          ((Quiver.Path.nil.cons RouteEdge.depotHill).cons RouteEdge.hillGarden)) = 1
    rw [isBridgeRoute_hillRoute]
    simp [pathProbability, edgeProbability]
  have legs : probability ((cachedCorrespondence q).map toHill ≫
      (cachedCorrespondence q).map climbDown) = 1 := by
    unfold probability
    rw [SingleObj.comp_as_mul]
    change (if isBridgeRoute (Quiver.Path.nil.cons RouteEdge.hillGarden) then (9 / 10 : ℝ)
        else pathProbability q (Quiver.Path.nil.cons RouteEdge.hillGarden)) *
      (if isBridgeRoute (Quiver.Path.nil.cons RouteEdge.depotHill) then (9 / 10 : ℝ)
        else pathProbability q (Quiver.Path.nil.cons RouteEdge.depotHill)) = 1
    rw [isBridgeRoute_climbDown, isBridgeRoute_toHill]
    simp [pathProbability, edgeProbability]
  change dist (probability ((cachedCorrespondence q).map (toHill ≫ climbDown)))
    (probability ((cachedCorrespondence q).map toHill ≫ (cachedCorrespondence q).map climbDown)) = 0
  rw [whole, legs, dist_self]

/-- **Even with the world's own step model** (`q = 3/10`), the cached model has
defect `1/5`, while its step model is at metric distance `0` from the world. -/
theorem cache_defect_step_exact :
    (cachedCorrespondence (3 / 10)).compositionDefect toBridge crossBridge = 1 / 5 ∧
      bisimulationMetric (chain (3 / 10 : ℝ) (by norm_num) (by norm_num))
        (chain (3 / 10 : ℝ) (by norm_num) (by norm_num)) (1 / 2) .depot .depot = 0 := by
  refine ⟨?_, ?_⟩
  · rw [cachedCorrespondence_defect]
    norm_num [abs_of_pos]
  · rw [metric_depot (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)]
    norm_num

/-- **A coherent model with rare slips** (`q = 1/100`) has defect `0` and
metric distance `29/400` from the world. -/
theorem coherent_defect_zero_metric_positive :
    (pathCorrespondence (1 / 100)).Exact ∧
      bisimulationMetric (chain (3 / 10 : ℝ) (by norm_num) (by norm_num))
        (chain (1 / 100 : ℝ) (by norm_num) (by norm_num)) (1 / 2) .depot .depot = 29 / 400 :=
  ⟨pathCorrespondence_exact _, metric_depot_rare⟩

/-! ## Today's goals are not tomorrow's -/

/-- The two sampled pairs: the bridge route and the hill route. -/
def routePair : Bool → ComposablePair (Paths Place)
  | true => ⟨_, _, _, toBridge, crossBridge⟩
  | false => ⟨_, _, _, toHill, climbDown⟩

/-- Today's goal: the hill route. -/
def today : FiniteWeighting ℝ Bool where
  support := {false}
  weight b := if b then 0 else 1
  nonneg b _ := by cases b <;> norm_num
  sum_eq_one := by simp

/-- Tomorrow's goal: the bridge route. -/
def tomorrow : FiniteWeighting ℝ Bool where
  support := {true}
  weight b := if b then 1 else 0
  nonneg b _ := by cases b <;> norm_num
  sum_eq_one := by simp

theorem today_average_zero : averageDefect (cachedCorrespondence (3 / 10)) today routePair = 0 := by
  simp only [averageDefect, FiniteWeighting.expectation, today, Finset.sum_singleton]
  change (if false = true then (0 : ℝ) else 1) *
    (cachedCorrespondence (3 / 10)).compositionDefect toHill climbDown = 0
  rw [cachedCorrespondence_hill_defect, mul_zero]

theorem tomorrow_average :
    averageDefect (cachedCorrespondence (3 / 10)) tomorrow routePair = 1 / 5 := by
  simp only [averageDefect, FiniteWeighting.expectation, tomorrow, Finset.sum_singleton]
  change (if true = true then (1 : ℝ) else 0) *
    (cachedCorrespondence (3 / 10)).compositionDefect toBridge crossBridge = 1 / 5
  rw [cachedCorrespondence_defect]
  norm_num [abs_of_pos]

/-- **Today's weighting does not charge tomorrow's goal**, so nothing transfers
(`FiniteWeighting.exists_no_transfer`). -/
theorem tomorrow_outside_today : true ∉ today.support ∧ true ∈ tomorrow.support := by
  simp [today, tomorrow]

/-- **The off-goal conclusion fails**: the cache says the bridge route delivers
with probability at least `17/20`; composing the step model gives `7/10`, and
so does the world (the undiscounted value of "deliver over the bridge"). -/
theorem cached_conclusion_fails :
    (17 / 20 : ℝ) ≤ probability ((cachedCorrespondence (3 / 10)).map (toBridge ≫ crossBridge)) ∧
      probability ((cachedCorrespondence (3 / 10)).map toBridge ≫
          (cachedCorrespondence (3 / 10)).map crossBridge) < 17 / 20 ∧
      bridgeDelivery.eval (chain (3 / 10 : ℝ) (by norm_num) (by norm_num)) 1 .depot < 17 / 20 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cached_map_bridgeRoute]
    norm_num
  · rw [cached_map_legs]
    norm_num
  · rw [eval_bridgeDelivery]
    norm_num

end Mettapedia.Cybernetics.ApproximateAdequacy.Delivery
