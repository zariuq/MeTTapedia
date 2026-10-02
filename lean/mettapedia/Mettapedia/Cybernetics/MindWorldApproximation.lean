import Mettapedia.Cybernetics.MindWorldBisimulation
import Mathlib.CategoryTheory.Action
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Approximate mind–world correspondences, approximate bisimulation, and goals

The exact case is `Mettapedia.Cybernetics.MindWorldBisimulation`: exact
correspondences over a view are functional simulations, or bisimulations
when transitions are also reflected.  This module treats approximation, and
keeps apart three quantities that are easy to conflate.

**1. Approximate bisimulation measures observations.**  Following A. Girard
and G. J. Pappas (*Approximation metrics for discrete and continuous
systems*, IEEE Trans. Automatic Control 52(5), 2007), an `ε`-approximate
simulation relates states whose observations are within `ε` and matches
every transition exactly (`IsApproxSimulation`); an `ε`-approximate
bisimulation is one in both directions (`IsApproxBisimulation`).
* Forgetting the observations leaves a bisimulation
  (`IsApproxBisimulation.isBisimulation`).  With the view as observation,
  the graph of the view is an approximate bisimulation exactly when the
  view is a bounded morphism (`graph_isApproxBisimulation_iff`), and in a
  metric space every `0`-approximate simulation lies inside that graph
  (`IsApproxSimulation.eq_of_zero`): the exact case of the previous module.
* For deterministic systems, two states are `ε`-approximately bisimilar
  exactly when their observation trajectories stay within `ε` forever
  (`approxBisimilar_update_iff`).  The behavioural pseudometrics of
  J. Desharnais, V. Gupta, R. Jagadeesan and P. Panangaden (*Metrics for
  labelled Markov processes*, TCS 318, 2004) generalise this to probabilistic
  transitions; they are not formalised here.
* **From update squares.**  An update square with error `δ` over an abstract
  update of modulus `ω` gives an `ε`-approximate bisimulation whenever
  `δ + ω ε ≤ ε` (`isApproxBisimulation_of_contraction`); instance:
  `Halving.approxBisimilar`, within `2`.
* The distance is any function into an ordered additive monoid, as for the
  approximate squares of the scope algebra; the structural results use no
  choice, and only their instances over `ℝ` inherit it from `Real`.  Control: with a
  non-contracting abstract update, an error of `1` per step admits no
  approximate bisimulation at any precision (`Drift.not_approxBisimilar`),
  since the error accumulates as in `Succ.error_iterate`.

**2. Correspondence defects measure non-functoriality.**  The defects of
`MindWorldApproximateFunctor` compare `F (P ≫ Q)` with `F P ≫ F Q` in the
geometry of mind arrows, for a correspondence whose paths always end exactly
at the image of the world endpoint.  They are not a distance between world
and mind states, and the two notions are independent:
* a path correspondence into the execution category of the mind's own
  transitions forces the image of each world transition to be reachable in
  the mind (`obj_reachable`), so a mind that drifts has no correspondence at
  all with the view as object map, whatever the budget
  (`Drift.no_correspondence_over_view`);
* a zero-defect correspondence, even a functional bisimulation of the
  transition structure, can have unboundedly different observations
  (`Collapse.zeroDefect`, `Collapse.not_approxBisimilar`).

**3. Update squares give bounded defects on process arrows.**  Where the
existing definitions do fit: let world processes be the arrows of the action
category of a monoid acting on world states, and mind arrows abstract
updates of mind states (`UpdateObject`), measured at the source state
(`evaluationGeometry`).  A model assigning an abstract update to each world
process is a path correspondence over the view (`updateCorrespondence`).
* Its identity defect is at most the error of the identity square, and its
  composition defect is at most the composite square's error plus the
  error of composing the two squares (`identityDefect_le`,
  `compositionDefect_le`), which is W11's `ApproxSquare.comp`; so update
  squares with errors `ε` form a bounded-defect correspondence
  (`boundedOfSquares`).
* Exact squares over a quotient view give an exact correspondence, a functor
  (`quotientCorrespondence_exact`).
* Control: a model exact on every generator and wrong on one composite has
  a positive composition defect and is not exact
  (`Fold.compositionDefect_eq`, `Fold.not_exact`); the bound is attained.

**4. What goal weighting adds.**  The principle weights defects by a
distribution over paths that favours goal-directed ones (Goertzel et al.,
§11.3).  An average weighted by goal relevance vanishes for every exact
correspondence (`goalWeightedDefect_eq_zero_of_exact`), and it can vanish
for a correspondence that is not exact (`Fold.goalWeighted_not_exact`).
Bisimulation and approximate bisimulation are uniform over all states and
transitions; goal weighting is exactly the licence to be wrong where no goal
depends on it.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.MindWorldApproximation

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Scope
open Mettapedia.GSLT.Dynamics.TypedValueGeometry
open Mettapedia.Cybernetics.MindWorldApproximateFunctor
open Mettapedia.Cybernetics.GSLTMindWorldCorrespondence
open Mettapedia.Cybernetics.MindWorldBisimulation
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

/-! ## Approximate simulation and bisimulation -/

section Approximate

variable {X Y O D : Type*} [LE D]

/-- **An `ε`-approximate simulation relation** (Girard and Pappas): related
states have observations within `ε` under `distance`, and every transition
of the first system is matched by a transition of the second that stays
related. -/
structure IsApproxSimulation (distance : O → O → D) (step : X → X → Prop)
    (step' : Y → Y → Prop) (obs : X → O) (obs' : Y → O) (ε : D) (R : X → Y → Prop) : Prop where
  /-- Related states have close observations. -/
  close : ∀ ⦃x y⦄, R x y → distance (obs x) (obs' y) ≤ ε
  /-- Transitions are matched exactly. -/
  forth : ∀ ⦃x y⦄, R x y → ∀ x', step x x' → ∃ y', step' y y' ∧ R x' y'

/-- **An `ε`-approximate bisimulation relation**: a simulation in both
directions. -/
def IsApproxBisimulation (distance : O → O → D) (step : X → X → Prop) (step' : Y → Y → Prop)
    (obs : X → O) (obs' : Y → O) (ε : D) (R : X → Y → Prop) : Prop :=
  IsApproxSimulation distance step step' obs obs' ε R ∧
    IsApproxSimulation distance step' step obs' obs ε (flip R)

/-- Two states are `ε`-approximately bisimilar. -/
def ApproxBisimilar (distance : O → O → D) (step : X → X → Prop) (step' : Y → Y → Prop)
    (obs : X → O) (obs' : Y → O) (ε : D) (x : X) (y : Y) : Prop :=
  ∃ R, IsApproxBisimulation distance step step' obs obs' ε R ∧ R x y

variable {distance : O → O → D} {step : X → X → Prop} {step' : Y → Y → Prop} {obs : X → O}
  {obs' : Y → O} {ε : D} {R : X → Y → Prop}

/-- **Forgetting the observations leaves a bisimulation.** -/
theorem IsApproxBisimulation.isBisimulation
    (approx : IsApproxBisimulation distance step step' obs obs' ε R) :
    IsBisimulation step step' R :=
  fun _ _ related => ⟨fun x' moved => approx.1.forth related x' moved,
    fun y' moved => approx.2.forth related y' moved⟩

end Approximate

section Graph

variable {X Y D : Type*} [LE D] {distance : Y → Y → D} {step : X → X → Prop}
  {step' : Y → Y → Prop} {view : X → Y}

/-- **With the view as observation, the graph of the view is an approximate
bisimulation exactly when the view is a bounded morphism**, at every
precision that bounds the distance of a state to itself. -/
theorem graph_isApproxBisimulation_iff {ε : D} (selfClose : ∀ y, distance y y ≤ ε) :
    IsApproxBisimulation distance step step' view id ε (fun x y => view x = y) ↔
      IsBoundedMorphism step step' view := by
  constructor
  · rintro ⟨forward, backward⟩
    refine ⟨fun x x' moved => ?_, fun x y' moved => ?_⟩
    · obtain ⟨_, moved', rfl⟩ := forward.forth rfl x' moved
      exact moved'
    · obtain ⟨x', moved', image⟩ := backward.forth (x := view x) (y := x) rfl y' moved
      exact ⟨x', moved', image⟩
  · intro bounded
    refine ⟨⟨fun x _ image => ?_, fun x _ image x' moved => ?_⟩,
      ⟨fun _ x image => ?_, fun _ x image y' moved => ?_⟩⟩
    · subst image
      exact selfClose _
    · subst image
      exact ⟨view x', bounded.map moved, rfl⟩
    · change view x = _ at image
      subst image
      exact selfClose _
    · change view x = _ at image
      subst image
      obtain ⟨x', moved', image'⟩ := bounded.lift moved
      exact ⟨x', moved', image'⟩

/-- **In a metric space a `0`-approximate simulation lies inside the graph of
the view.** -/
theorem IsApproxSimulation.eq_of_zero {Y : Type*} [MetricSpace Y] {step' : Y → Y → Prop}
    {view : X → Y} {R : X → Y → Prop}
    (simulation : IsApproxSimulation dist step step' view id (0 : ℝ) R)
    {x : X} {y : Y} (related : R x y) : view x = y :=
  dist_le_zero.mp (simulation.close related)

end Graph

/-! ### Deterministic systems: closeness of trajectories -/

section Deterministic

variable {X Y O D : Type*} [LE D] {distance : O → O → D} {f : X → X} {f' : Y → Y}
  {obs : X → O} {obs' : Y → O} {ε : D}

/-- **For deterministic systems and a symmetric distance, approximate
bisimilarity is closeness of the observation trajectories.** -/
theorem approxBisimilar_update_iff (symmetric : ∀ a b, distance a b = distance b a)
    {x : X} {y : Y} :
    ApproxBisimilar distance (fun a b => f a = b) (fun a b => f' a = b) obs obs' ε x y ↔
      ∀ n : ℕ, distance (obs (f^[n] x)) (obs' (f'^[n] y)) ≤ ε := by
  constructor
  · rintro ⟨R, ⟨forward, _⟩, related⟩
    have along : ∀ n : ℕ, R (f^[n] x) (f'^[n] y) := by
      intro n
      induction n with
      | zero => exact related
      | succ n ih =>
          obtain ⟨_, moved, related'⟩ := forward.forth ih _ rfl
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', moved]
          exact related'
    exact fun n => forward.close (along n)
  · intro close
    refine ⟨fun a b => ∀ n : ℕ, distance (obs (f^[n] a)) (obs' (f'^[n] b)) ≤ ε,
      ⟨⟨fun _ _ related => related 0, fun a b related _ moved => ?_⟩,
        ⟨fun _ _ related => ?_, fun b a related _ moved => ?_⟩⟩, close⟩
    · subst moved
      exact ⟨f' b, rfl, fun n => by
        simpa only [Function.iterate_succ_apply] using related (n + 1)⟩
    · rw [symmetric]
      exact related 0
    · subst moved
      exact ⟨f a, rfl, fun n => by
        simpa only [Function.iterate_succ_apply] using related (n + 1)⟩

end Deterministic

/-! ### From update squares, under contraction -/

section Contraction

variable {X Y D : Type*} [AddCommMonoid D] [PartialOrder D] [IsOrderedAddMonoid D]
  {distance : Y → Y → D} {view : X → Y} {f : X → X} {f' : Y → Y}

/-- **An update square with error `δ`, over an abstract update of modulus `ω`,
gives an `ε`-approximate bisimulation whenever `δ + ω ε ≤ ε`.** -/
theorem isApproxBisimulation_of_contraction (symmetric : ∀ a b, distance a b = distance b a)
    (triangle : ∀ a b c, distance a c ≤ distance a b + distance b c) {δ ε : D} {ω : D → D}
    (ω_mono : Monotone ω) (modulus : ∀ a b, distance (f' a) (f' b) ≤ ω (distance a b))
    (square : ApproxSquare distance view view f f' δ) (absorbs : δ + ω ε ≤ ε) :
    IsApproxBisimulation distance (fun a b => f a = b) (fun a b => f' a = b) view id ε
      (fun x y => distance (view x) y ≤ ε) := by
  have stays : ∀ x y, distance (view x) y ≤ ε → distance (view (f x)) (f' y) ≤ ε :=
    fun x y close =>
      calc distance (view (f x)) (f' y)
          ≤ distance (view (f x)) (f' (view x)) + distance (f' (view x)) (f' y) :=
            triangle _ _ _
        _ ≤ δ + ω (distance (view x) y) := add_le_add (square x) (modulus _ _)
        _ ≤ δ + ω ε := add_le_add le_rfl (ω_mono close)
        _ ≤ ε := absorbs
  refine ⟨⟨fun _ _ close => close, fun x y close _ moved => ?_⟩,
    ⟨fun y x (close : distance (view x) y ≤ ε) => ?_, fun y x close _ moved => ?_⟩⟩
  · subst moved
    exact ⟨f' y, rfl, stays x y close⟩
  · rw [symmetric]
    exact close
  · subst moved
    exact ⟨f x, rfl, stays x y close⟩

end Contraction

/-! ### Positive instance: halving plus one, abstracted by halving -/

namespace Halving

/-- The world update. -/
noncomputable def world (x : ℝ) : ℝ :=
  x / 2 + 1

/-- The abstract update drops the constant. -/
noncomputable def abstract (y : ℝ) : ℝ :=
  y / 2

theorem square : ApproxSquare dist id id world abstract 1 := by
  intro x
  change dist (x / 2 + 1) (x / 2) ≤ 1
  rw [Real.dist_eq, add_sub_cancel_left, abs_one]

theorem lipschitz (a b : ℝ) : dist (abstract a) (abstract b) ≤ 1 / 2 * dist a b := by
  unfold abstract
  rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_two]
  linarith

/-- **Every state is `2`-approximately bisimilar to its own abstraction.** -/
theorem approxBisimilar (x : ℝ) :
    ApproxBisimilar dist (fun a b => world a = b) (fun a b => abstract a = b) id id 2 x x :=
  ⟨_, isApproxBisimulation_of_contraction dist_comm dist_triangle (ω := fun t => 1 / 2 * t)
      (fun _ _ le => mul_le_mul_of_nonneg_left le (by norm_num)) lipschitz square
      (by norm_num),
    by rw [id, dist_self]; norm_num⟩

end Halving

/-! ## Path correspondences have exact endpoints -/

section Endpoints

variable {X Y : Type u}

/-- A route of a transition system witnesses reachability. -/
theorem reflTransGen_of_route {step : Y → Y → Prop} :
    ∀ {y y' : Y}, Route (fun a b => PLift (step a b)) y y' → Relation.ReflTransGen step y y'
  | _, _, .refl _ => Relation.ReflTransGen.refl
  | _, _, .cons moved rest => Relation.ReflTransGen.head moved.down (reflTransGen_of_route rest)

/-- **A path correspondence into the mind's execution category makes the image
of every world transition reachable in the mind.** -/
theorem obj_reachable {f : X → X} {step' : Y → Y → Prop}
    (correspondence : PathCorrespondence (ExecutionObject (updateSystem f))
      (ExecutionObject (transitionSystem step'))) (x : X) :
    Relation.ReflTransGen step' (correspondence.obj x) (correspondence.obj (f x)) :=
  reflTransGen_of_route (correspondence.map
    (show ExecutionPath (updateSystem f) x (f x) from .cons ⟨rfl⟩ (.refl (f x))))

end Endpoints

/-! ### Control: an abstraction that drifts by one per step -/

namespace Drift

/-- Observation of a count as a real number. -/
def observe (n : ℕ) : ℝ :=
  n

/-- The frozen transition relation relates only equal states. -/
theorem eq_of_reflTransGen_id {a b : ℕ}
    (reach : Relation.ReflTransGen (fun a b : ℕ => id a = b) a b) : a = b := by
  induction reach with
  | refl => rfl
  | tail _ moved ih => exact ih.trans moved

/-- The per-step square has error one: this is `Succ.square`. -/
theorem square : ApproxSquare natDist id id Succ.step id 1 :=
  Succ.square

/-- **No approximate bisimulation at any precision** relates the counter to
the frozen abstraction. -/
theorem not_approxBisimilar (ε : ℝ) :
    ¬ ApproxBisimilar dist (fun a b => Succ.step a = b) (fun a b => id a = b) observe observe ε
      0 0 := by
  intro bisimilar
  have close := (approxBisimilar_update_iff dist_comm).mp bisimilar
  obtain ⟨n, large⟩ := exists_nat_gt ε
  have bound := close n
  rw [Succ.step_iterate, Function.iterate_id, id, observe, observe, zero_add,
    Nat.cast_zero, Real.dist_eq, sub_zero, Nat.abs_cast] at bound
  linarith

/-- **No path correspondence of any defect has the view as object map**: the
frozen mind cannot reach the image of a world transition. -/
theorem no_correspondence_over_view :
    ¬ ∃ correspondence : PathCorrespondence (ExecutionObject (updateSystem Succ.step))
        (ExecutionObject (transitionSystem fun a b : ℕ => id a = b)),
      ∀ x : ℕ, correspondence.obj x = x := by
  rintro ⟨correspondence, objects⟩
  have reach := obj_reachable correspondence 0
  rw [objects, objects] at reach
  exact absurd (eq_of_reflTransGen_id reach) (by decide)

end Drift

/-! ### Control: zero defect with unbounded observational distance -/

namespace Collapse

/-- The collapse onto the one-state loop. -/
def view (_ : ℕ) : PUnit.{1} :=
  PUnit.unit

/-- It is a functional bisimulation of the transition structure. -/
theorem bounded :
    IsBoundedMorphism (fun a b : ℕ => Succ.step a = b) (fun a b : PUnit.{1} => id a = b) view :=
  isBoundedMorphism_update_iff.mpr fun _ => rfl

/-- **Its correspondence has zero defect.** -/
theorem zeroDefect :
    (exactCorrespondence (operationalOfPreserves bounded.map)).toPathCorrespondence.Exact :=
  exactCorrespondence_exact _

/-- The mind observes nothing. -/
def observeMind (_ : PUnit.{1}) : ℝ :=
  0

/-- **Yet no approximate bisimulation at any precision relates the world to its
image.** -/
theorem not_approxBisimilar (ε : ℝ) :
    ¬ ApproxBisimilar dist (fun a b : ℕ => Succ.step a = b) (fun a b : PUnit.{1} => id a = b)
      Drift.observe observeMind ε 0 PUnit.unit := by
  intro bisimilar
  have close := (approxBisimilar_update_iff dist_comm).mp bisimilar
  obtain ⟨n, large⟩ := exists_nat_gt ε
  have bound := close n
  rw [Succ.step_iterate, zero_add, observeMind, Drift.observe, Real.dist_eq, sub_zero,
    Nat.abs_cast] at bound
  linarith

end Collapse

/-! ## Update squares as bounded-defect correspondences -/

section UpdateCategory

/-- Mind states, with every abstract update as an arrow between any two
states. -/
structure UpdateObject (Y : Type u) where
  /-- The mind state. -/
  state : Y

instance (Y : Type u) : Category (UpdateObject Y) where
  Hom _ _ := Y → Y
  id _ := fun y => y
  comp first second := fun y => second (first y)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The distance of two abstract updates, measured at the source state. -/
noncomputable def evaluationGeometry (Y : Type u) [PseudoMetricSpace Y]
    (source target : UpdateObject Y) : ValueGeometry (source ⟶ target) :=
  (ValueGeometry.ofPseudoMetric Y).comap fun update : Y → Y => update source.state

variable {M X Y : Type u} [Monoid M] [MulAction M X]

/-- The monoid element of an arrow of the action category. -/
def process {p q : ActionCategory M X} (arrow : p ⟶ q) : M :=
  arrow.val

theorem process_smul {p q : ActionCategory M X} (arrow : p ⟶ q) :
    process arrow • p.back = q.back :=
  arrow.2

theorem process_id (p : ActionCategory M X) : process (𝟙 p) = 1 :=
  ActionCategory.id_val p

theorem process_comp {p q r : ActionCategory M X} (earlier : p ⟶ q) (later : q ⟶ r) :
    process (earlier ≫ later) = process later * process earlier :=
  ActionCategory.comp_val earlier later

/-- **A model of world processes as a path correspondence over the view**: world
states go to their views, a world process to the abstract update the model
assigns to it. -/
def updateCorrespondence (view : X → Y) (model : M → Y → Y)
    (geometry : ∀ source target : UpdateObject Y, ValueGeometry (source ⟶ target)) :
    PathCorrespondence (ActionCategory M X) (UpdateObject Y) where
  obj p := ⟨view p.back⟩
  map arrow := model (process arrow)
  geometry source target := geometry ⟨view source.back⟩ ⟨view target.back⟩

/-- **A homomorphic model is an exact correspondence**, whatever the
geometry. -/
theorem updateCorrespondence_exact {view : X → Y} {model : M → Y → Y}
    {geometry : ∀ source target : UpdateObject Y, ValueGeometry (source ⟶ target)}
    (one : model 1 = fun y => y) (mul : ∀ m n, model (n * m) = fun y => model n (model m y)) :
    (updateCorrespondence view model geometry).Exact := by
  refine ⟨fun p => ?_, fun earlier later => ?_⟩
  · change model (process (𝟙 p)) = fun y => y
    rw [process_id, one]
  · change model (process (earlier ≫ later)) = fun y => model (process later)
      (model (process earlier) y)
    rw [process_comp, mul]

variable [PseudoMetricSpace Y] {view : X → Y} {model : M → Y → Y} {ε : M → ℝ}

/-- **The identity defect is at most the error of the identity square.** -/
theorem identityDefect_le (squares : ∀ m, ApproxSquare dist view view (m • ·) (model m) (ε m))
    (p : ActionCategory M X) :
    (updateCorrespondence view model (evaluationGeometry Y)).identityDefect p ≤ ε 1 := by
  change dist (model (process (𝟙 p)) (view p.back)) (view p.back) ≤ ε 1
  have square : dist (view ((1 : M) • p.back)) (model 1 (view p.back)) ≤ ε 1 :=
    squares 1 p.back
  rw [one_smul] at square
  rw [process_id, dist_comm]
  exact square

/-- **The composition defect is at most the composite square's error plus the
error of composing the two squares.** -/
theorem compositionDefect_le (squares : ∀ m, ApproxSquare dist view view (m • ·) (model m) (ε m))
    {K : M → ℝ} (nonnegative : ∀ m, 0 ≤ K m)
    (lipschitz : ∀ m a b, dist (model m a) (model m b) ≤ K m * dist a b)
    {p q r : ActionCategory M X} (earlier : p ⟶ q) (later : q ⟶ r) :
    (updateCorrespondence view model (evaluationGeometry Y)).compositionDefect earlier later ≤
      ε (process later * process earlier) +
        (ε (process later) + K (process later) * ε (process earlier)) := by
  set m := process earlier
  set n := process later
  change dist (model (process (earlier ≫ later)) (view p.back))
      (model n (model m (view p.back))) ≤ _
  rw [process_comp]
  have composite := ApproxSquare.comp (dist_triangle (α := Y)) (ω := fun t => K n * t)
    (fun _ _ le => mul_le_mul_of_nonneg_left le (nonnegative n)) (lipschitz n)
    (squares m) (squares n) p.back
  have direct : dist (view ((n * m) • p.back)) (model (n * m) (view p.back)) ≤ ε (n * m) :=
    squares (n * m) p.back
  change dist (view (n • m • p.back)) (model n (model m (view p.back))) ≤
    ε n + K n * ε m at composite
  rw [mul_smul] at direct
  calc dist (model (n * m) (view p.back)) (model n (model m (view p.back)))
      ≤ dist (model (n * m) (view p.back)) (view (n • m • p.back)) +
          dist (view (n • m • p.back)) (model n (model m (view p.back))) :=
        dist_triangle _ _ _
    _ ≤ ε (n * m) + (ε n + K n * ε m) := by
        rw [dist_comm] at direct
        exact add_le_add direct composite

/-- **Update squares with errors `ε` form a bounded-defect mind–world
correspondence over the view.** -/
noncomputable def boundedOfSquares
    (squares : ∀ m, ApproxSquare dist view view (m • ·) (model m) (ε m))
    {K : M → ℝ} (nonnegative : ∀ m, 0 ≤ K m)
    (lipschitz : ∀ m a b, dist (model m a) (model m b) ≤ K m * dist a b) :
    BoundedPathCorrespondence (ActionCategory M X) (UpdateObject Y) where
  toPathCorrespondence := updateCorrespondence view model (evaluationGeometry Y)
  identityBudget _ := ε 1
  compositionBudget earlier later :=
    ε (process later * process earlier) +
      (ε (process later) + K (process later) * ε (process earlier))
  identityBudget_nonnegative p := (dist_nonneg).trans (squares 1 p.back)
  compositionBudget_nonnegative {p q _} _ _ :=
    add_nonneg ((dist_nonneg).trans (squares _ p.back))
      (add_nonneg ((dist_nonneg).trans (squares _ q.back))
        (mul_nonneg (nonnegative _) ((dist_nonneg).trans (squares _ p.back))))
  identity_bounded := identityDefect_le squares
  composition_bounded := compositionDefect_le squares nonnegative lipschitz

end UpdateCategory

/-! ### Exact squares over a quotient view -/

section Quotient

variable {M X : Type u} [Monoid M] [MulAction M X] (E : Setoid X)
  (compatible : ∀ (m : M) ⦃x y : X⦄, E x y → E (m • x) (m • y))

/-- The abstract update induced on the quotient. -/
def quotientModel (m : M) : Quotient E → Quotient E :=
  Quotient.map (m • ·) (compatible m)

/-- **Every square over the quotient view commutes on the nose.** -/
theorem quotient_square (m : M) (x : X) :
    Quotient.mk E (m • x) = quotientModel E compatible m (Quotient.mk E x) :=
  rfl

/-- **Exact squares over a quotient view give an exact correspondence**, for
any geometry: the model is a monoid action on the quotient. -/
theorem quotientCorrespondence_exact
    (geometry : ∀ source target : UpdateObject (Quotient E), ValueGeometry (source ⟶ target)) :
    (updateCorrespondence (Quotient.mk E) (quotientModel E compatible) geometry).Exact := by
  apply updateCorrespondence_exact
  · funext y
    induction y using Quotient.inductionOn with
    | h x => exact congrArg (Quotient.mk E) (one_smul M x)
  · intro m n
    funext y
    induction y using Quotient.inductionOn with
    | h x => exact congrArg (Quotient.mk E) (mul_smul n m x)

end Quotient

/-! ### Control: a model wrong on one composite -/

namespace Fold

/-- Scaling by `n`, except that the model of `4` adds one. -/
noncomputable def model (n : ℕ) (y : ℝ) : ℝ :=
  if n = 4 then n • y + 1 else n • y

/-- The error of each square. -/
def error (n : ℕ) : ℝ :=
  if n = 4 then 1 else 0

theorem squares : ∀ n : ℕ, ApproxSquare dist (id : ℝ → ℝ) id (n • ·) (model n) (error n) := by
  intro n x
  change dist (n • x) (model n x) ≤ error n
  unfold model error
  split_ifs
  · rw [Real.dist_eq, sub_add_cancel_left, abs_neg, abs_one]
  · rw [dist_self]

theorem lipschitz (n : ℕ) (a b : ℝ) : dist (model n a) (model n b) ≤ (n : ℝ) * dist a b := by
  unfold model
  split_ifs
  · rw [Real.dist_eq, Real.dist_eq, add_sub_add_right_eq_sub, nsmul_eq_mul, nsmul_eq_mul,
      ← mul_sub, abs_mul, Nat.abs_cast]
  · rw [Real.dist_eq, Real.dist_eq, nsmul_eq_mul, nsmul_eq_mul, ← mul_sub, abs_mul,
      Nat.abs_cast]

/-- The bounded-defect correspondence of the model. -/
noncomputable def correspondence :
    BoundedPathCorrespondence (ActionCategory ℕ ℝ) (UpdateObject ℝ) :=
  boundedOfSquares squares (K := fun n => (n : ℝ)) (fun n => Nat.cast_nonneg n) lipschitz

/-- Doubling at `0`. -/
def double : (ActionCategory.objEquiv ℕ ℝ 0 : ActionCategory ℕ ℝ) ⟶
    (ActionCategory.objEquiv ℕ ℝ 0 : ActionCategory ℕ ℝ) :=
  ⟨(2 : ℕ), by change (2 : ℕ) • (0 : ℝ) = 0; exact smul_zero 2⟩

/-- **The composition defect of doubling twice is one**, the error of the
square of `4`: the bound of `compositionDefect_le` is attained. -/
theorem compositionDefect_eq :
    correspondence.toPathCorrespondence.compositionDefect double double = 1 := by
  change dist (model (process (double ≫ double)) (0 : ℝ))
    (model (process double) (model (process double) 0)) = 1
  rw [process_comp]
  change dist (model (2 * 2) 0) (model 2 (model 2 0)) = 1
  norm_num [model, Real.dist_eq]

/-- **The model is not exact.** -/
theorem not_exact : ¬ correspondence.toPathCorrespondence.Exact :=
  correspondence.toPathCorrespondence.positive_compositionDefect_not_exact double double
    (by rw [compositionDefect_eq]; exact one_pos)

end Fold

/-! ## Goal weighting -/

section Goals

variable {World : Type*} [Category World] {Mind : Type*} [Category Mind]

/-- A composable pair of world paths. -/
structure ComposablePair (World : Type*) [Category World] where
  /-- The first endpoint. -/
  first : World
  /-- The middle endpoint. -/
  middle : World
  /-- The last endpoint. -/
  last : World
  /-- The earlier path. -/
  earlier : first ⟶ middle
  /-- The later path. -/
  later : middle ⟶ last

/-- **The goal-weighted composition defect** over a finite sample of
composable pairs: each defect weighted by the goal weight of the composite
path. -/
noncomputable def goalWeightedDefect (correspondence : MindWorldCorrespondence World Mind)
    (pairs : List (ComposablePair World)) : ℝ :=
  (pairs.map fun pair => correspondence.goalWeight (pair.earlier ≫ pair.later) *
    correspondence.toPathCorrespondence.compositionDefect pair.earlier pair.later).sum

/-- **Exact correspondences have zero goal-weighted defect.** -/
theorem goalWeightedDefect_eq_zero_of_exact (correspondence : MindWorldCorrespondence World Mind)
    (exact : correspondence.toPathCorrespondence.Exact) (pairs : List (ComposablePair World)) :
    goalWeightedDefect correspondence pairs = 0 := by
  unfold goalWeightedDefect
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rw [List.map_cons, List.sum_cons, ih, add_zero,
        correspondence.toPathCorrespondence.compositionDefect_eq_zero_of_exact exact, mul_zero]

end Goals

namespace Fold

/-- Goals ignore every path whose process is `4`. -/
noncomputable def goalCorrespondence :
    MindWorldCorrespondence (ActionCategory ℕ ℝ) (UpdateObject ℝ) where
  toBoundedPathCorrespondence := correspondence
  goalWeight path := if process path = 4 then 0 else 1
  resourceCost _ := 0
  goalWeight_nonnegative path := by
    split_ifs <;> norm_num
  resourceCost_nonnegative _ := le_rfl

/-- **Goal weighting can hide a defect**: the goal-weighted defect of doubling
twice vanishes, yet the correspondence is not exact. -/
theorem goalWeighted_not_exact :
    goalWeightedDefect goalCorrespondence [⟨_, _, _, double, double⟩] = 0 ∧
      ¬ goalCorrespondence.toPathCorrespondence.Exact := by
  refine ⟨?_, not_exact⟩
  change goalCorrespondence.goalWeight (double ≫ double) *
    correspondence.toPathCorrespondence.compositionDefect double double + 0 = 0
  have weight : goalCorrespondence.goalWeight (double ≫ double) = 0 := by
    change (if process (double ≫ double) = 4 then (0 : ℝ) else 1) = 0
    rw [process_comp]
    rfl
  rw [weight, zero_mul, add_zero]

end Fold

end Mettapedia.Cybernetics.MindWorldApproximation
