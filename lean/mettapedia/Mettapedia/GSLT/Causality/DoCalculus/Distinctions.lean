import Mettapedia.GSLT.Causality.DoCalculus.Adjustment
import Mettapedia.GSLT.Causality.DoCalculus.BowArc
import Mettapedia.GSLT.Causality.DoCalculus.FrontDoor
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Identification as factorization through the observational joint

A query on a class of models is identified from the observational joint when
the query factors through that joint: some function of the joint recovers the
query on every model in the class. A non-trivial fibre is two models with the
same joint and different query values, and it is the failure of identification.

Parent adjustment and the front-door formula are such functions. The bow is a
fibre: the two conditional tables induce one joint, and `do(X = true)` gives
`Y` mass `1` in one table and mass `1/2` in the other.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open scoped BigOperators ENNReal

/-- A query is identified from an observational reading when the reading
retains it. When the reading is surjective, this is agreement on fibres. -/
theorem identified_iff_constant_on_fibers {Model Shadow Query : Type*}
    {observational : Model → Shadow} (onto : Function.Surjective observational)
    (query : Model → Query) :
    Factors observational query ↔ ConstantOnFibers observational query :=
  factors_iff_constantOnFibers onto query

/-! ## The bow does not factor -/

/-- The observational joint of a bow table. -/
noncomputable def bowShadow :
    (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT → (Bow → Bool) → ℝ≥0∞ :=
  fun cpt => cpt.jointWeight

/-- `P(Y = true | do(X = true))` on a bow table. -/
noncomputable def bowQuery :
    (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT → ℝ≥0∞ :=
  fun cpt => bowDoMass cpt true

/-- The two bow tables are one observational joint and two interventional masses. -/
noncomputable def bowFiber : NonTrivialFiber bowShadow bowQuery where
  left := bowCPT1
  right := bowCPT2
  sameShadow := funext bow_joint_agree
  differentValue := bow_effect_not_identified.2

/-- The effect of `X` on `Y` in the bow is not identified from the joint. -/
theorem bow_query_not_identified : ¬ Factors bowShadow bowQuery :=
  bowFiber.not_factors

/-! ## Parent adjustment is a factoring map -/

variable {V β : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype β] [DecidableEq β] [MeasurableSpace β]
variable (graph : DirectedGraph V) (hAcyclic : graph.IsAcyclic)
variable [DecidableRel graph.edges]

/-- Tables whose treatment row is positive at the intervened value. -/
abbrev PositiveAt (treatment : V) (x : β) :=
  {cpt : (network (β := β) graph hAcyclic).DiscreteCPT //
    ∀ pa : ParentFun (β := β) graph treatment,
      cptAt graph hAcyclic cpt treatment pa x ≠ 0}

/-- The parent-adjustment formula, read off an arbitrary joint. -/
noncomputable def adjustOfJoint (treatment outcome : V) (x y : β)
    (joint : (V → β) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ pa : ParentFun (β := β) graph treatment,
    ((∑ f, if parentsMatch graph treatment pa f && decide (f treatment = x) &&
          decide (f outcome = y) then joint f else 0) /
      (∑ f, if parentsMatch graph treatment pa f && decide (f treatment = x) then
          joint f else 0)) *
      (∑ f, if parentsMatch graph treatment pa f then joint f else 0)

/-- On positive treatment rows, `P(y | do(x))` is the parent-adjustment
formula of the observational joint. -/
theorem parent_adjustment_identified (treatment outcome : V) (x y : β) :
    Factors
      (fun cpt : PositiveAt graph hAcyclic treatment x => cpt.1.jointWeight)
      (fun cpt => interventionalMass graph hAcyclic cpt.1 treatment outcome x y) := by
  refine ⟨adjustOfJoint graph treatment outcome x y, fun cpt => ?_⟩
  dsimp
  rw [parentAdjustment graph hAcyclic cpt.1 treatment outcome x y cpt.2]
  unfold parentMass
  rfl

/-! ## The front door is a factoring map -/

/-- Smoking tables with a positive smoking marginal and a positive tar row. -/
abbrev FrontPositive (s0 : β) :=
  {cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT //
    obs cpt (fun f => f .s = s0) ≠ 0 ∧ ∀ bs bt, pt cpt bs bt ≠ 0}

/-- Mass of a decidable event in an arbitrary joint on the smoking graph. -/
noncomputable def smokeMass (joint : (Smoke → β) → ℝ≥0∞)
    (pred : (Smoke → β) → Prop) [DecidablePred pred] : ℝ≥0∞ :=
  ∑ f, if pred f then joint f else 0

omit [DecidableEq β] in
lemma obs_eq_smokeMass
    (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (pred : (Smoke → β) → Prop) [DecidablePred pred] :
    obs cpt pred = smokeMass cpt.jointWeight pred := rfl

/-- The front-door formula, read off an arbitrary joint. -/
noncomputable def frontDoorOf (s0 c0 : β) (joint : (Smoke → β) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ bt, (smokeMass joint (fun f => f .s = s0 ∧ f .t = bt) /
      smokeMass joint (fun f => f .s = s0)) *
    (∑ bs, (smokeMass joint (fun f => f .c = c0 ∧ f .t = bt ∧ f .s = bs) /
        smokeMass joint (fun f => f .s = bs ∧ f .t = bt)) *
      smokeMass joint (fun f => f .s = bs))

/-- On a positive smoking marginal and positive tar rows,
`P(c0 | do(s0))` is the front-door formula of the observational joint. -/
theorem front_door_identified (s0 c0 : β) :
    Factors
      (fun cpt : FrontPositive s0 => cpt.1.jointWeight)
      (fun cpt => doMass cpt.1 s0 c0) := by
  refine ⟨frontDoorOf s0 c0, fun cpt => ?_⟩
  dsimp
  rw [frontDoor cpt.1 s0 c0 cpt.2.1 cpt.2.2]
  simp only [obs_eq_smokeMass]
  rfl
