import Mettapedia.GSLT.Distinction.RelationalIsometry
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverAdequacy

/-!
# Phase-independent public-return logical distance through the full spine

The graded observations ask whether a function may become publicly available.
The modal transitions are finite reachability modulo the authored equations.
All related runtime phases carry this observation; the existing span isometry
therefore compares actual lambda and rho states. This is a weak reachability
metric, distinct from the one-event polyadic block metric and from primitive
communication counts. No finite-branching claim about reachability is inferred
from finite branching of primitive steps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoMetric

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open NamePassingLambda NamePassingEnvironmentEquationsNative

def sourceObserver (Γ : Ctx sig) : System (sourceTheory Γ).closure :=
  .ofObserved ⟨Unit, fun _ source => NamePassingObserverAdequacy.MayReturn source⟩
    (fun _ _ _ equal =>
      (semanticDiamond (sourceTheory Γ).closure (NamePassingValueNative.sourcePredicate Γ)).2 equal)

def targetObserver {Γ : Ctx sig} (world : NamePassingSpine.World Γ) :
    System RhoUnaryReadback.Target.closure :=
  .ofObserved ⟨Unit, fun _ current =>
    (semanticDiamond RhoUnaryReadback.Target.closure
      (RhoUnaryInputObservation.targetPredicate world .zero)).1 current⟩
    (fun _ _ _ equal =>
      (semanticDiamond RhoUnaryReadback.Target.closure
        (RhoUnaryInputObservation.targetPredicate world .zero)).2 equal)

noncomputable def sourceReadings (Γ : Ctx sig) := GradedObservations.ofSystem (sourceObserver Γ)
noncomputable def targetReadings {Γ : Ctx sig} (world : NamePassingSpine.World Γ) :=
  GradedObservations.ofSystem (targetObserver world)

private theorem values_agree {Γ : Ctx sig} (world : NamePassingSpine.World Γ)
    (observation : Unit) {source : Expr Γ} {current : RhoUnaryReadback.TargetProcess}
    (related : (NamePassingSpine.correspondence world).related source current) :
    (targetReadings world).value observation current = (sourceReadings Γ).value observation source := by
  classical
  simp only [targetReadings, sourceReadings, GradedObservations.ofSystem, targetObserver,
    sourceObserver, System.ofObserved]
  have observed := NamePassingSpine.native_may_return_iff world related
  by_cases returned : NamePassingObserverAdequacy.MayReturn source
  · simp only [returned, observed.mp returned, if_true]
  · simp only [returned, mt observed.mpr returned, if_false]

noncomputable def comparison {Γ : Ctx sig} (world : NamePassingSpine.World Γ)
    (discount : ℝ) (nonneg : 0 ≤ discount) (bounded : discount ≤ 1) :=
  closureObservationRelation (NamePassingSpine.correspondence world)
    (sourceReadings Γ) (targetReadings world) id (values_agree world) discount nonneg bounded

theorem logicalDistance_eq {Γ : Ctx sig} (world : NamePassingSpine.World Γ)
    (discount : ℝ) (nonneg : 0 ≤ discount) (bounded : discount ≤ 1)
    {left right : Expr Γ} {left' right' : RhoUnaryReadback.TargetProcess}
    (before : (NamePassingSpine.correspondence world).related left left')
    (after : (NamePassingSpine.correspondence world).related right right') :
    (GradedSystem.stepping RhoUnaryReadback.Target.closure (targetReadings world)
      discount nonneg bounded).logicalDistance left' right' =
    (GradedSystem.stepping (sourceTheory Γ).closure (sourceReadings Γ)
      discount nonneg bounded).logicalDistance left right := by
  apply (comparison world discount nonneg bounded).logicalDistance_eq
    Function.surjective_id Function.surjective_id
  · exact ⟨left, left', (sourceTheory Γ).equations.iseqv.refl _,
      RhoUnaryReadback.Target.equations.iseqv.refl _, before⟩
  · exact ⟨right, right', (sourceTheory Γ).equations.iseqv.refl _,
      RhoUnaryReadback.Target.equations.iseqv.refl _, after⟩

theorem compiled_logicalDistance_eq {Γ : Ctx sig} (world : NamePassingSpine.World Γ)
    (discount : ℝ) (nonneg : 0 ≤ discount) (bounded : discount ≤ 1)
    (left right : Expr Γ) (leftCode rightCode : RhoUnaryCode.Code 0)
    (leftSupplied : NamePassingRho.compile left (NamePassingUnaryForward.references Γ) .zero
      world.world = some leftCode)
    (rightSupplied : NamePassingRho.compile right (NamePassingUnaryForward.references Γ) .zero
      world.world = some rightCode) :
    (GradedSystem.stepping RhoUnaryReadback.Target.closure (targetReadings world)
      discount nonneg bounded).logicalDistance
      (RhoUnaryReadback.runtimeProcess leftCode world.available)
      (RhoUnaryReadback.runtimeProcess rightCode world.available) =
    (GradedSystem.stepping (sourceTheory Γ).closure (sourceReadings Γ)
      discount nonneg bounded).logicalDistance left right :=
  logicalDistance_eq world discount nonneg bounded
    (NamePassingSpine.initial_related left world leftCode leftSupplied)
    (NamePassingSpine.initial_related right world rightCode rightSupplied)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoMetric
