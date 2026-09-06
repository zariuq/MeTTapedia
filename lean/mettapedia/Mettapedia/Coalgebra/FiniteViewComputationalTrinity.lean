import Mathlib.CategoryTheory.Discrete.Basic
import Mettapedia.Coalgebra.CoherentFiniteViewSystem
import Mettapedia.Computability.ComputationalTrinity

/-!
# Computational trinity over coherent finite-view systems

An operational state map, a behavior type, and a coherent finite-view system
form a commuting computational-trinity comparison without any exactness
assumption.  A compatible exact trinity exists precisely when both maps are
bijective:

* operational states represent behaviors faithfully and completely; and
* behaviors are represented faithfully and completely by coherent towers.

The theorem is independent of streams.  Streams instantiate the finite-view
interface, while later polynomial or container coalgebras need only provide
their own behavior observation and exactness proof.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.FiniteViewComputationalTrinity

open CategoryTheory
open Mettapedia.Coalgebra.CoherentFiniteViewSystem
open Mettapedia.Coalgebra.StreamFinality
open Mettapedia.Computability.ComputationalTrinity

universe u

abbrev Context := Discrete PUnit

private def here : Contextᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

def stateFace (State : Type u) :
    Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj State

def behaviorFace (Behavior : Type u) :
    Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj Behavior

def towerFace (system : FiniteViewSystem.{u}) :
    Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj system.Tower

def stateToBehavior {State : Type u} {Behavior : Type u}
    (unfold : State → Behavior) :
    stateFace State ⟶ behaviorFace Behavior :=
  (Functor.const Contextᵒᵖ).map (↾unfold)

def behaviorToTower {Behavior : Type u}
    {system : FiniteViewSystem.{u}}
    (observation : BehaviorObservation system Behavior) :
    behaviorFace Behavior ⟶ towerFace system :=
  (Functor.const Contextᵒᵖ).map (↾observation.toTower)

def stateToTower {State : Type u} {Behavior : Type u}
    {system : FiniteViewSystem.{u}}
    (unfold : State → Behavior)
    (observation : BehaviorObservation system Behavior) :
    stateFace State ⟶ towerFace system :=
  (Functor.const Contextᵒᵖ).map (↾(observation.toTower ∘ unfold))

/-- Operational states, behaviors, and coherent finite views always form a
commuting comparison. -/
def comparison {State : Type u} {Behavior : Type u}
    {system : FiniteViewSystem.{u}}
    (unfold : State → Behavior)
    (observation : BehaviorObservation system Behavior) :
    Comparison.{0, 0, u} Context where
  program := stateFace State
  logic := behaviorFace Behavior
  space := towerFace system
  programToLogic := stateToBehavior unfold
  logicToSpace := behaviorToTower observation
  programToSpace := stateToTower unfold observation
  coherence := by
    ext context state
    rfl

/-- Information loss in the spatial face is exactly collision of the
composite state-to-tower map. -/
theorem comparison_loses_iff_composite_collision
    {State : Type u} {Behavior : Type u}
    {system : FiniteViewSystem.{u}}
    (unfold : State → Behavior)
    (observation : BehaviorObservation system Behavior) :
    (comparison unfold observation).LosesProgramInformation ↔
      ∃ left right : State,
        left ≠ right ∧
          observation.toTower (unfold left) =
            observation.toTower (unfold right) := by
  constructor
  · rintro ⟨_context, left, right, different, sameTower⟩
    exact ⟨left, right, different, sameTower⟩
  · rintro ⟨left, right, different, sameTower⟩
    exact ⟨here, left, right, different, sameTower⟩

/-! ## Compatible exactness -/

/-- Exactness includes agreement with the independently supplied maps; an
unrelated isomorphism between carrier types is insufficient. -/
structure ExactTrinityWitness
    {State : Type u} {Behavior : Type u}
    {system : FiniteViewSystem.{u}}
    (unfold : State → Behavior)
    (observation : BehaviorObservation system Behavior) where
  stateBehavior : stateFace State ≅ behaviorFace Behavior
  stateBehavior_agrees : stateBehavior.hom = stateToBehavior unfold
  behaviorTower : behaviorFace Behavior ≅ towerFace system
  behaviorTower_agrees : behaviorTower.hom = behaviorToTower observation

private theorem constantIso_bijective
    {Source : Type u} {Target : Type u}
    (mapping : Source → Target)
    (isomorphism : stateFace Source ≅ behaviorFace Target)
    (agrees : isomorphism.hom = stateToBehavior mapping) :
    Function.Bijective mapping := by
  have componentAgreement :=
    congrArg (fun transformation => transformation.app here) agrees
  constructor
  · intro left right equalImages
    apply (isomorphism.app here).toEquiv.injective
    change isomorphism.hom.app here left = isomorphism.hom.app here right
    rw [componentAgreement]
    exact equalImages
  · intro target
    obtain ⟨source, represents⟩ :=
      (isomorphism.app here).toEquiv.surjective target
    change Source at source
    change isomorphism.hom.app here source = target at represents
    refine ⟨source, ?_⟩
    change (stateToBehavior mapping).app here source = target
    rw [← componentAgreement]
    exact represents

namespace ExactTrinityWitness

variable {State : Type u} {Behavior : Type u}
  {system : FiniteViewSystem.{u}}
  {unfold : State → Behavior}
  {observation : BehaviorObservation system Behavior}

theorem stateBehavior_bijective
    (witness : ExactTrinityWitness unfold observation) :
    Function.Bijective unfold :=
  constantIso_bijective unfold witness.stateBehavior
    witness.stateBehavior_agrees

theorem behaviorTower_exact
    (witness : ExactTrinityWitness unfold observation) :
    observation.Exact := by
  have componentAgreement :=
    congrArg (fun transformation => transformation.app here)
      witness.behaviorTower_agrees
  constructor
  · intro left right equalTowers
    apply (witness.behaviorTower.app here).toEquiv.injective
    change witness.behaviorTower.hom.app here left =
      witness.behaviorTower.hom.app here right
    rw [componentAgreement]
    exact equalTowers
  · intro tower
    obtain ⟨behavior, represents⟩ :=
      (witness.behaviorTower.app here).toEquiv.surjective tower
    change Behavior at behavior
    change witness.behaviorTower.hom.app here behavior = tower at represents
    refine ⟨behavior, ?_⟩
    change (behaviorToTower observation).app here behavior = tower
    rw [← componentAgreement]
    exact represents

/-- Forget compatible exactness to the general exact computational-trinity
interface. -/
def toExact (witness : ExactTrinityWitness unfold observation) :
    Exact.{0, 0, u} Context where
  program := stateFace State
  logic := behaviorFace Behavior
  space := towerFace system
  programLogic := witness.stateBehavior
  logicSpace := witness.behaviorTower

end ExactTrinityWitness

/-- Bijectivity of both supplied maps constructs the compatible exact
trinity. -/
noncomputable def exactTrinityWitnessOfBijective
    {State : Type u} {Behavior : Type u}
    {system : FiniteViewSystem.{u}}
    (unfold : State → Behavior)
    (observation : BehaviorObservation system Behavior)
    (stateExact : Function.Bijective unfold)
    (viewExact : observation.Exact) :
    ExactTrinityWitness unfold observation where
  stateBehavior :=
    (Functor.const Contextᵒᵖ).mapIso
      (Equiv.ofBijective unfold stateExact).toIso
  stateBehavior_agrees := rfl
  behaviorTower :=
    (Functor.const Contextᵒᵖ).mapIso
      (Equiv.ofBijective observation.toTower viewExact).toIso
  behaviorTower_agrees := rfl

/-- Exact computational-trinity compatibility exists exactly when the
operational and finite-view maps are both faithful and complete. -/
theorem exactTrinityWitness_nonempty_iff
    {State : Type u} {Behavior : Type u}
    {system : FiniteViewSystem.{u}}
    (unfold : State → Behavior)
    (observation : BehaviorObservation system Behavior) :
    Nonempty (ExactTrinityWitness unfold observation) ↔
      Function.Bijective unfold ∧ observation.Exact := by
  constructor
  · rintro ⟨witness⟩
    exact ⟨witness.stateBehavior_bijective, witness.behaviorTower_exact⟩
  · rintro ⟨stateExact, viewExact⟩
    exact ⟨exactTrinityWitnessOfBijective unfold observation
      stateExact viewExact⟩

/-! ## Independence controls over exact stream finite views -/

namespace Canary

abbrev booleanObservation := streamObservation Bool

/-- A faithful operational carrier representing only constant behaviors. -/
def constantBehavior : Bool → Stream Bool := constant

theorem constantBehavior_injective :
    Function.Injective constantBehavior := by
  intro left right equalStreams
  exact congrFun equalStreams 0

theorem constantBehavior_not_surjective :
    ¬ Function.Surjective constantBehavior := by
  intro surjective
  obtain ⟨label, represents⟩ :=
    surjective (changedAt 0 false true)
  have atZero := congrFun represents 0
  have atOne := congrFun represents 1
  cases label <;> simp [constantBehavior, constant, changedAt] at atZero atOne

/-- A complete carrier with an operational tag forgotten by behavior. -/
def taggedBehavior : Stream Bool × Bool → Stream Bool := Prod.fst

theorem taggedBehavior_surjective :
    Function.Surjective taggedBehavior := by
  intro stream
  exact ⟨(stream, false), rfl⟩

theorem taggedBehavior_not_injective :
    ¬ Function.Injective taggedBehavior := by
  intro injective
  have equalPairs := injective
    (show taggedBehavior (constant false, false) =
      taggedBehavior (constant false, true) by rfl)
  exact Bool.false_ne_true (congrArg Prod.snd equalPairs)

/-- Faithfulness without completeness prevents an exact trinity even though
the comparison loses no operational information. -/
theorem faithful_incomplete_comparison_not_exact :
    ¬ (comparison constantBehavior booleanObservation).LosesProgramInformation ∧
      ¬ Nonempty (ExactTrinityWitness constantBehavior booleanObservation) := by
  constructor
  · rw [comparison_loses_iff_composite_collision]
    rintro ⟨left, right, different, sameTower⟩
    have sameBehavior :=
      (streamObservation_exact Bool).1 sameTower
    exact different (constantBehavior_injective sameBehavior)
  · intro witness
    have exactMaps :=
      (exactTrinityWitness_nonempty_iff constantBehavior
        booleanObservation).mp witness
    exact constantBehavior_not_surjective exactMaps.1.2

/-- Completeness without faithfulness is observably lossy. -/
theorem complete_unfaithful_comparison_loses :
    (comparison taggedBehavior booleanObservation).LosesProgramInformation ∧
      ¬ Nonempty (ExactTrinityWitness taggedBehavior booleanObservation) := by
  constructor
  · rw [comparison_loses_iff_composite_collision]
    refine ⟨(constant false, false), (constant false, true), ?_, rfl⟩
    intro equalPairs
    exact Bool.false_ne_true (congrArg Prod.snd equalPairs)
  · intro witness
    have exactMaps :=
      (exactTrinityWitness_nonempty_iff taggedBehavior
        booleanObservation).mp witness
    exact taggedBehavior_not_injective exactMaps.1.1

/-- The final behavior carrier itself forms an exact trinity with its
coherent finite views. -/
noncomputable def exactStreamTrinity :
    ExactTrinityWitness (id : Stream Bool → Stream Bool)
      booleanObservation :=
  exactTrinityWitnessOfBijective id booleanObservation
    Function.bijective_id (streamObservation_exact Bool)

end Canary

#print axioms comparison_loses_iff_composite_collision
#print axioms ExactTrinityWitness.stateBehavior_bijective
#print axioms ExactTrinityWitness.behaviorTower_exact
#print axioms exactTrinityWitness_nonempty_iff
#print axioms Canary.constantBehavior_injective
#print axioms Canary.constantBehavior_not_surjective
#print axioms Canary.taggedBehavior_not_injective
#print axioms Canary.faithful_incomplete_comparison_not_exact
#print axioms Canary.complete_unfaithful_comparison_loses
#print axioms Canary.exactStreamTrinity

end Mettapedia.Coalgebra.FiniteViewComputationalTrinity
