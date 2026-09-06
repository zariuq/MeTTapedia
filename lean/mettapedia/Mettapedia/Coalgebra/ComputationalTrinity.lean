import Mettapedia.Coalgebra.CoherentPrefixTower
import Mettapedia.Coalgebra.StreamGSLT
import Mettapedia.Computability.ComputationalTrinity
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Coalgebraic behavior in the computational trinity

A deterministic coalgebra supplies three semantically distinct faces:

* operational states;
* their final stream behaviors; and
* coherent towers of finite observations.

They form a commuting computational-trinity comparison.  The behavior and
finite-view-tower faces are always equivalent.  Operational states join an
exact trinity only when unfolding is both faithful and complete.  Faithfulness
alone reflects operational distinctions but does not assert that every
behavior is represented; completeness alone represents every behavior but
may identify distinct operational states.

This is a choice-surface theorem, not a proposed language definition.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.ComputationalTrinity

open CategoryTheory
open Mettapedia.Coalgebra.StreamFinality
open Mettapedia.Coalgebra.StreamGSLT
open Mettapedia.Coalgebra.CoherentPrefixTower
open Mettapedia.Computability.ComputationalTrinity

universe u

abbrev Context := Discrete PUnit

private def here : Contextᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

/-! ## The three faces and their comparison -/

def stateFace {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label) :
    Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj coalgebra.Carrier

def behaviorFace (Label : Type u) :
    Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj (Stream Label)

def towerFace (Label : Type u) :
    Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj (Tower Label)

def stateToBehavior {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label) :
    stateFace coalgebra ⟶ behaviorFace Label :=
  (Functor.const Contextᵒᵖ).map
    (↾(unfold coalgebra : coalgebra.Carrier → Stream Label))

def behaviorToTower (Label : Type u) :
    behaviorFace Label ⟶ towerFace Label :=
  (Functor.const Contextᵒᵖ).map
    (↾(Tower.ofStream : Stream Label → Tower Label))

def stateToTower {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label) :
    stateFace coalgebra ⟶ towerFace Label :=
  (Functor.const Contextᵒᵖ).map
    (↾(Tower.ofStream ∘ unfold coalgebra))

/-- Operational states, final behavior, and coherent finite-view towers form
a commuting comparison without any exactness assumption. -/
def comparison {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label) :
    Comparison.{0, 0, u} Context where
  program := stateFace coalgebra
  logic := behaviorFace Label
  space := towerFace Label
  programToLogic := stateToBehavior coalgebra
  logicToSpace := behaviorToTower Label
  programToSpace := stateToTower coalgebra
  coherence := by
    ext context state
    rfl

/-! ## Exactness property bag -/

/-- Every stream behavior is represented by some operational state. -/
def BehaviorallyComplete {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label) : Prop :=
  Function.Surjective (unfold coalgebra)

/-- Operational state identity and stream behavior coincide exactly. -/
def BehaviorallyExact {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label) : Prop :=
  Function.Bijective (unfold coalgebra)

theorem behaviorallyExact_iff_faithful_and_complete
    {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label) :
    BehaviorallyExact coalgebra ↔
      BehaviorallyFaithful coalgebra ∧ BehaviorallyComplete coalgebra :=
  Iff.rfl

/-- The behavior-to-tower face is always exact: coherence removes precisely
the spurious raw towers. -/
def behaviorTowerIso (Label : Type u) :
    behaviorFace Label ≅ towerFace Label :=
  (Functor.const Contextᵒᵖ).mapIso (Tower.streamEquiv Label).toIso

@[simp]
theorem behaviorTowerIso_hom (Label : Type u) :
    (behaviorTowerIso Label).hom = behaviorToTower Label :=
  rfl

/-- A compatible operational/behavioral isomorphism is stronger than merely
postulating some isomorphism between the carrier types: its forward map must
be the independently defined final unfolding. -/
structure ExactBehaviorWitness {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label) where
  isomorphism : stateFace coalgebra ≅ behaviorFace Label
  agrees : isomorphism.hom = stateToBehavior coalgebra

namespace ExactBehaviorWitness

variable {Label : Type u}
variable {coalgebra : Coalgebra.{u, u} Label}

theorem behaviorallyExact
    (witness : ExactBehaviorWitness coalgebra) :
    BehaviorallyExact coalgebra := by
  have componentAgreement :=
    congrArg (fun transformation => transformation.app here) witness.agrees
  constructor
  · intro left right sameBehavior
    apply (witness.isomorphism.app here).toEquiv.injective
    change witness.isomorphism.hom.app here left =
      witness.isomorphism.hom.app here right
    rw [componentAgreement]
    exact sameBehavior
  · intro behavior
    obtain ⟨state, represents⟩ :=
      (witness.isomorphism.app here).toEquiv.surjective behavior
    change coalgebra.Carrier at state
    change witness.isomorphism.hom.app here state = behavior at represents
    refine ⟨state, ?_⟩
    change (stateToBehavior coalgebra).app here state = behavior
    rw [← componentAgreement]
    exact represents

/-- A compatible operational/behavioral isomorphism and the canonical
behavior/tower equivalence yield an exact computational trinity. -/
def exactTrinity (witness : ExactBehaviorWitness coalgebra) :
    Exact.{0, 0, u} Context where
  program := stateFace coalgebra
  logic := behaviorFace Label
  space := towerFace Label
  programLogic := witness.isomorphism
  logicSpace := behaviorTowerIso Label

theorem exactTrinity_programLogic_agrees
    (witness : ExactBehaviorWitness coalgebra) :
    witness.exactTrinity.programLogic.hom = stateToBehavior coalgebra :=
  witness.agrees

end ExactBehaviorWitness

/-- A bijective unfolding constructs the compatible exact-behavior witness.
The inverse is selected from the supplied surjectivity proof. -/
noncomputable def exactBehaviorWitnessOfBehaviorallyExact
    {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label)
    (exact : BehaviorallyExact coalgebra) :
    ExactBehaviorWitness coalgebra where
  isomorphism :=
    (Functor.const Contextᵒᵖ).mapIso
      (Equiv.ofBijective (unfold coalgebra) exact).toIso
  agrees := rfl

/-- Exact operational/behavioral compatibility exists exactly when unfolding
is bijective. -/
theorem exactBehaviorWitness_nonempty_iff
    {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label) :
    Nonempty (ExactBehaviorWitness coalgebra) ↔
      BehaviorallyExact coalgebra := by
  constructor
  · rintro ⟨witness⟩
    exact witness.behaviorallyExact
  · intro exact
    exact ⟨exactBehaviorWitnessOfBehaviorallyExact coalgebra exact⟩

/-! ## Information loss is exactly behavioral collision -/

theorem comparison_loses_iff_behavior_collision
    {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label) :
    (comparison coalgebra).LosesProgramInformation ↔
      ∃ left right : coalgebra.Carrier,
        left ≠ right ∧ unfold coalgebra left = unfold coalgebra right := by
  constructor
  · rintro ⟨context, left, right, different, sameTower⟩
    refine ⟨left, right, different, ?_⟩
    apply Tower.ofStream_injective
    exact sameTower
  · rintro ⟨left, right, different, sameBehavior⟩
    refine ⟨here, left, right, different, ?_⟩
    exact congrArg Tower.ofStream sameBehavior

theorem faithful_not_loses
    {Label : Type u}
    (coalgebra : Coalgebra.{u, u} Label)
    (faithful : BehaviorallyFaithful coalgebra) :
    ¬ (comparison coalgebra).LosesProgramInformation := by
  rw [comparison_loses_iff_behavior_collision]
  rintro ⟨left, right, different, sameBehavior⟩
  exact different (faithful sameBehavior)

/-! ## Independence canaries -/

namespace Canary

/-- Only constant Boolean streams are represented. -/
def constantBoolCoalgebra : Coalgebra Bool where
  Carrier := Bool
  observe := _root_.id
  next := _root_.id

theorem unfold_constantBool (label : Bool) :
    unfold constantBoolCoalgebra label = constant label := by
  funext depth
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis => exact inductionHypothesis

theorem constantBool_faithful :
    BehaviorallyFaithful constantBoolCoalgebra := by
  intro left right sameBehavior
  have atZero := congrFun sameBehavior 0
  change left = right at atZero
  exact atZero

theorem constantBool_not_complete :
    ¬ BehaviorallyComplete constantBoolCoalgebra := by
  intro complete
  obtain ⟨label, represents⟩ :=
    complete (changedAt 0 false true)
  rw [unfold_constantBool] at represents
  have atZero := congrFun represents 0
  have atOne := congrFun represents 1
  cases label <;> simp [constant, changedAt] at atZero atOne

/-- Add an operational tag which final stream behavior deliberately ignores. -/
def taggedStreamCoalgebra : Coalgebra Bool where
  Carrier := Stream Bool × Bool
  observe := fun state => head state.1
  next := fun state => (tail state.1, state.2)

def taggedProjectionHom :
    Hom taggedStreamCoalgebra (streamCoalgebra Bool) where
  toFun := Prod.fst
  observe_preserved := by intro state; rfl
  next_preserved := by intro state; rfl

theorem unfold_taggedStream (state : taggedStreamCoalgebra.Carrier) :
    unfold taggedStreamCoalgebra state = state.1 := by
  have equality := congrFun
    (hom_to_stream_eq_unfold taggedStreamCoalgebra taggedProjectionHom) state
  exact equality.symm

theorem taggedStream_complete :
    BehaviorallyComplete taggedStreamCoalgebra := by
  intro stream
  exact ⟨(stream, false), unfold_taggedStream (stream, false)⟩

theorem taggedStream_not_faithful :
    ¬ BehaviorallyFaithful taggedStreamCoalgebra := by
  intro faithful
  have sameBehavior :
      unfold taggedStreamCoalgebra (constant false, false) =
        unfold taggedStreamCoalgebra (constant false, true) := by
    rw [unfold_taggedStream, unfold_taggedStream]
  have statesEqual := faithful sameBehavior
  have tagsEqual := congrArg Prod.snd statesEqual
  exact Bool.false_ne_true tagsEqual

theorem unfold_streamCoalgebra_eq_id (Label : Type u) :
    unfold (streamCoalgebra Label) = _root_.id := by
  exact
    (hom_to_stream_eq_unfold (streamCoalgebra Label)
      (Hom.id (streamCoalgebra Label))).symm

theorem streamCoalgebra_exact (Label : Type u) :
    BehaviorallyExact (streamCoalgebra Label) := by
  unfold BehaviorallyExact
  rw [unfold_streamCoalgebra_eq_id]
  exact Function.bijective_id

/-- Faithfulness and completeness are independent, while the final stream
coalgebra has both. -/
theorem faithfulness_completeness_independent :
    (BehaviorallyFaithful constantBoolCoalgebra ∧
      ¬ BehaviorallyComplete constantBoolCoalgebra) ∧
    (¬ BehaviorallyFaithful taggedStreamCoalgebra ∧
      BehaviorallyComplete taggedStreamCoalgebra) ∧
    BehaviorallyExact (streamCoalgebra Bool) :=
  ⟨⟨constantBool_faithful, constantBool_not_complete⟩,
    ⟨taggedStream_not_faithful, taggedStream_complete⟩,
    streamCoalgebra_exact Bool⟩

/-- Absence of information loss is weaker than exact trinity: the constant
coalgebra is faithful but does not represent every Boolean stream. -/
theorem faithful_comparison_need_not_be_exact :
    ¬ (comparison constantBoolCoalgebra).LosesProgramInformation ∧
      ¬ BehaviorallyExact constantBoolCoalgebra := by
  refine ⟨faithful_not_loses constantBoolCoalgebra constantBool_faithful, ?_⟩
  intro exact
  exact constantBool_not_complete exact.2

end Canary

/-! ## Axiom audit -/

#print axioms behaviorallyExact_iff_faithful_and_complete
#print axioms behaviorTowerIso
#print axioms ExactBehaviorWitness.behaviorallyExact
#print axioms exactBehaviorWitness_nonempty_iff
#print axioms comparison_loses_iff_behavior_collision
#print axioms faithful_not_loses
#print axioms Canary.constantBool_faithful
#print axioms Canary.constantBool_not_complete
#print axioms Canary.taggedStream_complete
#print axioms Canary.taggedStream_not_faithful
#print axioms Canary.streamCoalgebra_exact
#print axioms Canary.faithfulness_completeness_independent
#print axioms Canary.faithful_comparison_need_not_be_exact

end Mettapedia.Coalgebra.ComputationalTrinity
