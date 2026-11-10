import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.GSOSProfile
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSFinalBialgebraControls

/-! # Compositional behaviour of the admitted transform profile

The coalgebra is built from admitted transform events. Its equality with the
independent GSOS coalgebra is derived from operational correspondence. This
allows the existing final-bialgebra action and context-congruence theorem to
apply to this profile. Two independently distinguishable futures survive.

The observation records finite sets of successors per action. It deliberately
forgets candidate multiplicity; the free event category retains that data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GSOSProfile

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.FiniteBranching
open GSOSControls (signature actions naturals stopped choose law)
open IndexedPolynomial
open Classical

theorem admitted_target_supported {source target : Term}
    (event : effect.Event permission source target) :
    target ∈ ({GSOSControls.pure (1 : Nat), GSOSControls.pure (3 : Nat), GSOSControls.pure (4 : Nat)} : Finset Term) := by
  obtain ⟨leaf, _, allowed⟩ := event.permitted
  have target_eq : GSOSControls.pure event.firing.output = target := event.target_eq
  rw [← target_eq]
  rcases allowed with ⟨_, _, same⟩ | ⟨_, _, same⟩ | ⟨_, _, same⟩ <;> simp [same]

/-- A finite readout of actual admitted events, with no call to the GSOS evaluator. -/
def observedSuccessors (source : Term) (action : Nat) : Finset Term :=
  ({GSOSControls.pure (1 : Nat), GSOSControls.pure (3 : Nat), GSOSControls.pure (4 : Nat)} : Finset Term).filter
    (fun target => ∃ event : effect.Event permission source target, event.firing.action = action)

theorem observed_successors_eq (source : Term) (action : Nat) :
    observedSuccessors source action = successors source action := by
  ext target
  simp only [observedSuccessors, Finset.mem_filter]
  constructor
  · exact fun ⟨_, event⟩ => (event_iff_successor source target action).mp event
  · intro member
    obtain ⟨event, action_eq⟩ := (event_iff_successor source target action).mpr member
    exact ⟨admitted_target_supported event, event, action_eq⟩

def coalgebra : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := operational.V
  str base sort := match base, sort with
    | PUnit.unit, () => ↾observedSuccessors

theorem coalgebra_transitions_eq : coalgebra.str = operational.str := by
  funext base sort
  cases base
  cases sort
  apply ConcreteCategory.hom_ext
  intro term
  funext action
  exact observed_successors_eq term action

theorem coalgebra_eq_operational : coalgebra = operational := by
  change Endofunctor.Coalgebra.mk operational.V coalgebra.str =
    Endofunctor.Coalgebra.mk operational.V operational.str
  rw [coalgebra_transitions_eq]

def observe (term : Term) : FiniteActionTree.Tree Nat PUnit :=
  (FinalSemantics.observe signature actions coalgebra).f PUnit.unit () term

theorem observation_iff_bisimilar (first second : Term) : observe first = observe second ↔
    Bisimulation.Bisimilar coalgebra coalgebra PUnit.unit () first second :=
  FinalSemantics.kernel_iff_bisimilar signature actions coalgebra coalgebra PUnit.unit () first second

/-- Interpreting the leaf processes, then applying the final compatible
algebra, agrees with observing the actual transform-event coalgebra. -/
theorem compositional_observation (term : Term) :
    observe term = (FinalBialgebra.finalAlgebra law).a.f PUnit.unit ()
      ((signature.termMonad.map (FinalSemantics.observe signature actions leaves).f)
        PUnit.unit () term) := by
  unfold observe
  change (FinalSemantics.observe signature actions
    (Endofunctor.Coalgebra.mk operational.V coalgebra.str)).f PUnit.unit () term = _
  rw [coalgebra_transitions_eq]
  exact (congrArg (fun mapping => mapping PUnit.unit () term)
    (FinalBialgebra.operational_observation law leaves)).symm

/-- All contexts of this first-order GSOS signature preserve the behavioural
equivalence of the admitted transform profile. -/
theorem context_preserves_bisimilarity
    (context : signature.polynomial.Free
      (Bisimulation.ContextPairs (lawEquiv signature actions law) leaves) PUnit.unit ()) :
    Bisimulation.Bisimilar coalgebra coalgebra PUnit.unit ()
      (Free.bind signature.polynomial (fun _ _ pair => pair.val.1) PUnit.unit () context)
      (Free.bind signature.polynomial (fun _ _ pair => pair.val.2) PUnit.unit () context) := by
  change Bisimulation.Bisimilar (Endofunctor.Coalgebra.mk operational.V coalgebra.str)
    (Endofunctor.Coalgebra.mk operational.V coalgebra.str) PUnit.unit () _ _
  rw [coalgebra_transitions_eq]
  exact Bisimulation.context_related (lawEquiv signature actions law) leaves PUnit.unit () context

def fork : Term := choose (GSOSControls.pure (0 : Nat)) (GSOSControls.pure (2 : Nat))

theorem two_transform_futures : observedSuccessors fork 7 =
    {GSOSControls.pure (1 : Nat), GSOSControls.pure (3 : Nat)} := by
  simp [observed_successors_eq, fork, successors_choose, successors_pure,
    leafSuccessors, FinitePowerset.map]

theorem left_future_enabled : observedSuccessors (GSOSControls.pure (1 : Nat)) 9 =
    {GSOSControls.pure (4 : Nat)} := by
  simp [observed_successors_eq, successors_pure, leafSuccessors, FinitePowerset.map]

theorem right_future_stopped : observedSuccessors (GSOSControls.pure (3 : Nat)) 9 = ∅ := by
  simp [observed_successors_eq, successors_pure, leafSuccessors, FinitePowerset.map]

theorem futures_not_bisimilar : ¬ Bisimulation.Bisimilar coalgebra coalgebra PUnit.unit ()
    (GSOSControls.pure (1 : Nat)) (GSOSControls.pure (3 : Nat)) := by
  intro related
  have unavailable := (Bisimulation.bisimilar_availability
    (left := coalgebra) (right := coalgebra) PUnit.unit () related 9).2 right_future_stopped
  change observedSuccessors (GSOSControls.pure (1 : Nat)) 9 = ∅ at unavailable
  rw [left_future_enabled] at unavailable
  exact Finset.singleton_ne_empty _ unavailable

theorem future_observations_differ : observe (GSOSControls.pure (1 : Nat)) ≠ observe (GSOSControls.pure (3 : Nat)) :=
  fun same => futures_not_bisimilar ((observation_iff_bisimilar _ _).mp same)

theorem final_readout_retains_both :
    FiniteActionTree.Tree.step (observe fork) 7 =
      {observe (GSOSControls.pure (1 : Nat)), observe (GSOSControls.pure (3 : Nat))} := by
  unfold observe
  rw [FinalSemantics.observe_step]
  change FinitePowerset.map _ (observedSuccessors fork 7) = _
  rw [two_transform_futures]
  simp [FinitePowerset.map]

theorem final_successor_count : (FiniteActionTree.Tree.step (observe fork) 7).card = 2 := by
  rw [final_readout_retains_both]
  simp [future_observations_differ]

/-- Removing one future changes the complete final observation. -/
theorem omitting_a_future_fails : FiniteActionTree.Tree.step (observe fork) 7 ≠
    {observe (GSOSControls.pure (3 : Nat))} := by
  rw [final_readout_retains_both]
  intro same
  have member : observe (GSOSControls.pure (1 : Nat)) ∈
      ({observe (GSOSControls.pure (3 : Nat))} : Finset _) := same ▸ (by simp)
  exact future_observations_differ (Finset.mem_singleton.mp member)

def forged : Candidate := ⟨[false], 7, 99⟩

theorem forged_prepared : effect.Prepares (s := fork) forged :=
  candidate_prepares forged ⟨0, rfl⟩

theorem forged_refused : ¬ step.Admits (s := fork) forged := by
  rintro ⟨_, leaf, found, allowed⟩
  have source_eq : leaf = 0 := (Option.some.inj found).symm
  subst leaf
  change LeafAllows 0 7 99 at allowed
  simp [LeafAllows] at allowed

theorem forged_still_refines : ∀ (solution : Bool → Bool),
    Presentation.Controls.frame.Models (a := ()) (b := ()) solution
      (effect.knowledge (effect.preparedResult (s := fork) forged forged_prepared)) →
    Presentation.Controls.frame.Models (a := ()) (b := ())
      (Presentation.Controls.frame.comp (a := ()) (b := ()) (c := ()) solution (effect.along forged forged_prepared))
      (effect.knowledge fork) := effect.models_along forged forged_prepared

def repeated : Term := choose (GSOSControls.pure (0 : Nat)) (GSOSControls.pure (0 : Nat))

def leftEvent : effect.Event permission repeated (GSOSControls.pure (1 : Nat)) where
  firing := ⟨[false], 7, 1⟩
  prepared := candidate_prepares _ ⟨0, rfl⟩
  permitted := ⟨0, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  target_eq := rfl

def rightEvent : effect.Event permission repeated (GSOSControls.pure (1 : Nat)) where
  firing := ⟨[true], 7, 1⟩
  prepared := candidate_prepares _ ⟨0, rfl⟩
  permitted := ⟨0, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  target_eq := rfl

theorem repeated_events_distinct : leftEvent ≠ rightEvent := by
  intro same
  have paths := congrArg (fun event => event.firing.path) same
  change [false] = [true] at paths
  cases List.cons.inj paths |>.1

theorem set_observation_forgets_multiplicity :
    leftEvent ≠ rightEvent ∧ observedSuccessors repeated 7 = {GSOSControls.pure (1 : Nat)} := by
  refine ⟨repeated_events_distinct, ?_⟩
  simp [observed_successors_eq, repeated, successors_choose, successors_pure,
    leafSuccessors, FinitePowerset.map]

/-- The independently defined syntactic-equality test cannot be added under
the same GSOS congruence guarantee: no law presents its closed transitions. -/
theorem syntactic_inspection_requires_another_contract :
    ¬ ∃ inspectionLaw : Law FinalBialgebra.EqualityTestControl.signature
        FinalBialgebra.EqualityTestControl.actions,
      ∀ term label, (FinalBialgebra.closedOperational inspectionLaw).str PUnit.unit () term label =
        FinalBialgebra.EqualityTestControl.step term :=
  FinalBialgebra.EqualityTestControl.no_law_presents_equalityTest

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GSOSProfile
