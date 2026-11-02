import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardedProcessCounterexamples

/-!
# Distinct guard causes and the prohibition on retroactive binding

Two distinct indexed tells state the same equation. Either can justify a
later ask, but the common final solution cannot justify asking before both.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutBindingControls

open Mettapedia.Logic.LP
open LinearConnectionLayout
open GuardedProcessCounterexamples (sig A X a b emptyWorld)

def tellZero : Event (Term sig) Nat := (⟨[], [], [(X, a)], [], []⟩, ⟨[], [], []⟩)
def askZero : Event (Term sig) Nat := (⟨[], [], [], [.equal X a], []⟩, ⟨[], [], []⟩)

def events : Fin 3 → Event (Term sig) Nat
  | 0 => tellZero
  | 1 => tellZero
  | 2 => askZero

def label : Nat → Term sig := fun _ => a
def leftCuts : Fin 3 → Finset (Fin 3) := fun i => if i = 2 then {0} else ∅
def rightCuts : Fin 3 → Finset (Fin 3) := fun i => if i = 2 then {1} else ∅
def noCuts : Fin 3 → Finset (Fin 3) := fun _ => ∅

theorem conditions : GuardCutSequentialization.Conditions A (Subst.single 0 a) label emptyWorld events := by
  refine ⟨?_, by decide +kernel, by decide +kernel, ?_, ?_, ?_, A.models_nil _, ?_⟩
  · intro event
    fin_cases event <;> simp [events, tellZero, askZero, ShapeTest.Holds, ShapeTest.ofSelection]
  · simp [LinearConnectionLayout.made, UnorderedOccurrenceConnections.roster, emptyWorld,
      events, tellZero, askZero, List.finRange_succ]
  · intro event occurrence port
    fin_cases event <;> simp [events, tellZero, askZero] at port
  · intro event
    fin_cases event <;> simp [events, tellZero, askZero]
  · intro event equation member
    fin_cases event <;>
      simp [ConditionalComposite.addedEquations, Selection.equations, events, tellZero, askZero] at member
    all_goals
      obtain rfl := member
      change (Subst.single 0 a : Subst sig) 0 = a
      exact Subst.single_eq (σ := sig) 0 a

theorem left_computed : GuardCutOrders.order? events leftCuts = some [0, 2, 1] := by decide +kernel
theorem right_computed : GuardCutOrders.order? events rightCuts = some [1, 2, 0] := by decide +kernel

theorem left_asks : GuardedCutSemantics.Asks A label emptyWorld events leftCuts := by
  intro current check member assignment solved
  fin_cases current
  · simp [events, tellZero] at member
  · simp [events, tellZero] at member
  · have same : check = .equal X a := by simpa [events, askZero] using member
    subst check
    have prefixSolved := (A.models_append ..).mp solved |>.1
    have cause := ((GuardedCutSemantics.models_cutStore A assignment label emptyWorld events (leftCuts 2)).mp
      prefixSolved).2 0 (by decide +kernel)
    exact cause (X, a) (by simp [events, tellZero, ConditionalComposite.addedEquations, Selection.equations])

theorem right_asks : GuardedCutSemantics.Asks A label emptyWorld events rightCuts := by
  intro current check member assignment solved
  fin_cases current
  · simp [events, tellZero] at member
  · simp [events, tellZero] at member
  · have same : check = .equal X a := by simpa [events, askZero] using member
    subst check
    have prefixSolved := (A.models_append ..).mp solved |>.1
    have cause := ((GuardedCutSemantics.models_cutStore A assignment label emptyWorld events (rightCuts 2)).mp
      prefixSolved).2 1 (by decide +kernel)
    exact cause (X, a) (by simp [events, tellZero, ConditionalComposite.addedEquations, Selection.equations])

theorem either_tell_can_justify_the_ask :
    ConditionalSchedule.Executable A label emptyWorld ([0, 2, 1].map events) ∧
      ConditionalSchedule.Executable A label emptyWorld ([1, 2, 0].map events) :=
  ⟨(conditions.computed_order_executes leftCuts left_computed left_asks).1,
    (conditions.computed_order_executes rightCuts right_computed right_asks).1⟩

theorem premature_ask_refused :
    ¬ ConditionalSchedule.Executable A label emptyWorld ([2, 0, 1].map events) := by
  rintro ⟨valid, _⟩
  have solved : A.Models (Subst.single 0 b) ((events 2).2.problem label (events 2).1 emptyWorld) :=
    A.models_nil _
  have equal := valid.checks (.equal X a) (by simp [events, askZero]) (Subst.single 0 b) solved
  have impossible : b = a := by simpa only [Check.Holds, SubstitutionAction.Solves,
      FirstOrder.action, X, a, Subst.applyTerm, Subst.single_eq] using equal
  exact GuardedProcessCounterexamples.a_ne_b impossible.symm

theorem one_final_model_does_not_justify_an_earlier_ask :
    A.Models (Subst.single 0 a)
      (ConditionalSchedule.follow label emptyWorld ([2, 0, 1].map events)).equations ∧
      ¬ ConditionalSchedule.Executable A label emptyWorld ([2, 0, 1].map events) := by
  refine ⟨(models_follow_iff A (Subst.single 0 a) label _ emptyWorld).mpr ⟨conditions.incoming, ?_⟩,
    premature_ask_refused⟩
  intro event member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact conditions.connections index

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutBindingControls
