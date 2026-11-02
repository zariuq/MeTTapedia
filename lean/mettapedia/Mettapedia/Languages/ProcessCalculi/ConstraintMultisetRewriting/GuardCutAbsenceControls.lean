import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardedProcessCounterexamples

/-!
# An absence process needs two cut families, not one partial order

The checker may run before a physical token is made or after it is consumed,
but cannot run between those two events. Both valid orders are obtained from
the actual Kahn result and original all-future guard, not an assumed run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutAbsenceControls

open Mettapedia.Logic.LP
open LinearConnectionLayout
open GuardedProcessCounterexamples (sig A lab pTok qTok emptyWorld maker checker guarded makeFive)

def taker : Event (Term sig) Nat := (⟨[pTok], [], [], [], []⟩, ⟨[4], [], []⟩)

def events : Fin 3 → Event (Term sig) Nat
  | 0 => maker
  | 1 => taker
  | 2 => checker

def beforeCuts : Fin 3 → Finset (Fin 3) := fun _ => ∅
def afterCuts : Fin 3 → Finset (Fin 3) := fun i => if i = 2 then {0, 1} else ∅
def betweenCuts : Fin 3 → Finset (Fin 3) := fun i => if i = 2 then {0} else ∅

def beforeOrder : List (Fin 3) := [2, 0, 1]
def afterOrder : List (Fin 3) := [0, 1, 2]
def betweenOrder : List (Fin 3) := [0, 2, 1]

theorem conditions : GuardCutSequentialization.Conditions A (Subst.id sig) lab emptyWorld events := by
  refine ⟨?_, by decide +kernel, by decide +kernel, ?_, ?_, ?_, A.models_nil _, ?_⟩
  · intro event
    fin_cases event <;>
      simp [events, maker, taker, checker, guarded, makeFive, ShapeTest.Holds, ShapeTest.ofSelection, lab]
  · simp [LinearConnectionLayout.made, UnorderedOccurrenceConnections.roster, emptyWorld]
  · intro event occurrence port
    fin_cases event
    · simp [events, maker] at port
    · have same : occurrence = 4 := by simpa [events, taker] using port
      subst occurrence
      exact Or.inr ⟨0, by simp [events, maker]⟩
    · simp [events, checker, makeFive] at port
  · intro event
    fin_cases event <;> simp [events, maker, taker, checker, makeFive]
  · intro event equation member
    fin_cases event <;>
      simp [ConditionalComposite.addedEquations, Selection.equations, events, maker, taker, checker,
        guarded, makeFive] at member
    obtain rfl := member
    rfl

theorem before_computed : GuardCutOrders.order? events beforeCuts = some beforeOrder := by decide +kernel
theorem after_computed : GuardCutOrders.order? events afterCuts = some afterOrder := by decide +kernel
theorem between_computed : GuardCutOrders.order? events betweenCuts = some betweenOrder := by decide +kernel

theorem before_world_empty : GuardedCutSemantics.cutWorld emptyWorld events (beforeCuts 2) = ∅ := by
  ext occurrence
  simp [GuardedCutSemantics.mem_cutWorld, beforeCuts, emptyWorld]

theorem after_world_empty : GuardedCutSemantics.cutWorld emptyWorld events (afterCuts 2) = ∅ := by
  ext occurrence
  simp [GuardedCutSemantics.mem_cutWorld, afterCuts, emptyWorld, events, maker, taker]

theorem before_asks : GuardedCutSemantics.Asks A lab emptyWorld events beforeCuts := by
  intro current check member assignment _
  fin_cases current
  · simp [events, maker] at member
  · simp [events, taker] at member
  · have same : check = .absent pTok := by simpa [events, checker, guarded] using member
    subst check
    change Check.Holds A assignment lab (GuardedCutSemantics.cutWorld emptyWorld events (beforeCuts 2))
      (.absent pTok)
    rw [before_world_empty]
    intro occurrence present
    exact False.elim (Finset.notMem_empty occurrence present)

theorem after_asks : GuardedCutSemantics.Asks A lab emptyWorld events afterCuts := by
  intro current check member assignment _
  fin_cases current
  · simp [events, maker] at member
  · simp [events, taker] at member
  · have same : check = .absent pTok := by simpa [events, checker, guarded] using member
    subst check
    change Check.Holds A assignment lab (GuardedCutSemantics.cutWorld emptyWorld events (afterCuts 2))
      (.absent pTok)
    rw [after_world_empty]
    intro occurrence present
    exact False.elim (Finset.notMem_empty occurrence present)

theorem before_runs : ConditionalSchedule.Executable A lab emptyWorld (beforeOrder.map events) :=
  (conditions.computed_order_executes beforeCuts before_computed before_asks).1

theorem after_runs : ConditionalSchedule.Executable A lab emptyWorld (afterOrder.map events) :=
  (conditions.computed_order_executes afterCuts after_computed after_asks).1

theorem between_guard_refused : ¬ GuardedCutSemantics.Asks A lab emptyWorld events betweenCuts := by
  intro asks
  have prefixSolved : A.Models (Subst.id sig)
      (GuardedCutSemantics.cutStore emptyWorld lab events (betweenCuts 2)) :=
    (GuardedCutSemantics.models_cutStore A (Subst.id sig) lab emptyWorld events (betweenCuts 2)).mpr
      ⟨conditions.incoming, fun event _ => conditions.connections event⟩
  have holds := asks 2 (.absent pTok) (by simp [events, checker, guarded]) (Subst.id sig)
    ((A.models_append ..).mpr ⟨prefixSolved, conditions.connections 2⟩)
  have present : 4 ∈ GuardedCutSemantics.cutWorld emptyWorld events (betweenCuts 2) := by
    simp [GuardedCutSemantics.mem_cutWorld, betweenCuts, emptyWorld, events, maker]
  exact holds 4 present rfl

theorem between_does_not_run :
    ¬ ConditionalSchedule.Executable A lab emptyWorld (betweenOrder.map events) := by
  rintro ⟨_, valid, _⟩
  exact GuardedProcessCounterexamples.guarded_never_fires_beside_p _ (by decide +kernel) makeFive valid

theorem two_orders_force_the_middle (relation : Fin 3 → Fin 3 → Prop)
    (left : beforeOrder.Pairwise fun first second => ¬ relation second first)
    (right : afterOrder.Pairwise fun first second => ¬ relation second first) :
    betweenOrder.Pairwise fun first second => ¬ relation second first := by
  simp [beforeOrder, afterOrder, betweenOrder] at left right ⊢
  tauto

theorem no_single_dependency_relation :
    ¬ ∃ relation : Fin 3 → Fin 3 → Prop, ∀ order : List (Fin 3),
      order.Perm (List.finRange 3) →
      (ConditionalSchedule.Executable A lab emptyWorld (order.map events) ↔
        order.Pairwise fun first second => ¬ relation second first) := by
  rintro ⟨relation, exactOrders⟩
  have left := (exactOrders beforeOrder (by decide +kernel)).mp before_runs
  have right := (exactOrders afterOrder (by decide +kernel)).mp after_runs
  exact between_does_not_run ((exactOrders betweenOrder (by decide +kernel)).mpr
    (two_orders_force_the_middle relation left right))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutAbsenceControls
