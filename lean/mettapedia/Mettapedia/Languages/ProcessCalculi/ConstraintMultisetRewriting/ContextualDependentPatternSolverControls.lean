import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolverPrune
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklistControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRecognitionControls

/-!
# The full solver on concrete stores

Every run below executes the actual full solver (pattern rule with the occurs check, prune rule,
exchange rule, then the qualified worklist round) inside the actual driver, in the cumulative tower, evaluated by the kernel.

* **Crossed arguments.** Over `T : U0, F : (a b : T) → U0`, the store `λ x y. F y x ≐ λ x y. Id T x y`
  is solved by the pattern rule with a principal answer. Its left side is not an eta-expansion of
  `F`, so the worklist round alone is stuck on it.
* **An out-of-image refutation.** `λ x y. F x ≐ λ x y. y` is refuted with a certificate;
  `λ x y. F x ≐ λ x y. x` is solved.
* **Pruning inside the solver.** For `G y z ≐ F x y` the prune rule prunes `G` to `{y}`, exchanges,
  and solves `F`; the run commits with a principal answer. Without the prune rule, and with the
  worklist round alone, the same store is stuck.
* **A non-pattern.** `F x x ≐ Id T y x` stays suspended; it is never refuted.
* **Decisiveness on multi-equation stores.** Two consistent pattern equations are decided with a
  principal answer, and a refutable equation beside a solvable one is decided with a refutation;
  in both cases the fragment theorem gives the same outcome at every larger budget.
* **Wake-up around a prune.** The heterogeneous `λ x y z. refl (G y z) ≐ λ x y z. refl (F x y)`
  is suspended alone; beside the flex-flex equation it waits, the prune rule solves `G` and `F`,
  and the woken equation is discharged by conversion. The run commits with a principal answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternSolver.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiShape ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentReductionReflection TypedEquality.StrongNormalization
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls ContextualDependentWorklist

/-- The actual full solver in the cumulative tower. -/
def full : Solver setting.levels :=
  fullSolver (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique 16

/-- The qualified worklist step alone. -/
def worklistOnly : Solver setting.levels :=
  ContextualDependentWorklist.solver (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16

/-- Close a scoped equation into a store equation with the executable universe joins. -/
def closeStore {Θ : Context Tower.rules} (constraint : Scoped Θ) : EquationStore (TotalTerm Θ) :=
  match constraint.closeWith setting.levels ExecutableTowerChoices.choices with
  | some active => [active.equation]
  | none => []

theorem closeStore_models {Θ Δ : Context Tower.rules} (constraint : Scoped Θ) (solution : Δ ⟶ Θ)
    (closed : ∃ active, constraint.closeWith setting.levels ExecutableTowerChoices.choices = some active) :
    (frames setting.levels).Models solution (closeStore constraint) ↔ constraint.Holds solution := by
  obtain ⟨active, computed⟩ := closed
  unfold closeStore
  rw [computed]
  exact (Active.holds_iff_models setting.levels active solution).symm.trans
    (Scoped.closeWith_holds_iff setting.levels ExecutableTowerChoices.choices constraint computed solution)

/-! ## Crossed arguments -/

/-- `F y x` under `x y : T`. -/
def crossed : Pattern spine scope where
  args := fun position => match position with
    | .inl _ => .inr (.inl ())
    | .inr (.inl _) => .inl ()
    | .inr (.inr impossible) => impossible.elim
  injective := by
    intro one two same
    rcases one with ⟨⟩ | ⟨⟩ | impossible <;> rcases two with ⟨⟩ | ⟨⟩ | other
    all_goals first | rfl | cases same | exact impossible.elim | exact other.elim
  compatible := by unfold CtxRen; decide +kernel

/-- `Id T x y` in `T, F, x, y`. -/
def ordered : Term scope.target ((lifted spine).result.reindex crossed.map.hom) :=
  ⟨(.id (.var 3) (.var 1) (.var 0) : Tower.Tm 4), .idForm (.var (3 : Fin 4)) (.sort _) (.var (1 : Fin 4)) (.var (0 : Fin 4))⟩

def crossedStore : EquationStore (TotalTerm (extend types outerWhole)) := closeStore (crossed.constraint ordered)

theorem crossed_store_length : crossedStore.length = 1 := by decide +kernel

theorem crossed_solved : (run full crossedStore 2).readout = .commit := by decide +kernel

theorem crossed_worklist_stuck : (run worklistOnly crossedStore 4).readout = .suspended := by decide +kernel

theorem crossed_principal :
    ∃ state finished, run full crossedStore 2 = .solved state finished ∧
      (frames setting.levels).Principal crossedStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit crossed_solved
  exact ⟨state, finished, solved, drive_solved_principal full solved⟩

/-! ## A certified refutation: `F x ≐ y` -/

open DispatchControls in
def outsideStore := closeStore (Outside.first.constraint Outside.outsideVariable)

open DispatchControls in
def insideStore := closeStore (Outside.first.constraint Outside.insideVariable)

theorem outside_refuted : (run full outsideStore 1).readout = .refuted := by decide +kernel

theorem inside_solved : (run full insideStore 2).readout = .commit := by decide +kernel

/-! ## Pruning inside the solver: `G y z ≐ F x y` -/

def flexFlexStore := closeStore ContextualDependentPrune.Controls.flexFlex

/-- The prune rule prunes `G` to `{y}`, exchanges `F` and `H`, and solves `F`; the run commits. -/
theorem flexFlex_solved : (run full flexFlexStore 2).readout = .commit := by decide +kernel

theorem flexFlex_principal :
    ∃ state finished, run full flexFlexStore 2 = .solved state finished ∧
      (frames setting.levels).Principal flexFlexStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit flexFlex_solved
  exact ⟨state, finished, solved, drive_solved_principal full solved⟩

/-- Without pruning the same store is stuck: the pattern rule alone does not decide it. -/
def patternOnly : Solver setting.levels :=
  solver (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal 16

theorem flexFlex_without_pruning_stuck : (run patternOnly flexFlexStore 4).readout = .suspended := by decide +kernel

theorem flexFlex_worklist_stuck : (run worklistOnly flexFlexStore 4).readout = .suspended := by decide +kernel

/-! ## A non-pattern stays residual -/

/-- `F x x ≐ Id T y x` is not a pattern; it is never refuted by the solver. -/
def repeatedStore := closeStore (scope.toScoped RecognitionControls.repeatedEquation)

theorem repeated_suspended : (run full repeatedStore 4).readout = .suspended := by decide +kernel

/-! ## Fragment completeness on multi-equation stores -/

def twoPatterns : EquationStore (TotalTerm (extend types outerWhole)) :=
  crossedStore ++ closeStore (straight.constraint swapped)

theorem twoPatterns_decided : decidesWithin full 3 _ twoPatterns = true := by decide +kernel

/-- **Decisiveness, solved case**: from some budget on, every run reaches the same principal
answer. -/
theorem twoPatterns_fragment :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run full twoPatterns larger = run full twoPatterns fuel ∧
      ((∃ state finished, run full twoPatterns larger = .solved state finished ∧
          (frames setting.levels).Principal twoPatterns state.answer) ∨
        (∃ absent, run full twoPatterns larger = .refuted absent)) :=
  (fullFragment (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique 16).decided
    (Reaches.of_decidesWithin full 3 _ twoPatterns twoPatterns_decided)

theorem twoPatterns_solved : (run full twoPatterns 4).readout = .commit := by decide +kernel

def outsideAndInside := outsideStore ++ insideStore

theorem outsideAndInside_decided : decidesWithin full 1 _ outsideAndInside = true := by decide +kernel

/-- **Decisiveness, refuted case.** -/
theorem outsideAndInside_fragment :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run full outsideAndInside larger = run full outsideAndInside fuel ∧
      ((∃ state finished, run full outsideAndInside larger = .solved state finished ∧
          (frames setting.levels).Principal outsideAndInside state.answer) ∨
        (∃ absent, run full outsideAndInside larger = .refuted absent)) :=
  (fullFragment (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique 16).decided
    (Reaches.of_decidesWithin full 1 _ outsideAndInside outsideAndInside_decided)

theorem outsideAndInside_refuted : (run full outsideAndInside 1).readout = .refuted := by decide +kernel

/-! ## Postponement and wake-up around a prune -/

section Twins

open ContextualDependentPrune.Controls

def newerValue : Term localScope.target (universeAt localScope.target) :=
  ⟨newerPattern.application.code, newerPattern.application.typed⟩

def olderValue : Term localScope.target (universeAt localScope.target) :=
  ⟨olderApplication.term.code, olderApplication.term.typed⟩

/-- `Id U0 v v` under `x y z : T`. -/
def identityOf (value : Term localScope.target (universeAt localScope.target)) : TypeOver localScope.target :=
  ⟨.id (.head (.sort Tower.zero)) value.code value.code, .sort (.succ Tower.zero), .sort _,
    .idForm (.headType (.sort _)) (.sort _) value.typed value.typed⟩

def reflOf (value : Term localScope.target (universeAt localScope.target)) : Term localScope.target (identityOf value) :=
  ⟨.refl value.code, .reflIntro value.typed⟩

/-- `λ x y z. refl v` at `Π x y z. Id U0 v v`, closed with the executable universe joins. -/
def closedRefl (value : Term localScope.target (universeAt localScope.target)) : Option (Active metas) :=
  (localScope.toScoped ⟨identityOf value, reflOf value, reflOf value⟩).closeWith setting.levels
    ExecutableTowerChoices.choices

/-- **A heterogeneous equation**: `λ x y z. refl (G y z) ≐ λ x y z. refl (F x y)`, whose two
annotations agree only once `G` and `F` are solved. -/
def twinEquation : EquationStore (TotalTerm metas) :=
  match closedRefl newerValue, closedRefl olderValue with
  | some left, some right => [(⟨left.type, left.left⟩, ⟨right.type, right.left⟩)]
  | _, _ => []

def twinStore : EquationStore (TotalTerm metas) := twinEquation ++ flexFlexStore

theorem twin_store_length : twinStore.length = 2 := by decide +kernel

/-- Alone, the heterogeneous equation waits: it is suspended, not refuted. -/
theorem twin_alone_suspended : (run full twinEquation 4).readout = .suspended := by decide +kernel

/-- With the flex-flex equation, the prune rule solves `G` and `F`; the postponed equation then
wakes with agreeing types and is discharged. The run commits. -/
theorem twin_then_solved : (run full twinStore 3).readout = .commit := by decide +kernel

theorem twin_principal :
    ∃ state finished, run full twinStore 3 = .solved state finished ∧
      (frames setting.levels).Principal twinStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit twin_then_solved
  exact ⟨state, finished, solved, drive_solved_principal full solved⟩

end Twins

end ContextualDependentPatternSolver.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
