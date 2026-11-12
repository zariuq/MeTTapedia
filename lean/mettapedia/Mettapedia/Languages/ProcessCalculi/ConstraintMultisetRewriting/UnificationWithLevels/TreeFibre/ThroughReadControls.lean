import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughRead
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughLaterControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedJoinControls

/-!
# Controls: the reader of stores through later declarations, in the tree's tower

* The dd store is read with one step, stripping `y : X` (`dd_read`), and not without it (`dd_read_zero`); the store
  that needs reordering is read with two, exchanging `y` and `Z` and then stripping `y` (`re_read`), and not with one
  (`re_read_one`). The reader alone settles both (`dd_read_settles`, `re_read_settles`).
* **Where the reader stops: a store that meets a declaration whose type mentions an unknown.** Over
  `X : U1, y : X, y' : X`, the store `X ≐ Π (_ : U0). U0`, `y ≐ y'`: the second equation meets `y` and `y'`, so neither
  can be stripped, and no reader reads the store (`met_unread`), nor its second equation (`metFlex_unread`): `y : X` is
  no universe family, and the Miller pieces are built over telescopes of universe families. The arrow equation alone
  is read past both (`metArrow_read`). The store is solvable (`met_solvable`).
* **The common rank is not lowered by an answer that instantiates a declaration into a Π-type**: the arrow equation's
  answer `X := Π (_ : U0). U0`, lifted past `y` and `y'` (`metAnswer`, which solves it: `metAnswer_solves`), leaves
  `y ≐ y'` over `y y' : Π (_ : U0). U0`, a telescope of families again, but the occurrence weight rises from 3 to 4
  (`met_weight`, `met_after_weight`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-- The one solver's fragment in the tower, read by the mixed reader and the glb-join reader. -/
def towerOneWitness {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (PLift (InOne ExecutableTowerChoices.choices problem)) :=
  if mixed : inMixedB ExecutableTowerChoices.choices problem = true then
    some ⟨inOne_of_mixed _ (inMixed_of_B _ mixed)⟩
  else if joined : inGlbJoinFragmentKB problem = true then some ⟨.inr (.inl (inGlbJoinFragmentK_of_B joined))⟩
  else none

/-- **The reader in the tower**, over the one solver's fragment. -/
abbrev towerRead (fuel depth : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  throughRead (S := setting) (InOne ExecutableTowerChoices.choices) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer towerOneWitness fuel depth problem

/-- **The one solver's fragment is settled in the tower.** -/
theorem towerOne_settles {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InOne ExecutableTowerChoices.choices problem) : Settles problem :=
  one_settles (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes Miller.Controls.towerInh
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening towerJoin towerJoin_sound LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) (fun ha hb => LevelGlb.towerGlb_total ha hb) towerJoin_total inside

/-- **Every store the reader reads in the tower is settled.** -/
theorem towerRead_settles {fuel depth : Nat} {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (towerRead fuel depth problem).isSome = true) : Settles problem :=
  throughRead_settles (S := setting) (InOne ExecutableTowerChoices.choices) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer towerOneWitness
    (fun inside => towerOne_settles inside) found

/-! ## The dd store and the store that needs reordering -/

theorem dd_read : (towerRead 6 1 ddStore).isSome = true := by decide +kernel
theorem dd_read_zero : (towerRead 6 0 ddStore).isSome = false := by decide +kernel
theorem dd_read_settles : Settles ddStore := towerRead_settles dd_read

theorem re_read : (towerRead 6 2 reStore).isSome = true := by decide +kernel
theorem re_read_one : (towerRead 6 1 reStore).isSome = false := by decide +kernel
theorem re_read_settles : Settles reStore := towerRead_settles re_read

/-! ## Where the reader stops -/

def metY' : TypeOver ctxDd := formIn ctxDd (.var 1) (by decide +kernel)
/-- `X : U1, y : X, y' : X`. -/
abbrev ctxMet := extend ctxDd metY'
def metUType : TypeOver ctxMet := formIn ctxMet (.head U1) (by decide +kernel)
def metXType : TypeOver ctxMet := formIn ctxMet (.var 2) (by decide +kernel)

/-- `X ≐ Π (_ : U0). U0` at `U1`. -/
def metArrow : Equation (TotalTerm ctxMet) :=
  (termIn ctxMet metUType (.var 2) (by decide +kernel),
    termIn ctxMet metUType (.pi (.head U0) (.head U0)) (by decide +kernel))

/-- `y ≐ y'` at `X`. -/
def metFlex : Equation (TotalTerm ctxMet) :=
  (termIn ctxMet metXType (.var 1) (by decide +kernel), termIn ctxMet metXType (.var 0) (by decide +kernel))

def metStore : EquationStore (TotalTerm ctxMet) := [metArrow, metFlex]

/-- **Not read**, at any depth up to three. -/
theorem met_unread : (towerRead 6 3 metStore).isSome = false := by decide +kernel

/-- `y ≐ y'` alone is read by no piece: `y : X` is no universe family. -/
theorem metFlex_unread : (Miller.readEq (S := setting) metFlex).isSome = false ∧
    inMixedB ExecutableTowerChoices.choices [metFlex] = false ∧ (towerRead 6 3 [metFlex]).isSome = false := by
  decide +kernel

/-- The arrow equation alone is read past `y'` and `y`. -/
theorem metArrow_read : (towerRead 6 2 [metArrow]).isSome = true := by decide +kernel

def metFirst : empty setting.R ⟶ ctxDd1 :=
  Elimination.instantiate (empty setting.R)
    (termIn (empty setting.R) ddX (.pi (.head U0) (.head U0)) (by decide +kernel)).2

def metSecond : empty setting.R ⟶ ctxDd :=
  pair metFirst (termIn (empty setting.R) (ddY.reindex metFirst) (.lam (.var 0)) (by decide +kernel)).2

/-- `X := Π (_ : U0). U0`, `y := λ z. z`, `y' := λ z. z`. -/
def metSolution : empty setting.R ⟶ ctxMet :=
  pair metSecond (termIn (empty setting.R) (metY'.reindex metSecond) (.lam (.var 0)) (by decide +kernel)).2

/-- **Solvable.** -/
theorem met_solvable : (frames setting.levels).Solvable metStore := by
  refine ⟨_, metSolution, fun e member => ?_⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact models_by metSolution metArrow.1.2 metArrow.2.2 (by decide +kernel) _ List.mem_cons_self
  · rw [List.mem_singleton.mp member]
    exact models_by metSolution metFlex.1.2 metFlex.2.2 (by decide +kernel) _ List.mem_cons_self

/-! ## The occurrence weight rises when a declaration is instantiated into a Π-type -/

def afterType : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head U0) (.head U0)) (by decide +kernel)
abbrev ctxAfter1 := extend (empty setting.R) afterType
def afterType' : TypeOver ctxAfter1 := formIn ctxAfter1 (.pi (.head U0) (.head U0)) (by decide +kernel)
/-- `y y' : Π (_ : U0). U0`: the telescope instantiated by `X := Π (_ : U0). U0`. -/
abbrev ctxAfter := extend ctxAfter1 afterType'

def afterEmpty : ctxAfter ⟶ empty setting.R :=
  projectionHom ctxAfter1 afterType' ≫ projectionHom (empty setting.R) afterType

def afterX : ctxAfter ⟶ ctxDd1 :=
  pair afterEmpty (termIn ctxAfter (ddX.reindex afterEmpty) (.pi (.head U0) (.head U0)) (by decide +kernel)).2

def afterY : ctxAfter ⟶ ctxDd :=
  pair afterX (termIn ctxAfter (ddY.reindex afterX) (.var 1) (by decide +kernel)).2

/-- **The arrow equation's answer lifted past `y` and `y'`**: `X := Π (_ : U0). U0`, `y := y`, `y' := y'`. -/
def metAnswer : ctxAfter ⟶ ctxMet :=
  pair afterY (termIn ctxAfter (metY'.reindex afterY) (.var 0) (by decide +kernel)).2

theorem metAnswer_solves : (frames setting.levels).Models metAnswer [metArrow] :=
  models_by metAnswer metArrow.1.2 metArrow.2.2 (by decide +kernel)

/-- **The weight before the answer**: `X`, `y`, `y'` occur, each at arity zero. -/
theorem met_weight : Miller.weight (S := setting) metStore = 3 := by decide +kernel

/-- **The weight after it**: `y` and `y'` now have arity one. -/
theorem met_after_weight :
    Miller.weight (S := setting) ((frames setting.levels).applyStore metAnswer [metFlex]) = 4 := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
