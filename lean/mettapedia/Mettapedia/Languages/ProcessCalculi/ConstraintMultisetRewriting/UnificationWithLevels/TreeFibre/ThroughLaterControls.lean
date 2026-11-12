import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughLater
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrowsControls

/-!
# Controls: declarations that mention an unknown being solved, in the tree's tower

* **The dd store** (`X ≐ Π (_ : U0). U0` over `X : U1, y : X`), outside the pieces of arrow codes because `y : X` mentions
  `X`: it is the store over `X : U1` read past `y : X` (`dd_equivalent`), so it is decided through the later
  declaration (`dd_through`, `dd_settles`, `dd_settled_principal`). The run before the later declaration commits
  (`ddStore0_committed`), and its answer instantiates `y : X` to `y : Π (_ : U0). U0` (`dd_instantiated`).
* **A store that needs reordering**: `X ≐ Π (_ : Z). Z` over `X : U1, y : X, Z : U0`. The answer's value mentions `Z`,
  declared after `y : X`; no telescope keeping that order types `y : Π (_ : Z). Z`. Exchanging `y` and `Z` (`Z`
  depends on nothing) gives the store over `X : U1, Z : U0` read past `y`; so it is decided through an exchange and a
  later declaration (`re_through`, `re_settles`). It is solvable (`re_solvable`), so it has a principal answer
  (`re_principal`).
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

/-- One-equation stores with the same four codes are equivalent. -/
theorem equivalent_of_codes {Θ : Context setting.R} {first second : Equation (TotalTerm Θ)}
    (leftType : first.1.1.code = second.1.1.code) (leftTerm : first.1.2.code = second.1.2.code)
    (rightType : first.2.1.code = second.2.1.code) (rightTerm : first.2.2.code = second.2.2.code) :
    (frames setting.levels).Equivalent [first] [second] := by
  intro Δ σ
  have same := ContextualDependentInPlace.solves_of_codes σ leftType leftTerm rightType rightTerm
  constructor
  · intro solved e member
    obtain rfl := List.mem_singleton.mp member
    exact same.mp (solved first List.mem_cons_self)
  · intro solved e member
    obtain rfl := List.mem_singleton.mp member
    exact same.mpr (solved second List.mem_cons_self)

/-- **Settled through later declarations, in the tower.** -/
theorem towerThrough_settles {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : Through (InArrowsCod ExecutableTowerChoices.choices) problem) : Settles problem :=
  throughArrows_settles (S := setting) ExecutableTowerChoices.choices LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening
    (fun ha hb => LevelGlb.towerGlb_total ha hb) inside

/-! ## The dd store -/

def ddType1 : TypeOver ctxDd1 := formIn ctxDd1 (.head U1) (by decide +kernel)

/-- `X ≐ Π (_ : U0). U0` over `X : U1` alone. -/
def ddEquation0 : Equation (TotalTerm ctxDd1) :=
  (termIn ctxDd1 ddType1 (.var 0) (by decide +kernel),
    termIn ctxDd1 ddType1 (.pi (.head U0) (.head U0)) (by decide +kernel))

def ddStore0 : EquationStore (TotalTerm ctxDd1) := [ddEquation0]

theorem ddStore0_inside : InArrowsCod ExecutableTowerChoices.choices ddStore0 := inArrowsCod_of_B _ (by decide +kernel)

/-- **The dd store is the store over `X : U1` read past `y : X`.** -/
theorem dd_equivalent :
    (frames setting.levels).Equivalent ddStore ((frames setting.levels).applyStore (projectionHom ctxDd1 ddY) ddStore0) :=
  equivalent_of_codes (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem dd_through : Through (InArrowsCod ExecutableTowerChoices.choices) ddStore :=
  .equivalent dd_equivalent (.later ddY (.base ddStore0_inside))

/-- **The dd store is settled**, through its later declaration. -/
theorem dd_settles : Settles ddStore := towerThrough_settles dd_through

theorem dd_settled_principal :
    (∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxDd), (frames setting.levels).Principal ddStore answer) ∨
      ¬ (frames setting.levels).Solvable ddStore :=
  dd_settles.principal_or_unsolvable

/-- The run before the later declaration commits. -/
theorem ddStore0_committed : (run arrowCodTowerSolver ddStore0 2).readout = .commit := by decide +kernel

/-- Whether the solved run's answer instantiates `y : X` to `y : Π (_ : U0). U0`. -/
def ddInstantiated : Bool :=
  match run arrowCodTowerSolver ddStore0 2 with
  | .solved state _ => decide (Presentation.subst state.answer.substitution ddY.code = .pi (.head U0) (.head U0))
  | _ => false

/-- **The instantiated telescope**: lifted past `y : X`, the solved run's answer declares `y : Π (_ : U0). U0`
(`later_target`). -/
theorem dd_instantiated : ddInstantiated = true := by decide +kernel

/-! ## A store that needs reordering -/

def zType : TypeOver ctxDd1 := formIn ctxDd1 (.head U0) (by decide +kernel)

/-- `X : U1, y : X, Z : U0`. -/
abbrev ctxRe := ContextualDependentParameterExchange.context ddY zType

def reType : TypeOver ctxRe := formIn ctxRe (.head U1) (by decide +kernel)

/-- `X ≐ Π (_ : Z). Z` at `U1`. -/
def reEquation : Equation (TotalTerm ctxRe) :=
  (termIn ctxRe reType (.var 2) (by decide +kernel),
    termIn ctxRe reType (.pi (.var 0) (.var 1)) (by decide +kernel))

def reStore : EquationStore (TotalTerm ctxRe) := [reEquation]

/-- Outside the pieces of arrow codes: `y : X` mentions `X`. -/
theorem re_outside : inArrowsCodB ExecutableTowerChoices.choices reStore = false := by decide +kernel

/-- `X : U1, Z : U0`. -/
abbrev ctxXZ := extend ctxDd1 zType

def xzType : TypeOver ctxXZ := formIn ctxXZ (.head U1) (by decide +kernel)

/-- `X ≐ Π (_ : Z). Z` over `X : U1, Z : U0`. -/
def reEquation0 : Equation (TotalTerm ctxXZ) :=
  (termIn ctxXZ xzType (.var 1) (by decide +kernel),
    termIn ctxXZ xzType (.pi (.var 0) (.var 1)) (by decide +kernel))

def reStore0 : EquationStore (TotalTerm ctxXZ) := [reEquation0]

theorem reStore0_inside : InArrowsCod ExecutableTowerChoices.choices reStore0 := inArrowsCod_of_B _ (by decide +kernel)

/-- **After exchanging `y` and `Z`**, the store is the store over `X : U1, Z : U0` read past `y`. -/
theorem re_exchanged_equivalent :
    (frames setting.levels).Equivalent (ContextualDependentPrune.exchange setting.levels ddY zType reStore).remaining
      ((frames setting.levels).applyStore
        (projectionHom ctxXZ (ContextualDependentParameterExchange.second zType ddY)) reStore0) :=
  equivalent_of_codes (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem re_through : Through (InArrowsCod ExecutableTowerChoices.choices) reStore :=
  .exchange ddY zType (.equivalent re_exchanged_equivalent (.later _ (.base reStore0_inside)))

/-- **The store that needs reordering is settled**, through an exchange and a later declaration. -/
theorem re_settles : Settles reStore := towerThrough_settles re_through

def reFirst : empty setting.R ⟶ ctxDd1 :=
  Elimination.instantiate (empty setting.R)
    (termIn (empty setting.R) ddX (.pi (.head .legacyGround) (.head .legacyGround)) (by decide +kernel)).2

def reSecond : empty setting.R ⟶ extend ctxDd1 ddY :=
  pair reFirst (termIn (empty setting.R) (ddY.reindex reFirst) (.lam (.var 0)) (by decide +kernel)).2

/-- `X := Π (_ : G). G`, `y := λ x. x`, `Z := G`. -/
def reSolution : empty setting.R ⟶ ctxRe :=
  pair reSecond (termIn (empty setting.R) ((ContextualDependentParameterExchange.second ddY zType).reindex reSecond)
    (.head .legacyGround) (by decide +kernel)).2

theorem re_solvable : (frames setting.levels).Solvable reStore :=
  ⟨_, reSolution, models_by reSolution reEquation.1.2 reEquation.2.2 (by decide +kernel)⟩

/-- **A principal answer**, over the reordered, instantiated telescope. -/
theorem re_principal : ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxRe),
    (frames setting.levels).Principal reStore answer := by
  rcases re_settles.principal_or_unsolvable with found | absent
  · exact found
  · exact absurd re_solvable absent

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
