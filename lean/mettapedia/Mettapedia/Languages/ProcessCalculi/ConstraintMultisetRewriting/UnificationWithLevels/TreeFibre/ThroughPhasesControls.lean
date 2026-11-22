import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughPhases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughReadControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedObstructionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlaceControls

/-!
# Controls: deciding in phases, in the tree's tower

**With the solver mixing Miller patterns and arrow codes as the base decision** (`towerPhases`):
* the store that meets a declaration mentioning a solved unknown (`metStore`: `X ≐ Π (_ : U0). U0`, `y ≐ y'` over
  `X : U1, y : X, y' : X`), which the reader of later declarations does not read, is decided in two phases
  (`met_phases`, not in one: `met_phases_one`): `X ≐ Π (_ : U0). U0` over `X : U1` first, lifted past `y` and `y'`;
  then `y ≐ y'`, now over `y y' : Π (_ : U0). U0`, in η-long form, a Miller equation (`met_second_phase`). It is
  settled (`met_settles`) and, being solvable, has a principal answer (`met_principal`);
* the dd store is decided in one phase (`dd_phases`), the store that needs reordering through an exchange
  (`re_phases`);
* `y ≐ y'` alone, `X` unsolved, is decided neither in phases nor by the reader (`metFlex_pieces`): `y : X` never
  becomes a universe family. The tree's in-place solver, which works over any telescope, decides it
  (`metFlex_inPlace`).

**With the three solvers tried in turn as the base** (`towerAll`: the mixed solver, the mixed join solver, the in-place
solver), the phases make them cooperate: `coopStore` (the spare store's glb-join equation and `w ≐ w'` over
`w w' : Z`) is decided by none of them alone (`coop_alone`) and in two phases by all of them (`coop_phases`,
`coop_principal`): the glb-join equation over the older telescope by the mixed join solver, then `w ≐ w'` by the
in-place solver. The store mixing a Miller permutation with a glb-join equation, where the tree's one-rank solvers stop
(`MixedObstructionControls`), is decided by the in-place solver (`mj_inPlace`, `mj_principal`).
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

/-- Which way a decision went: `1` a finished update, `2` a refutation, `0` none. -/
def decidedKind {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} : Option (Decided problem) → Nat
  | some (.solved _ _) => 1
  | some (.refuted _) => 2
  | none => 0

/-- A decision that went to a finished update gives a principal answer. -/
theorem principal_of_decided {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {found : Option (Decided problem)} (solved : decidedKind found = 1) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), (frames setting.levels).Principal problem answer := by
  rcases found with _ | ⟨update, finished⟩ | absent
  · simp [decidedKind] at solved
  · exact ⟨update.target, update.answer, update.completed finished⟩
  · simp [decidedKind] at solved

/-! ## The mixed solver as the base -/

/-- **Deciding in phases in the tower**, from runs of the mixed solver. -/
abbrev towerPhases (fuel depth : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  phases (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun problem => Decided.ofRun towerMixedSolver 8 problem)
    fuel depth problem

/-- **The met store is decided in two phases.** -/
theorem met_phases : (towerPhases 6 2 metStore).isSome = true := by decide +kernel

theorem met_phases_one : (towerPhases 6 1 metStore).isSome = false := by decide +kernel

theorem met_settles : Settles metStore :=
  phases_settles (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun problem => Decided.ofRun towerMixedSolver 8 problem) met_phases

/-- **A principal answer.** -/
theorem met_principal : ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxMet),
    (frames setting.levels).Principal metStore answer := by
  rcases met_settles.principal_or_unsolvable with found | absent
  · exact found
  · exact absurd met_solvable absent

/-- **The second phase is a Miller store**: `y ≐ y'` over the instantiated telescope `y y' : Π (_ : U0). U0`, in
η-long form, read by the mixed reader. -/
theorem met_second_phase : inMixedB ExecutableTowerChoices.choices
    (ContextualDependentEtaDepth.expandStore TowerModel.facts
      ((frames setting.levels).applyStore metAnswer [metFlex])) = true := by decide +kernel

/-- **The dd store is decided in one phase.** -/
theorem dd_phases : (towerPhases 6 1 ddStore).isSome = true := by decide +kernel

/-- **The store that needs reordering is decided through an exchange.** -/
theorem re_phases : decidedKind (towerPhases 6 2 reStore) = 1 := by decide +kernel

/-- **`y ≐ y'` alone, `X` unsolved, is decided neither in phases nor by the reader**, over the tree's level pieces. -/
theorem metFlex_pieces : (towerPhases 6 3 [metFlex]).isSome = false ∧ (towerRead 6 3 [metFlex]).isSome = false := by
  decide +kernel

/-- **The tree's in-place solver decides it**: it works over any telescope. -/
theorem metFlex_inPlace : decidedKind (Decided.ofRun ContextualDependentInPlace.Controls.inPlaceOnly 8 [metFlex]) = 1 := by
  decide +kernel

/-! ## Three solvers as the base -/

/-- The mixed solver, the mixed join solver and the in-place solver, tried in turn. -/
def towerBase {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Option (Decided problem) :=
  (Decided.ofRun towerMixedSolver 8 problem).orElse fun _ =>
    (Decided.ofRun towerMixedJoinSolver 8 problem).orElse fun _ =>
      Decided.ofRun ContextualDependentInPlace.Controls.inPlaceOnly 8 problem

/-- **Deciding in phases from the three solvers.** -/
abbrev towerAll (fuel depth : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  phases (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer towerBase fuel depth problem

def coopW : TypeOver ctxSJ := formIn ctxSJ (.var 0) (by decide +kernel)
abbrev ctxCoop1 := extend ctxSJ coopW
def coopW' : TypeOver ctxCoop1 := formIn ctxCoop1 (.var 1) (by decide +kernel)
/-- `X : U0 → U0, Y : U2 → U1, Z : U1, w : Z, w' : Z`. -/
abbrev ctxCoop := extend ctxCoop1 coopW'
def coopFamType : TypeOver ctxCoop := formIn ctxCoop (.pi (.head U0) (.head U1)) (by decide +kernel)
def coopZType : TypeOver ctxCoop := formIn ctxCoop (.var 2) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U1`: the spare store's glb-join equation. -/
def coopFlex : Equation (TotalTerm ctxCoop) :=
  (termIn ctxCoop coopFamType (.lam (.app (.var 5) (.var 0))) (by decide +kernel),
    termIn ctxCoop coopFamType (.lam (.app (.var 4) (.var 0))) (by decide +kernel))

/-- `w ≐ w'` at `Z`. -/
def coopPoint : Equation (TotalTerm ctxCoop) :=
  (termIn ctxCoop coopZType (.var 1) (by decide +kernel), termIn ctxCoop coopZType (.var 0) (by decide +kernel))

def coopStore : EquationStore (TotalTerm ctxCoop) := [coopFlex, coopPoint]

/-- **None of the three solvers decides it alone.** -/
theorem coop_alone : decidedKind (Decided.ofRun towerMixedSolver 8 coopStore) = 0 ∧
    decidedKind (Decided.ofRun towerMixedJoinSolver 8 coopStore) = 0 ∧
    decidedKind (Decided.ofRun ContextualDependentInPlace.Controls.inPlaceOnly 8 coopStore) = 0 := by decide +kernel

/-- **Two phases decide it**: the glb-join equation over the older telescope, then `w ≐ w'`. -/
theorem coop_phases : decidedKind (towerAll 6 2 coopStore) = 1 := by decide +kernel
theorem coop_phases_one : decidedKind (towerAll 6 1 coopStore) = 0 := by decide +kernel

theorem coop_principal : ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxCoop),
    (frames setting.levels).Principal coopStore answer := principal_of_decided coop_phases

/-- **The store mixing a Miller permutation with a glb-join equation is decided by the in-place solver.** -/
theorem mj_inPlace : decidedKind (Decided.ofRun ContextualDependentInPlace.Controls.inPlaceOnly 8 mjStore) = 1 := by
  decide +kernel

theorem mj_principal : ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxMJ),
    (frames setting.levels).Principal mjStore answer := principal_of_decided mj_inPlace

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
