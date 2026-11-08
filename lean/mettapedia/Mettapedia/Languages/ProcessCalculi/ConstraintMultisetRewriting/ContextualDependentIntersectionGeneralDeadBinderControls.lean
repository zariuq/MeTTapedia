import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralDeadBinder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralAnywhereOpen
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullStrengthening

/-!
# Controls for intersection behind a dead binder

In the tower typed equality strengthens past an unused variable (`tower_strengthening`, by
`Interface.DependentFull.Strengthening.equal_strengthen`), so the dead-binder family runs there. At budget 16 and eight rounds, over
`A : U0, F : U0 → U0 → U0, b : F A A`:

| Store | Anywhere solver | Dead-binder solver |
|---|---|---|
| `λ p x y. F x y ≐ λ p x y. F y x` at `Π (p : Id (F A A) b b). Π x y. U0` | suspended | commit |
| the same, then `λ x y. F x x ≐ λ x y. x` | suspended | refuted |

Wherever the anywhere family decides, the dead-binder family decides the same way (`dead_of_anywhere`), so the census
and the reorder witness keep their outcomes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral.DeadControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.OlderControls
open ContextualDependentIntersectionGeneral.AnywhereControls ContextualDependentIntersectionGeneral.InPlaceControls

/-- **Typed equality strengthens past an unused variable in the tower.** -/
theorem tower_strengthening : EqualStrengthening setting.R := by
  intro _ _ _ formed _ _ _ typedLeft typedRight equal
  exact Interface.DependentFull.Strengthening.equal_strengthen (fun _ => (0 : Nat)) formed typedLeft typedRight equal

/-- The dead-binder solver of the tower controls, as a fuel-indexed family. -/
noncomputable def deadTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  deadFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening

/-- The dead-binder solver at budget 16. -/
noncomputable def deadOnly : Solver setting.levels := deadTower.solver 16

/-! ## The open row -/

/-- **The dead-binder solver commits on the open row of the anywhere family.** -/
theorem annotated_committed : (run deadOnly annotatedStore 8).readout = .commit := by decide +kernel

/-- `λ x y. F x x ≐ λ x y. x`, at `U0 → U0 → U0`. -/
def annotatedDiagonal : Equation (TotalTerm withDependentAfter) :=
  (termIn withDependentAfter binaryDependent (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 1))))
      (by decide +kernel),
    termIn withDependentAfter binaryDependent (.lam (.lam (.var 1))) (by decide +kernel))

/-- The open row, then the diagonal. -/
def annotatedDiagonalStore : EquationStore (TotalTerm withDependentAfter) := annotatedStore ++ [annotatedDiagonal]

theorem annotatedDiagonal_anywhere_suspended :
    (run anywhereOnly annotatedDiagonalStore 8).readout = .suspended := by decide +kernel

/-- **The dead-binder solver refutes it.** -/
theorem annotatedDiagonal_refuted : (run deadOnly annotatedDiagonalStore 8).readout = .refuted := by decide +kernel

theorem annotatedDiagonal_unsolvable : ¬ (frames setting.levels).Solvable annotatedDiagonalStore :=
  Outcome.readout_eq_refuted annotatedDiagonal_refuted

/-- `λ p x y. F x x ≐ λ p x y. x`, at the annotation that mentions `b`. -/
def underDiagonal : Equation (TotalTerm withDependentAfter) :=
  (termIn withDependentAfter annotatedType (.lam (.lam (.lam (.app (.app (.var 4) (.var 1)) (.var 1)))))
      (by decide +kernel),
    termIn withDependentAfter annotatedType (.lam (.lam (.lam (.var 1)))) (by decide +kernel))

/-- The open row, then the diagonal under the same dead binder. -/
def underDiagonalStore : EquationStore (TotalTerm withDependentAfter) := annotatedStore ++ [underDiagonal]

/-- **A store outside the fragment that stays suspended**: `F x x` is not a pattern, and with the diagonal under the
same dead binder the dead-binder solver does not reach the refutation at this budget (the diagonal outside the binder
is refuted, `annotatedDiagonal_refuted`). -/
theorem underDiagonal_suspended : (run deadOnly underDiagonalStore 8).readout = .suspended := by decide +kernel

/-! ## Conservativity -/

/-- **Wherever the anywhere solver decides at budget 16, the dead-binder solver decides the same way.** -/
theorem dead_of_anywhere {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (decided : (run anywhereOnly problem 8).Decided) : run deadOnly problem 8 = run anywhereOnly problem 8 :=
  dead_run_of_anywhere (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening 16 8 problem decided

/-- **The census keeps its outcomes under the dead-binder solver.** -/
theorem dead_of_final {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (final : ContextualDependentAcceptance3.Controls.finalDecided problem = true) :
    (run inPlaceOnly problem 8).Decided ∧ run deadOnly problem 8 = run inPlaceOnly problem 8 := by
  obtain ⟨decided, same⟩ := anywhere_of_final final
  refine ⟨decided, ?_⟩
  have anywhereDecided : (run anywhereOnly problem 8).Decided := by rw [same]; exact decided
  rw [dead_of_anywhere anywhereDecided, same]

end ContextualDependentIntersectionGeneral.DeadControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
