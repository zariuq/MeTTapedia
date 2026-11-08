import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4EveryControls

/-!
# A firing gap of the every-rule family: a dead binder under a live binder

The every-rule family reads a dead binder only in front of an equation, as the outermost abstraction of both sides.
Over `A : U0, F : U0 → U0 → U0, b : F A A`, the equation

  `λ x p y. F x y ≐ λ x p y. x` at `Π (x : U0). Π (p : Id (F A A) b b). Π (y : U0). U0`

has its dead binder `p` under the live binder `x`. It is a Miller pattern equation for `F` with equal annotations
(`middle_shape`), in the dynamic pattern fragment (`middle_in_fragment`), and solvable by `F := λ x y. x`
(`middle_solvable`); the every-rule family is suspended on it at budgets 16, 64 and 256 (`middle_suspended`,
`middle_suspended_64`, `middle_suspended_256`). So is the innermost case `λ x y p. F x y ≐ λ x y p. x` (`last_gap`).
Suspension at every budget is not proved here.

Reading such a binder means opening the live binders first: the dead binder is then the last declaration of the
opened context, where R119's reading and strengthening apply, and the reduced equation closes back under the live
binders. The under-binder family does this and commits on both stores
(`ContextualDependentAcceptance4.middle_under_committed`, `ContextualDependentAcceptance4.last_under_committed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance4

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.OlderControls
open ContextualDependentIntersectionGeneral.AnywhereControls ContextualDependentIntersectionGeneral.InPlaceControls
open ContextualDependentIntersectionGeneral.DeadControls

/-- `Π (x : U0). Π (p : Id (F A A) b b). Π (y : U0). U0`. -/
def middleType : TypeOver withDependentAfter :=
  formIn withDependentAfter (.pi (.head (.sort Tower.zero))
    (.pi (.id (.app (.app (.var 2) (.var 3)) (.var 3)) (.var 1) (.var 1))
      (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))) (by decide +kernel)

/-- `λ x p y. F x y ≐ λ x p y. x`. -/
def middlePattern : Equation (TotalTerm withDependentAfter) :=
  (termIn withDependentAfter middleType (.lam (.lam (.lam (.app (.app (.var 4) (.var 2)) (.var 0)))))
      (by decide +kernel),
    termIn withDependentAfter middleType (.lam (.lam (.lam (.var 2)))) (by decide +kernel))

def middleStore : EquationStore (TotalTerm withDependentAfter) := [middlePattern]

/-- The store has Miller sides and equal annotation codes. -/
theorem middle_shape :
    middleStore.all (fun equation => ContextualDependentShortClosure.Controls.sidesMiller equation &&
      decide (equation.1.1.code = equation.2.1.code)) = true := by
  decide +kernel

/-- **The store is in the dynamic pattern fragment.** -/
theorem middle_in_fragment : InFragmentStore middleStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl middlePattern.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- The conversion executable accepts the instantiated equation. -/
theorem middle_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      firstContext.raw (subst deadPatternSolution.substitution middlePattern.1.2.code)
      (subst deadPatternSolution.substitution middlePattern.2.2.code)
      (subst deadPatternSolution.substitution middlePattern.1.1.code)).isSome = true := by
  decide +kernel

/-- **The store is solvable**, by `F := λ x y. x`. -/
theorem middle_solvable : (frames setting.levels).Solvable middleStore := by
  refine ⟨firstContext, deadPatternSolution, (models_iff setting.levels deadPatternSolution middleStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(middleType.reindex deadPatternSolution).isType.refl, ?_⟩
  have check := middle_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      firstContext.raw (subst deadPatternSolution.substitution middlePattern.1.2.code)
      (subst deadPatternSolution.substitution middlePattern.2.2.code)
      (subst deadPatternSolution.substitution middlePattern.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down firstContext.formed (middlePattern.1.2.reindex deadPatternSolution).typed
        (middlePattern.2.2.reindex deadPatternSolution).typed

/-- **The every-rule family is suspended on it** at budget 16. -/
theorem middle_suspended : (run (everyTower.solver 16) middleStore 8).readout = .suspended := by decide +kernel

/-- **And at budget 64.** -/
theorem middle_suspended_64 : (run (everyTower.solver 64) middleStore 8).readout = .suspended := by decide +kernel

/-- **And at budget 256.** -/
theorem middle_suspended_256 : (run (everyTower.solver 256) middleStore 8).readout = .suspended := by
  decide +kernel

/-- **The firing gap of the every-rule family**: in the fragment, solvable, and suspended at budgets 16, 64 and
256. -/
theorem middle_gap :
    InFragmentStore middleStore ∧ (frames setting.levels).Solvable middleStore ∧
      (run (everyTower.solver 16) middleStore 8).readout = .suspended ∧
      (run (everyTower.solver 64) middleStore 8).readout = .suspended ∧
      (run (everyTower.solver 256) middleStore 8).readout = .suspended :=
  ⟨middle_in_fragment, middle_solvable, middle_suspended, middle_suspended_64, middle_suspended_256⟩

/-! ## The dead binder innermost -/

/-- `Π (x y : U0). Π (p : Id (F A A) b b). U0`. -/
def lastType : TypeOver withDependentAfter :=
  formIn withDependentAfter (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero))
    (.pi (.id (.app (.app (.var 3) (.var 4)) (.var 4)) (.var 2) (.var 2)) (.head (.sort Tower.zero)))))
    (by decide +kernel)

/-- `λ x y p. F x y ≐ λ x y p. x`. -/
def lastPattern : Equation (TotalTerm withDependentAfter) :=
  (termIn withDependentAfter lastType (.lam (.lam (.lam (.app (.app (.var 4) (.var 2)) (.var 1)))))
      (by decide +kernel),
    termIn withDependentAfter lastType (.lam (.lam (.lam (.var 2)))) (by decide +kernel))

def lastStore : EquationStore (TotalTerm withDependentAfter) := [lastPattern]

theorem last_in_fragment : InFragmentStore lastStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl lastPattern.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem last_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      firstContext.raw (subst deadPatternSolution.substitution lastPattern.1.2.code)
      (subst deadPatternSolution.substitution lastPattern.2.2.code)
      (subst deadPatternSolution.substitution lastPattern.1.1.code)).isSome = true := by
  decide +kernel

theorem last_solvable : (frames setting.levels).Solvable lastStore := by
  refine ⟨firstContext, deadPatternSolution, (models_iff setting.levels deadPatternSolution lastStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(lastType.reindex deadPatternSolution).isType.refl, ?_⟩
  have check := last_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      firstContext.raw (subst deadPatternSolution.substitution lastPattern.1.2.code)
      (subst deadPatternSolution.substitution lastPattern.2.2.code)
      (subst deadPatternSolution.substitution lastPattern.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down firstContext.formed (lastPattern.1.2.reindex deadPatternSolution).typed
        (lastPattern.2.2.reindex deadPatternSolution).typed

/-- **The innermost dead binder is not read either**: in the fragment, solvable, suspended at budget 16. -/
theorem last_gap :
    InFragmentStore lastStore ∧ (frames setting.levels).Solvable lastStore ∧
      (run (everyTower.solver 16) lastStore 8).readout = .suspended :=
  ⟨last_in_fragment, last_solvable, by decide +kernel⟩

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
