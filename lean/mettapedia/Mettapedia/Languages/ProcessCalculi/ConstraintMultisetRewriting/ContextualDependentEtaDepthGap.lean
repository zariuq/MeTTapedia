import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthFamily
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4UnderControls

/-!
# Abstraction depth: gap witnesses and controls

Over `A : U0`, at `(U0 → U0) → U0 → U0`:

* **`λ g. g ≐ λ g x. x`** (`shallowStore`, the right side deeper) and **`λ g x. x ≐ λ g. g`** (`deepStore`, the left
  side deeper) are in the dynamic pattern fragment, and the under-binder family's first round is stuck on them at
  budgets 16, 64 and 256 (16 and 64 for `deepStore`). The census opens at the left side's depth, and the readers of
  codes need both sides at the same depth. R110's η reorientation reads only the right-deeper case, and only through
  the clash test, the first pattern, prune and exchange rules and the in-place rule.
* **`λ g. g ≐ λ g x. g (g x)`** and, at `(U0 → U0) → (U0 → U0) → U0 → U0`, **`λ g h. g ≐ λ g h x. h x`**: stuck at
  budget 16.
* Over `A, F : (U0 → U0) → U0 → U0`, **`λ g x. g (F g x) ≐ λ g. g`** (`solvableStore`) is in the fragment and solvable
  by `F := λ g x. x`.

**The η-depth family** (`ContextualDependentEtaDepth.longTower`) refutes the four unsolvable stores, with certified
refutations (so they are unsolvable), and commits on the solvable one. It keeps R119's 44 census stores' outcomes
(`long_of_final`).

**A gap that remains.** At the flexible base `(A → A) → A → A`, **`λ g. g ≐ λ g x. x`** (`flexibleStore`) is in the
fragment, and the η-depth family is stuck in its first round at budgets 16 and 64: after η-expansion the sides `g x`
and `x` have distinct skeletons, but the clash reader reads skeletons only at a rigid base type, and the flexible-base
readers only spines of one local.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentIntersectionGeneral.InPlaceControls ContextualDependentIntersectionGeneral.DeadControls

abbrev ctxA := ContextualDependentInversion.Controls.typeContext

/-- `(U0 → U0) → U0 → U0` over `A`. -/
def functions : TypeOver ctxA := formIn ctxA (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
  (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))) (by decide +kernel)

/-- `(U0 → U0) → (U0 → U0) → U0 → U0` over `A`. -/
def twoFunctions : TypeOver ctxA := formIn ctxA (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
  (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
    (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))) (by decide +kernel)

/-- `(A → A) → A → A`. -/
def flexibleFunctions : TypeOver ctxA := formIn ctxA (.pi (.pi (.var 0) (.var 1)) (.pi (.var 1) (.var 2)))
  (by decide +kernel)

/-- `λ g. g ≐ λ g x. x`. -/
def shallowEquation : Equation (TotalTerm ctxA) :=
  (termIn ctxA functions (.lam (.var 0)) (by decide +kernel),
    termIn ctxA functions (.lam (.lam (.var 0))) (by decide +kernel))
def shallowStore : EquationStore (TotalTerm ctxA) := [shallowEquation]

/-- `λ g x. x ≐ λ g. g`. -/
def deepEquation : Equation (TotalTerm ctxA) :=
  (termIn ctxA functions (.lam (.lam (.var 0))) (by decide +kernel),
    termIn ctxA functions (.lam (.var 0)) (by decide +kernel))
def deepStore : EquationStore (TotalTerm ctxA) := [deepEquation]

/-- `λ g. g ≐ λ g x. g (g x)`. -/
def twiceStore : EquationStore (TotalTerm ctxA) :=
  [(termIn ctxA functions (.lam (.var 0)) (by decide +kernel),
    termIn ctxA functions (.lam (.lam (.app (.var 1) (.app (.var 1) (.var 0))))) (by decide +kernel))]

/-- `λ g h. g ≐ λ g h x. h x`. -/
def otherStore : EquationStore (TotalTerm ctxA) :=
  [(termIn ctxA twoFunctions (.lam (.lam (.var 1))) (by decide +kernel),
    termIn ctxA twoFunctions (.lam (.lam (.lam (.app (.var 1) (.var 0))))) (by decide +kernel))]

/-- `λ g. g ≐ λ g x. x` at `(A → A) → A → A`, a flexible base. -/
def flexibleEquation : Equation (TotalTerm ctxA) :=
  (termIn ctxA flexibleFunctions (.lam (.var 0)) (by decide +kernel),
    termIn ctxA flexibleFunctions (.lam (.lam (.var 0))) (by decide +kernel))
def flexibleStore : EquationStore (TotalTerm ctxA) := [flexibleEquation]

/-- `A, F : (U0 → U0) → U0 → U0`. -/
abbrev ctxF := extend ctxA functions
def functionsF : TypeOver ctxF := formIn ctxF (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
  (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))) (by decide +kernel)

/-- `λ g x. g (F g x) ≐ λ g. g`: solvable by `F := λ g x. x`. -/
def solvableEquation : Equation (TotalTerm ctxF) :=
  (termIn ctxF functionsF (.lam (.lam (.app (.var 1) (.app (.app (.var 2) (.var 1)) (.var 0))))) (by decide +kernel),
    termIn ctxF functionsF (.lam (.var 0)) (by decide +kernel))
def solvableStore : EquationStore (TotalTerm ctxF) := [solvableEquation]

/-! ## Membership in the fragment -/

theorem shallow_in_fragment : InFragmentStore shallowStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl shallowEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem deep_in_fragment : InFragmentStore deepStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl deepEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem flexible_in_fragment : InFragmentStore flexibleStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl flexibleEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem solvable_in_fragment : InFragmentStore solvableStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl solvableEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-! ## The under-binder family is stuck -/

/-- **The first round of the under-binder family is stuck on `λ g. g ≐ λ g x. x`**, at budget 16. -/
theorem shallow_under_stuck : isStuck (run (underTower.solver 16) shallowStore 1) = true := by decide +kernel
theorem shallow_under_stuck_64 : isStuck (run (underTower.solver 64) shallowStore 1) = true := by decide +kernel
theorem shallow_under_stuck_256 : isStuck (run (underTower.solver 256) shallowStore 1) = true := by decide +kernel
theorem deep_under_stuck : isStuck (run (underTower.solver 16) deepStore 1) = true := by decide +kernel
theorem deep_under_stuck_64 : isStuck (run (underTower.solver 64) deepStore 1) = true := by decide +kernel
theorem twice_under_stuck : isStuck (run (underTower.solver 16) twiceStore 1) = true := by decide +kernel
theorem other_under_stuck : isStuck (run (underTower.solver 16) otherStore 1) = true := by decide +kernel

/-! ## The η-depth family decides them -/

theorem shallow_long_refuted : (run (longTower.solver 16) shallowStore 8).readout = .refuted := by decide +kernel
theorem deep_long_refuted : (run (longTower.solver 16) deepStore 8).readout = .refuted := by decide +kernel
theorem twice_long_refuted : (run (longTower.solver 16) twiceStore 8).readout = .refuted := by decide +kernel
theorem other_long_refuted : (run (longTower.solver 16) otherStore 8).readout = .refuted := by decide +kernel
/-- **The solvable store commits** under the η-depth family. -/
theorem solvable_long_committed : (run (longTower.solver 16) solvableStore 8).readout = .commit := by decide +kernel

theorem shallow_unsolvable : ¬ (frames setting.levels).Solvable shallowStore :=
  Outcome.readout_eq_refuted shallow_long_refuted
theorem deep_unsolvable : ¬ (frames setting.levels).Solvable deepStore :=
  Outcome.readout_eq_refuted deep_long_refuted
theorem twice_unsolvable : ¬ (frames setting.levels).Solvable twiceStore :=
  Outcome.readout_eq_refuted twice_long_refuted
theorem other_unsolvable : ¬ (frames setting.levels).Solvable otherStore :=
  Outcome.readout_eq_refuted other_long_refuted

/-- **R119's census**: the η-depth family decides the 44 census stores as the in-place family does. -/
theorem long_of_final {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (final : ContextualDependentAcceptance3.Controls.finalDecided problem = true) :
    (run inPlaceOnly problem 8).Decided ∧ run (longTower.solver 16) problem 8 = run inPlaceOnly problem 8 := by
  obtain ⟨decided, same⟩ := under_of_final final
  refine ⟨decided, ?_⟩
  have underDecided : (run (underTower.solver 16) problem 8).Decided := by rw [same]; exact decided
  rw [← same]
  exact long_run_of_under (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening 16 8 problem
    underDecided

/-! ## A gap at a flexible base -/

/-- **The η-depth family is stuck on `λ g. g ≐ λ g x. x` at a flexible base**, at budget 16. -/
theorem flexible_long_stuck : isStuck (run (longTower.solver 16) flexibleStore 1) = true := by decide +kernel
theorem flexible_long_stuck_64 : isStuck (run (longTower.solver 64) flexibleStore 1) = true := by decide +kernel

end ContextualDependentEtaDepth.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
