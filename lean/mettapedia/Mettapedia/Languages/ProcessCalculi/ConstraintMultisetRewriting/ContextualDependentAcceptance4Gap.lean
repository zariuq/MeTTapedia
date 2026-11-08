import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralDeadBinderControls

/-!
# A firing gap: a pattern equation behind a dead binder

Acceptance for the dead-binder family is reduced to firing (`ContextualDependentAcceptance4.tower_dead_decided_of_firing`).
This store shows that firing still needs a rule. Over `A : U0, F : U0 → U0 → U0, b : F A A`, the equation

  `λ p x y. F x y ≐ λ p x y. x` at `Π (p : Id (F A A) b b). Π (x y : U0). U0`

is a Miller pattern equation for `F`, with equal annotations (`deadPattern_shape`), in the dynamic pattern fragment
(`deadPattern_in_fragment`), and solvable by `F := λ x y. x`, after which `b : A` (`deadPattern_solvable`).

The pattern rules solve the newest metavariable, and `b` comes after `F` and mentions it; the in-place rules would
strengthen the equation past `b`, but its annotation mentions `b` through `p`; the reorder rule cannot exchange `b` and
`F`; and the dead-binder rule drops `p` only in front of an intersection. The dead-binder family is suspended at budgets
16, 64 and 256 (`deadPattern_suspended`, `deadPattern_suspended_64`, `deadPattern_suspended_256`), as is the anywhere
family (`deadPattern_anywhere`). Suspension at every budget is not proved here.

The binder `p` is dead: neither side nor the codomain mentions it. Dropping it in front of the pattern rules, as the
dead-binder rule already does in front of intersection, would solve the store.
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

/-- `λ p x y. F x y ≐ λ p x y. x`, at the annotation that mentions `b`. -/
def deadPattern : Equation (TotalTerm withDependentAfter) :=
  (termIn withDependentAfter annotatedType (.lam (.lam (.lam (.app (.app (.var 4) (.var 1)) (.var 0)))))
      (by decide +kernel),
    termIn withDependentAfter annotatedType (.lam (.lam (.lam (.var 1)))) (by decide +kernel))

def deadPatternStore : EquationStore (TotalTerm withDependentAfter) := [deadPattern]

/-- The store has Miller sides and equal annotation codes. -/
theorem deadPattern_shape :
    deadPatternStore.all (fun equation => ContextualDependentShortClosure.Controls.sidesMiller equation &&
      decide (equation.1.1.code = equation.2.1.code)) = true := by
  decide +kernel

/-- **The store is in the dynamic pattern fragment.** -/
theorem deadPattern_in_fragment : InFragmentStore deadPatternStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl deadPattern.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- `F := λ x y. x`. -/
def firstAnswer : typeContext ⟶ withBinary :=
  Elimination.instantiate typeContext (termIn typeContext binary (.lam (.lam (.var 1))) (by decide +kernel)).2

/-- `A : U0, b : (λ x y. x) A A`. -/
abbrev firstContext := extend typeContext (dependentAfter.reindex firstAnswer)

open TypedContextual.QuotientComprehensionSyntax in
/-- The solution `F := λ x y. x`, lifted past `b`. -/
def deadPatternSolution : firstContext ⟶ withDependentAfter := rawLift firstAnswer dependentAfter

/-- The conversion executable accepts the instantiated equation. -/
theorem deadPattern_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      firstContext.raw (subst deadPatternSolution.substitution deadPattern.1.2.code)
      (subst deadPatternSolution.substitution deadPattern.2.2.code)
      (subst deadPatternSolution.substitution deadPattern.1.1.code)).isSome = true := by
  decide +kernel

/-- **The store is solvable.** -/
theorem deadPattern_solvable : (frames setting.levels).Solvable deadPatternStore := by
  refine ⟨firstContext, deadPatternSolution, (models_iff setting.levels deadPatternSolution deadPatternStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(annotatedType.reindex deadPatternSolution).isType.refl, ?_⟩
  have check := deadPattern_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      firstContext.raw (subst deadPatternSolution.substitution deadPattern.1.2.code)
      (subst deadPatternSolution.substitution deadPattern.2.2.code)
      (subst deadPatternSolution.substitution deadPattern.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down firstContext.formed (deadPattern.1.2.reindex deadPatternSolution).typed
        (deadPattern.2.2.reindex deadPatternSolution).typed

/-- **The dead-binder family is suspended on it** at budget 16. -/
theorem deadPattern_suspended : (run deadOnly deadPatternStore 8).readout = .suspended := by decide +kernel

/-- **And at budget 64.** -/
theorem deadPattern_suspended_64 : (run (deadTower.solver 64) deadPatternStore 8).readout = .suspended := by
  decide +kernel

/-- **And at budget 256.** -/
theorem deadPattern_suspended_256 : (run (deadTower.solver 256) deadPatternStore 8).readout = .suspended := by
  decide +kernel

/-- The anywhere family is suspended on it too. -/
theorem deadPattern_anywhere : (run anywhereOnly deadPatternStore 8).readout = .suspended := by decide +kernel

/-- **The firing gap**: in the fragment, solvable, and the dead-binder family suspended at budgets 16 and 64. -/
theorem deadPattern_gap :
    InFragmentStore deadPatternStore ∧ (frames setting.levels).Solvable deadPatternStore ∧
      (run deadOnly deadPatternStore 8).readout = .suspended ∧
      (run (deadTower.solver 64) deadPatternStore 8).readout = .suspended :=
  ⟨deadPattern_in_fragment, deadPattern_solvable, deadPattern_suspended, deadPattern_suspended_64⟩

end ContextualDependentIntersectionGeneral.DeadControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
