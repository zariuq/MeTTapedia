import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralAnywhereControls

/-!
# The open intersection row: an annotation that mentions a later declaration

Over `A : U0, F : U0 → U0 → U0, b : F A A`, the equation

  `λ p x y. F x y ≐ λ p x y. F y x` at `Π (p : Id (F A A) b b). Π (x y : U0). U0`

is a flex–flex intersection on `F`, in the dynamic pattern fragment (`annotated_in_fragment`). Rotation cannot move
`F` past `b`, which mentions it, and in-place intersection cannot strengthen the equation past `b`, because its
annotation mentions `b`. The anywhere solver is suspended on it at budget 16 (`annotated_suspended`), and the store is
solvable (`annotated_solvable`: `F := λ x y. A`, after which `b : A`), so this is an open row of the census, not a
refutation.

The binder `p` is dead: neither the bodies nor the codomain mention it. Reading the equation without it and
intersecting there closes the row where typed equality strengthens past an unused variable, as in the tower
(`ContextualDependentIntersectionGeneral.DeadControls.annotated_committed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral.AnywhereControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.OlderControls

/-- `Π (p : Id (F A A) b b). Π x y. U0`. -/
def annotatedType : TypeOver withDependentAfter :=
  formIn withDependentAfter (.pi (.id (.app (.app (.var 1) (.var 2)) (.var 2)) (.var 0) (.var 0))
    (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))) (by decide +kernel)

/-- `λ p x y. F x y ≐ λ p x y. F y x`, whose annotation mentions `b : F A A`. -/
def annotatedEquation : Equation (TotalTerm withDependentAfter) :=
  (termIn withDependentAfter annotatedType (.lam (.lam (.lam (.app (.app (.var 4) (.var 1)) (.var 0)))))
      (by decide +kernel),
    termIn withDependentAfter annotatedType (.lam (.lam (.lam (.app (.app (.var 4) (.var 0)) (.var 1)))))
      (by decide +kernel))

def annotatedStore : EquationStore (TotalTerm withDependentAfter) := [annotatedEquation]

/-- The store has Miller sides and equal annotation codes. -/
theorem annotated_shape :
    annotatedStore.all (fun equation => ContextualDependentShortClosure.Controls.sidesMiller equation &&
      decide (equation.1.1.code = equation.2.1.code)) = true := by
  decide +kernel

/-- **The open row is in the dynamic pattern fragment.** -/
theorem annotated_in_fragment : InFragmentStore annotatedStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl annotatedEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The open row**: the anywhere solver is suspended at budget 16. -/
theorem annotated_suspended : (run anywhereOnly annotatedStore 8).readout = .suspended := by decide +kernel

/-! ## The store is solvable -/

/-- `F := λ x y. A`. -/
def constantAnswer : typeContext ⟶ withBinary :=
  Elimination.instantiate typeContext (termIn typeContext binary (.lam (.lam (.var 2))) (by decide +kernel)).2

/-- `A : U0, b : (λ x y. A) A A`. -/
abbrev solvedContext := extend typeContext (dependentAfter.reindex constantAnswer)

open TypedContextual.QuotientComprehensionSyntax in
/-- The solution `F := λ x y. A`, lifted past `b`. -/
def annotatedSolution : solvedContext ⟶ withDependentAfter := rawLift constantAnswer dependentAfter

/-- The conversion executable accepts the instantiated equation. -/
theorem annotated_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      solvedContext.raw (subst annotatedSolution.substitution annotatedEquation.1.2.code)
      (subst annotatedSolution.substitution annotatedEquation.2.2.code)
      (subst annotatedSolution.substitution annotatedEquation.1.1.code)).isSome = true := by
  decide +kernel

/-- **The open row is solvable.** -/
theorem annotated_solvable : (frames setting.levels).Solvable annotatedStore := by
  refine ⟨solvedContext, annotatedSolution, (models_iff setting.levels annotatedSolution annotatedStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(annotatedType.reindex annotatedSolution).isType.refl, ?_⟩
  have check := annotated_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      solvedContext.raw (subst annotatedSolution.substitution annotatedEquation.1.2.code)
      (subst annotatedSolution.substitution annotatedEquation.2.2.code)
      (subst annotatedSolution.substitution annotatedEquation.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down solvedContext.formed (annotatedEquation.1.2.reindex annotatedSolution).typed
        (annotatedEquation.2.2.reindex annotatedSolution).typed

/-- **The gap witness of the anywhere family**: in the fragment, solvable, suspended at budget 16. -/
theorem annotated_gap :
    InFragmentStore annotatedStore ∧ (frames setting.levels).Solvable annotatedStore ∧
      (run anywhereOnly annotatedStore 8).readout = .suspended :=
  ⟨annotated_in_fragment, annotated_solvable, annotated_suspended⟩

end ContextualDependentIntersectionGeneral.AnywhereControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
