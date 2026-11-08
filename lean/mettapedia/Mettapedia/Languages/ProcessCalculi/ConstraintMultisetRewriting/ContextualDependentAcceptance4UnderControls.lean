import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4UnderFamily
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4GapInner

/-!
# Controls for the under-binder family

The tower's under-binder family commits on both firing gaps of the every-rule family, the dead binder under one live
binder (`middle_under_committed`) and under two (`last_under_committed`), as well as on the dead-binder gap
(`deadPattern_under_committed`) and on two dead binders in front (`twoDead_under_committed`); it refutes R119's
unsolvable diagonal store (`annotatedDiagonal_under_refuted`), and decides R119's 44 census stores as the in-place
family does (`under_of_final`).

An annotation that mentions a later declaration through a **used** binder, `λ p. F ≐ λ p. Id (Id G b b) p p` at
`Π (p : Id G b b). U0` with `F` older than `b`, is refuted (`used_under_refuted`, `used_unsolvable`): an older
metavariable cannot depend on `p`.
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

/-- **A dead binder under one live binder**: committed. -/
theorem middle_under_committed : (run (underTower.solver 16) middleStore 8).readout = .commit := by decide +kernel

/-- **A dead binder under two live binders**: committed. -/
theorem last_under_committed : (run (underTower.solver 16) lastStore 8).readout = .commit := by decide +kernel

/-- The dead-binder gap: committed. -/
theorem deadPattern_under_committed : (run (underTower.solver 16) deadPatternStore 8).readout = .commit := by
  decide +kernel

/-- Two dead binders in front: committed. -/
theorem twoDead_under_committed : (run (underTower.solver 16) twoDeadStore 8).readout = .commit := by
  decide +kernel

/-- **R119's unsolvable diagonal store**: refuted. -/
theorem annotatedDiagonal_under_refuted :
    (run (underTower.solver 16) annotatedDiagonalStore 8).readout = .refuted := by
  decide +kernel

/-- **R119's census**: the under-binder family decides the 44 census stores as the in-place family does. -/
theorem under_of_final {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (final : ContextualDependentAcceptance3.Controls.finalDecided problem = true) :
    (run inPlaceOnly problem 8).Decided ∧ run (underTower.solver 16) problem 8 = run inPlaceOnly problem 8 := by
  obtain ⟨decided, same⟩ := dead_of_final final
  refine ⟨decided, ?_⟩
  have deadDecided : (run deadOnly problem 8).Decided := by rw [same]; exact decided
  rw [← same]
  exact under_run_of_dead (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening 16 8 problem
    deadDecided

/-! ## An annotation that mentions a later declaration through a used binder -/

/-- `U0` over a context. -/
def smallUniverse (Γ : Context setting.R) (accepted : (ContextualDependentPruning.formType (S := setting)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 Γ (.head (.sort Tower.zero))).isSome) : TypeOver Γ :=
  formIn Γ (.head (.sort Tower.zero)) accepted

/-- `A : U0, G : U0`. -/
abbrev ctxG := extend ContextualDependentInversion.Controls.typeContext
  (smallUniverse ContextualDependentInversion.Controls.typeContext (by decide +kernel))
/-- `A : U0, G : U0, F : U0`. -/
abbrev ctxGF := extend ctxG (smallUniverse ctxG (by decide +kernel))
def gType : TypeOver ctxGF := formIn ctxGF (.var 1) (by decide +kernel)
/-- `A : U0, G : U0, F : U0, b : G`. -/
abbrev ctxGFb := extend ctxGF gType

/-- `Π (p : Id G b b). U0`. -/
def usedType : TypeOver ctxGFb :=
  formIn ctxGFb (.pi (.id (.var 2) (.var 0) (.var 0)) (.head (.sort Tower.zero))) (by decide +kernel)

/-- `λ p. F ≐ λ p. Id (Id G b b) p p`: `F` is older than `b`, and the right side uses `p`. -/
def usedStore : EquationStore (TotalTerm ctxGFb) :=
  [(termIn ctxGFb usedType (.lam (.var 2)) (by decide +kernel),
    termIn ctxGFb usedType (.lam (.id (.id (.var 3) (.var 1) (.var 1)) (.var 0) (.var 0))) (by decide +kernel))]

/-- The store has Miller sides and equal annotation codes. -/
theorem used_shape :
    usedStore.all (fun equation => ContextualDependentShortClosure.Controls.sidesMiller equation &&
      decide (equation.1.1.code = equation.2.1.code)) = true := by
  decide +kernel

/-- **A used binder whose type mentions a later declaration is refuted**, with a certified refutation. -/
theorem used_under_refuted : (run (underTower.solver 16) usedStore 8).readout = .refuted := by decide +kernel

/-- So the store has no solution. -/
theorem used_unsolvable : ¬ (frames setting.levels).Solvable usedStore :=
  Outcome.readout_eq_refuted used_under_refuted

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
