import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTowerBudget

/-!
# Sufficient and insufficient budgets of the actual normalizer

A family with k beta steps succeeds at k+1 units of fuel and is unfinished
at k. Every member is typed. The untyped self-application loop exhausts
every budget, showing why the typing/normalization boundary matters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentReductionBudget.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open ExecutableReduction

def delayed {n : Nat} : Nat → Tower.Tm n → Tower.Tm n
  | 0, term => term
  | count + 1, term => .app (.lam (.var 0)) (delayed count term)

abbrev ground : Tower.Tm 0 := .head .legacyGround
abbrev sort0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)

def run {n : Nat} (fuel : Nat) (term : Tower.Tm n) : Option (Tower.Tm n) :=
  (ContextualDependentTowerBudget.reducer fuel term).map Subtype.val

theorem delayed_step {n : Nat} (count fuel : Nat) (term : Tower.Tm n) :
    run (fuel + 1) (delayed (count + 1) term) = run fuel (delayed count term) := by
  cases computed : ExecutableReduction.normalize Tower.rules (fun _ => none) fuel (delayed count term) <;>
    simp [run, ContextualDependentTowerBudget.reducer, delayed, ExecutableReduction.normalize, ExecutableReduction.step,
      inst0, subst, subst0, computed]

theorem exact_sufficient_budget (count : Nat) :
    run (count + 1) (delayed count ground) = some ground := by
  induction count with
  | zero => rfl
  | succ count ih => rw [delayed_step, ih]

theorem one_less_is_unfinished (count : Nat) : run count (delayed count ground) = none := by
  induction count with
  | zero => rfl
  | succ count ih => rw [delayed_step, ih]

theorem delayed_is_typed (count : Nat) : Typed Tower.rules .nil (delayed count ground) sort0 := by
  induction count with
  | zero => exact .headType .legacyGround
  | succ count ih =>
    exact Derivable.appElim (A := sort0) (B := sort0)
      (.lamIntro (.piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _)
        (.sorts _ _)) (.sort _) (.var 0)) ih

theorem larger_budgets_agree (count larger : Nat) (enough : count + 1 ≤ larger) :
    run larger (delayed count ground) = some ground := by
  have accepted := exact_sufficient_budget count
  unfold run at accepted ⊢
  cases computed : ContextualDependentTowerBudget.reducer (count + 1) (delayed count ground) with
  | none =>
    simp only [computed, Option.map_none] at accepted
    cases accepted
  | some result =>
    have stable := success_mono Tower.rules (fun _ => none) computed enough
    change ExecutableReduction.normalize Tower.rules (fun _ => none) larger (delayed count ground) = some result at stable
    change (ExecutableReduction.normalize Tower.rules (fun _ => none) larger (delayed count ground)).map Subtype.val = _
    rw [stable]
    simpa only [computed] using accepted

def selfApply : Tower.Tm 0 := .lam (.app (.var 0) (.var 0))
def loop : Tower.Tm 0 := .app selfApply selfApply

theorem loop_exhausts_every_budget (fuel : Nat) :
    ContextualDependentTowerBudget.reducer fuel loop = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have loopStep : ExecutableReduction.step Tower.rules (fun _ => none) loop =
        some (⟨loop, StepCore.betaPi (.app (.var 0) (.var 0)) selfApply⟩ : StepResult Tower.rules loop) := rfl
    unfold ContextualDependentTowerBudget.reducer at ih ⊢
    rw [ExecutableReduction.normalize, loopStep]
    dsimp only
    rw [ih]

theorem loop_has_no_typing (type : Tower.Tm 0) : ¬ Typed Tower.rules .nil loop type := by
  intro typed
  obtain ⟨fuel, result, _, stable⟩ := ContextualDependentTowerBudget.typed_eventually_stable .nil typed
  have accepted := stable fuel (Nat.le_refl _)
  rw [loop_exhausts_every_budget] at accepted
  cases accepted

/-- A reducer's certificate type alone does not promise eventual success. -/
def refusingReducer : Reducer Tower.rules := fun _ _ _ => none

theorem certificate_type_does_not_imply_completeness :
    Typed Tower.rules .nil ground sort0 ∧ ∀ fuel, refusingReducer fuel ground = none :=
  ⟨.headType .legacyGround, fun _ => rfl⟩

end ContextualDependentReductionBudget.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
