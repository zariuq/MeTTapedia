import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Renaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning

/-!
# Reflecting conversion reductions through variable maps

The existing directed-reduction reflection theorem excludes universe-head
steps. Conversion also uses those steps. Here the same syntax inversion
covers the complete conversion reduction, while reusing the existing shape
inversion lemmas and the explicit root-renaming reflection contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentReductionReflection

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open TypedEquality TypedEquality.Normalization
open TypedEquality.StrongNormalization

variable {Head : Type} {R : Rules Head}

/-- Only injective maps are needed by context strengthening. -/
def RootReflectsInjections (root : RootComputation Head) : Prop :=
  ∀ {n m : Nat} (rho : Ren n m), Function.Injective rho →
    ∀ {term : Tm Head n} {result : Tm Head m},
      root.step (Presentation.rename rho term) result →
        ∃ recovered, root.step term recovered ∧ result = Presentation.rename rho recovered

theorem RootReflectsInjections.of_all {root : RootComputation Head}
    (reflects : RootReflectsRename root) : RootReflectsInjections root := by
  intro n m rho _ term result step
  exact reflects rho step


theorem step_reflects (reflects : RootReflectsInjections R.computation) {m : Nat}
    {s u : Tm Head m} (step : StepCore R.computation R.headEq s u) :
    ∀ {n : Nat} (ρ : Ren n m) (_injective : Function.Injective ρ) (t : Tm Head n), Presentation.rename ρ t = s →
      ∃ t', StepCore R.computation R.headEq t t' ∧ u = Presentation.rename ρ t' := by
  induction step with
  | betaPi body a =>
      intro n ρ injective t h
      obtain ⟨f, a', rfl, hf, rfl⟩ := rename_eq_app h
      obtain ⟨b, rfl, rfl⟩ := rename_eq_lam hf
      exact ⟨inst0 a' b, .betaPi b a', (rename_inst0 ρ a' b).symm⟩
  | betaSigmaFst a b =>
      intro n ρ injective t h
      obtain ⟨p, rfl, hp⟩ := rename_eq_fst h
      obtain ⟨a', b', rfl, rfl, rfl⟩ := rename_eq_pair hp
      exact ⟨a', .betaSigmaFst a' b', rfl⟩
  | betaSigmaSnd a b =>
      intro n ρ injective t h
      obtain ⟨p, rfl, hp⟩ := rename_eq_snd h
      obtain ⟨a', b', rfl, rfl, rfl⟩ := rename_eq_pair hp
      exact ⟨b', .betaSigmaSnd a' b', rfl⟩
  | @head n left right equal =>
      intro sourceArity rho injective term image
      cases term <;> simp only [Presentation.rename, reduceCtorEq, Tm.head.injEq] at image
      subst left
      exact ⟨.head right, .head equal, rfl⟩
  | root r =>
      intro n ρ injective t h
      subst h
      obtain ⟨t', r', rfl⟩ := reflects ρ injective r
      exact ⟨t', .root r', rfl⟩
  | congPiDom _ ih =>
      intro n ρ injective t h
      obtain ⟨A, B, rfl, rfl, rfl⟩ := rename_eq_pi h
      obtain ⟨A', s, rfl⟩ := ih ρ injective A rfl
      exact ⟨.pi A' B, .congPiDom s, rfl⟩
  | congPiCod _ ih =>
      intro n ρ injective t h
      obtain ⟨A, B, rfl, rfl, rfl⟩ := rename_eq_pi h
      obtain ⟨B', s, rfl⟩ := ih (liftRen ρ) (ContextualDependentPruning.liftRen_injective injective) B rfl
      exact ⟨.pi A B', .congPiCod s, rfl⟩
  | congSigmaDom _ ih =>
      intro n ρ injective t h
      obtain ⟨A, B, rfl, rfl, rfl⟩ := rename_eq_sigma h
      obtain ⟨A', s, rfl⟩ := ih ρ injective A rfl
      exact ⟨.sigma A' B, .congSigmaDom s, rfl⟩
  | congSigmaCod _ ih =>
      intro n ρ injective t h
      obtain ⟨A, B, rfl, rfl, rfl⟩ := rename_eq_sigma h
      obtain ⟨B', s, rfl⟩ := ih (liftRen ρ) (ContextualDependentPruning.liftRen_injective injective) B rfl
      exact ⟨.sigma A B', .congSigmaCod s, rfl⟩
  | congIdTy _ ih =>
      intro n ρ injective t h
      obtain ⟨A, a, b, rfl, rfl, rfl, rfl⟩ := rename_eq_id h
      obtain ⟨A', s, rfl⟩ := ih ρ injective A rfl
      exact ⟨.id A' a b, .congIdTy s, rfl⟩
  | congIdLeft _ ih =>
      intro n ρ injective t h
      obtain ⟨A, a, b, rfl, rfl, rfl, rfl⟩ := rename_eq_id h
      obtain ⟨a', s, rfl⟩ := ih ρ injective a rfl
      exact ⟨.id A a' b, .congIdLeft s, rfl⟩
  | congIdRight _ ih =>
      intro n ρ injective t h
      obtain ⟨A, a, b, rfl, rfl, rfl, rfl⟩ := rename_eq_id h
      obtain ⟨b', s, rfl⟩ := ih ρ injective b rfl
      exact ⟨.id A a b', .congIdRight s, rfl⟩
  | congLam _ ih =>
      intro n ρ injective t h
      obtain ⟨b, rfl, rfl⟩ := rename_eq_lam h
      obtain ⟨b', s, rfl⟩ := ih (liftRen ρ) (ContextualDependentPruning.liftRen_injective injective) b rfl
      exact ⟨.lam b', .congLam s, rfl⟩
  | congAppFun _ ih =>
      intro n ρ injective t h
      obtain ⟨f, a, rfl, rfl, rfl⟩ := rename_eq_app h
      obtain ⟨f', s, rfl⟩ := ih ρ injective f rfl
      exact ⟨.app f' a, .congAppFun s, rfl⟩
  | congAppArg _ ih =>
      intro n ρ injective t h
      obtain ⟨f, a, rfl, rfl, rfl⟩ := rename_eq_app h
      obtain ⟨a', s, rfl⟩ := ih ρ injective a rfl
      exact ⟨.app f a', .congAppArg s, rfl⟩
  | congPairFst _ ih =>
      intro n ρ injective t h
      obtain ⟨a, b, rfl, rfl, rfl⟩ := rename_eq_pair h
      obtain ⟨a', s, rfl⟩ := ih ρ injective a rfl
      exact ⟨.pair a' b, .congPairFst s, rfl⟩
  | congPairSnd _ ih =>
      intro n ρ injective t h
      obtain ⟨a, b, rfl, rfl, rfl⟩ := rename_eq_pair h
      obtain ⟨b', s, rfl⟩ := ih ρ injective b rfl
      exact ⟨.pair a b', .congPairSnd s, rfl⟩
  | congFst _ ih =>
      intro n ρ injective t h
      obtain ⟨p, rfl, rfl⟩ := rename_eq_fst h
      obtain ⟨p', s, rfl⟩ := ih ρ injective p rfl
      exact ⟨.fst p', .congFst s, rfl⟩
  | congSnd _ ih =>
      intro n ρ injective t h
      obtain ⟨p, rfl, rfl⟩ := rename_eq_snd h
      obtain ⟨p', s, rfl⟩ := ih ρ injective p rfl
      exact ⟨.snd p', .congSnd s, rfl⟩
  | congRefl _ ih =>
      intro n ρ injective t h
      obtain ⟨a, rfl, rfl⟩ := rename_eq_refl h
      obtain ⟨a', s, rfl⟩ := ih ρ injective a rfl
      exact ⟨.refl a', .congRefl s, rfl⟩


/-- Reflect a whole conversion reduction, including head equality steps. -/
theorem reduces_reflects (reflects : RootReflectsInjections R.computation) {n m : Nat}
    {rho : Ren n m} {term : Tm Head n} {result : Tm Head m}
    (injective : Function.Injective rho)
    (steps : TypedEquality.Reduces R (Presentation.rename rho term) result) :
    ∃ recovered, TypedEquality.Reduces R term recovered ∧ result = Presentation.rename rho recovered := by
  induction steps with
  | refl => exact ⟨term, .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨middle, earlier, rfl⟩ := ih
      obtain ⟨recovered, later, image⟩ := step_reflects reflects step rho injective middle rfl
      exact ⟨recovered, earlier.tail later, image⟩

end ContextualDependentReductionReflection
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
