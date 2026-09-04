import Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.BinderOps
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge

theorem closeFVar_zero_injective_test {x : String} {p q : Pattern}
    (hp : lc_at 0 p = true) (hq : lc_at 0 q = true)
    (h : closeFVar 0 x p = closeFVar 0 x q) : p = q := by
  have hopen := congrArg (openBVar 0 (.fvar x)) h
  simpa [openBVar_closeBVar_cancel hp, openBVar_closeBVar_cancel hq] using hopen

theorem quoteExactWith_injective_test
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hρ : Function.Injective ρ) (hcompat : QuoteCompat ν k ρ) :
    Function.Injective (quoteExactWith ν k ρ) := by
  intro t u heq
  induction t generalizing k with
  | var i =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact hρ heq
  | const c =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact quoteDeclName_injective heq
  | u0 =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
  | u1 =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
  | pi A B ihA ihB =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      rename_i A' B'
      rcases heq with ⟨hA, hB⟩
      refine ⟨ihA hρ hcompat hA, ?_⟩
      have hopened := closeFVar_zero_injective_test
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) B)
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) B') hB
      exact ihB (envCons_injective_of_injective_of_compat hρ hcompat)
        (QuoteCompat.envCons hcompat.1 hcompat) hopened
  | sigma A B ihA ihB =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      rename_i A' B'
      rcases heq with ⟨hA, hB⟩
      refine ⟨ihA hρ hcompat hA, ?_⟩
      have hopened := closeFVar_zero_injective_test
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) B)
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) B') hB
      exact ihB (envCons_injective_of_injective_of_compat hρ hcompat)
        (QuoteCompat.envCons hcompat.1 hcompat) hopened
  | id A a b ihA iha ihb =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ⟨ihA hρ hcompat heq.1,
        iha hρ hcompat heq.2.1, ihb hρ hcompat heq.2.2⟩
  | lam body ih =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      rename_i body'
      have hopened := closeFVar_zero_injective_test
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) body)
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) body') heq
      exact ih (envCons_injective_of_injective_of_compat hρ hcompat)
        (QuoteCompat.envCons hcompat.1 hcompat) hopened
  | app f a ihf iha =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ⟨ihf hρ hcompat heq.1, iha hρ hcompat heq.2⟩
  | pair a b iha ihb =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ⟨iha hρ hcompat heq.1, ihb hρ hcompat heq.2⟩
  | fst p ih =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ih hρ hcompat heq
  | snd p ih =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ih hρ hcompat heq
  | refl a ih =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ih hρ hcompat heq

theorem quoteTmWith_injective_of_constantFree_test
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hρ : Function.Injective ρ) (hcompat : QuoteCompat ν k ρ)
    {t u : PureTm n} (ht : ConstantFree t) (hu : ConstantFree u)
    (h : quoteTmWith ν k ρ t = quoteTmWith ν k ρ u) : t = u := by
  apply quoteExactWith_injective_test hρ hcompat
  rw [quoteExactWith_eq_quoteTmWith ht, quoteExactWith_eq_quoteTmWith hu]
  exact h

theorem RegularCtx.constantFreeCtx_test {Γ : Ctx n} (hΓ : RegularCtx Γ) :
    ConstantFreeCtx Γ := by
  induction hΓ with
  | nil => trivial
  | snoc hΓ hA ih =>
      exact ⟨ih, (hA.constantFree_both ih).1⟩

theorem quotePureCtx_injective_test
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hρ : Function.Injective ρ) (hcompat : QuoteCompat ν k ρ)
    {Γ Δ : Ctx n} (hΓ : RegularCtx Γ) (hΔ : RegularCtx Δ)
    (h : quotePureCtx ν k ρ Γ = quotePureCtx ν k ρ Δ) : Γ = Δ := by
  induction hΓ with
  | nil =>
      cases hΔ
      rfl
  | @snoc n Γ A hΓ hA ih =>
      cases hΔ with
      | @snoc _ Δ B hΔ hB =>
          let ρtail : QuoteEnv n := fun i => ρ i.succ
          have hρtail : Function.Injective ρtail := by
            intro i j hij
            exact Fin.succ_inj.mp (hρ hij)
          have hcompatTail : QuoteCompat ν k ρtail := by
            refine ⟨hcompat.1, ?_⟩
            intro i j hj
            exact hcompat.2 i.succ j hj
          have hparts := List.cons.inj h
          have htypes : quoteTmWith ν k ρtail A = quoteTmWith ν k ρtail B :=
            congrArg Prod.snd hparts.1
          have hcfΓ := RegularCtx.constantFreeCtx_test hΓ
          have hcfΔ := RegularCtx.constantFreeCtx_test hΔ
          have hAB := quoteTmWith_injective_of_constantFree_test hρtail hcompatTail
            (hA.constantFree_both hcfΓ).1 (hB.constantFree_both hcfΔ).1 htypes
          have hΓΔ := ih hρtail hcompatTail hΔ hparts.2
          exact congrArg₂ Ctx.snoc hΓΔ hAB

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
