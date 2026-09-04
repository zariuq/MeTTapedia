import Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.BinderOps
open Mettapedia.Languages.MeTTa.Pure.Fragment
open Mettapedia.Languages.MeTTa.Pure.Typing
open Mettapedia.Languages.MeTTa.Pure.SubjectReduction
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge

theorem red_beta_quote_test
    {ν : Nat → String} (hinst0 : Inst0OpenBridgeCompat ν)
    {body : PureTm (n + 1)} {a : PureTm n}
    (hbody : ConstantFree body) (ha : ConstantFree a)
    (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat ν k ρ) :
    PureConv (quoteTmWith ν k ρ (.app (.lam body) a))
      (quoteTmWith ν k ρ (inst0 a body)) := by
  let qbody := quoteTmWith ν (k + 1) (envCons (ν k) ρ) body
  let qclosed := closeFVar 0 (ν k) qbody
  let qa := quoteTmWith ν k ρ a
  have hbodyPure : PureTmPattern qbody := quoteTmWith_pure hbody _ _ _
  have hclosedPure : PureTmPattern qclosed := pureTm_closeBVar (ν k) hbodyPure
  have haPure : PureTmPattern qa := quoteTmWith_pure ha _ _ _
  have hbody0 : lc_at 0 qbody = true := lc_quoteTmWith ν (k + 1) _ body
  have hbody1 : lc_at 1 qbody = true := lc_at_mono hbody0 (Nat.zero_le 1)
  have hclosed1 : lc_at 1 qclosed = true :=
    lc_at_closeFVar_of_lt (k := 1) (l := 0) (ν k) qbody (by omega) hbody1
  have ha0 : lc_at 0 qa = true := lc_quoteTmWith ν k ρ a
  have hbeta : PureConv (mkApp (mkLam qclosed) qa) (openBVar 0 qa qclosed) :=
    .betaPi qclosed qa hclosedPure haPure hclosed1 ha0
  rw [hinst0 k ρ a body hcompat]
  exact hbeta

theorem red_quote_test
    {ν : Nat → String} (hinst0 : Inst0OpenBridgeCompat ν)
    {t u : PureTm n} (hred : Red t u) (ht : ConstantFree t)
    (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat ν k ρ) :
    PureConv (quoteTmWith ν k ρ t) (quoteTmWith ν k ρ u) ∧ ConstantFree u := by
  induction hred generalizing k with
  | betaPi body a =>
      cases ht with
      | app hlam ha =>
        cases hlam with
        | lam hbody =>
          exact ⟨red_beta_quote_test hinst0 hbody ha k ρ hcompat,
            ha.inst0 hbody⟩
  | betaSigmaFst a b =>
      cases ht with
      | fst hpair =>
        cases hpair with
        | pair ha hb =>
          exact ⟨by
            simpa [quoteTmWith] using
              (PureConv.betaSigmaFst
                (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)
                (quoteTmWith_pure ha _ _ _) (quoteTmWith_pure hb _ _ _)
                (lc_quoteTmWith ν k ρ a) (lc_quoteTmWith ν k ρ b)), ha⟩
  | betaSigmaSnd a b =>
      cases ht with
      | snd hpair =>
        cases hpair with
        | pair ha hb =>
          exact ⟨by
            simpa [quoteTmWith] using
              (PureConv.betaSigmaSnd
                (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)
                (quoteTmWith_pure ha _ _ _) (quoteTmWith_pure hb _ _ _)
                (lc_quoteTmWith ν k ρ a) (lc_quoteTmWith ν k ρ b)), hb⟩
  | @congPiDom n A A' B hA ih =>
      cases ht with
      | pi hAcf hBcf =>
        obtain ⟨hconv, hA'cf⟩ := ih hAcf k ρ hcompat
        let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
        let closedB := closeFVar 0 (ν k) qB
        have hpureClosed : PureTmPattern closedB :=
          pureTm_closeBVar (ν k) (quoteTmWith_pure hBcf _ _ _)
        exact ⟨by
          simpa [quoteTmWith, qB, closedB] using
            (PureConv.congPi (L := ∅) hconv
              (fun x _ => .refl _ (pureTm_openBVar (.fvar x) hpureClosed))),
          .pi hA'cf hBcf⟩
  | @congPiCod n A B B' hB ih =>
      cases ht with
      | pi hAcf hBcf =>
        have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
        obtain ⟨hconv, hB'cf⟩ := ih hBcf (k + 1) (envCons (ν k) ρ) hcompat'
        let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
        let qB' := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B'
        let closedB := closeFVar 0 (ν k) qB
        let closedB' := closeFVar 0 (ν k) qB'
        have hcanon : PureConv
            (openBVar 0 (.fvar (ν k)) closedB)
            (openBVar 0 (.fvar (ν k)) closedB') := by
          simpa [qB, qB', closedB, closedB',
            openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B),
            openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B')] using hconv
        have hARefl : PureConv (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ A) :=
          .refl _ (quoteTmWith_pure hAcf _ _ _)
        exact ⟨by
          simpa [quoteTmWith, qB, qB', closedB, closedB'] using
            (PureConv.congPi (L := ∅) hARefl (fun x _ =>
              pureConv_openBVar_change_name hcanon
                (isFresh_closeFVar_self 0 (ν k) qB)
                (isFresh_closeFVar_self 0 (ν k) qB'))),
          .pi hAcf hB'cf⟩
  | @congSigmaDom n A A' B hA ih =>
      cases ht with
      | sigma hAcf hBcf =>
        obtain ⟨hconv, hA'cf⟩ := ih hAcf k ρ hcompat
        let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
        let closedB := closeFVar 0 (ν k) qB
        have hpureClosed : PureTmPattern closedB :=
          pureTm_closeBVar (ν k) (quoteTmWith_pure hBcf _ _ _)
        exact ⟨by
          simpa [quoteTmWith, qB, closedB] using
            (PureConv.congSigma (L := ∅) hconv
              (fun x _ => .refl _ (pureTm_openBVar (.fvar x) hpureClosed))),
          .sigma hA'cf hBcf⟩
  | @congSigmaCod n A B B' hB ih =>
      cases ht with
      | sigma hAcf hBcf =>
        have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
        obtain ⟨hconv, hB'cf⟩ := ih hBcf (k + 1) (envCons (ν k) ρ) hcompat'
        let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
        let qB' := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B'
        let closedB := closeFVar 0 (ν k) qB
        let closedB' := closeFVar 0 (ν k) qB'
        have hcanon : PureConv
            (openBVar 0 (.fvar (ν k)) closedB)
            (openBVar 0 (.fvar (ν k)) closedB') := by
          simpa [qB, qB', closedB, closedB',
            openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B),
            openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B')] using hconv
        have hARefl : PureConv (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ A) :=
          .refl _ (quoteTmWith_pure hAcf _ _ _)
        exact ⟨by
          simpa [quoteTmWith, qB, qB', closedB, closedB'] using
            (PureConv.congSigma (L := ∅) hARefl (fun x _ =>
              pureConv_openBVar_change_name hcanon
                (isFresh_closeFVar_self 0 (ν k) qB)
                (isFresh_closeFVar_self 0 (ν k) qB'))),
          .sigma hAcf hB'cf⟩
  | @congIdTy n A A' a b hA ih =>
      cases ht with
      | id hAcf hacf hbcf =>
        obtain ⟨hconv, hA'cf⟩ := ih hAcf k ρ hcompat
        exact ⟨by simpa [quoteTmWith] using (PureConv.congId hconv
          (.refl _ (quoteTmWith_pure hacf _ _ _))
          (.refl _ (quoteTmWith_pure hbcf _ _ _))), .id hA'cf hacf hbcf⟩
  | @congIdLeft n A a a' b ha ih =>
      cases ht with
      | id hAcf hacf hbcf =>
        obtain ⟨hconv, ha'cf⟩ := ih hacf k ρ hcompat
        exact ⟨by simpa [quoteTmWith] using (PureConv.congId
          (.refl _ (quoteTmWith_pure hAcf _ _ _)) hconv
          (.refl _ (quoteTmWith_pure hbcf _ _ _))), .id hAcf ha'cf hbcf⟩
  | @congIdRight n A a b b' hb ih =>
      cases ht with
      | id hAcf hacf hbcf =>
        obtain ⟨hconv, hb'cf⟩ := ih hbcf k ρ hcompat
        exact ⟨by simpa [quoteTmWith] using (PureConv.congId
          (.refl _ (quoteTmWith_pure hAcf _ _ _))
          (.refl _ (quoteTmWith_pure hacf _ _ _)) hconv), .id hAcf hacf hb'cf⟩
  | @congLam n b b' hb ih =>
      cases ht with
      | lam hbcf =>
        have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
        obtain ⟨hconv, hb'cf⟩ := ih hbcf (k + 1) (envCons (ν k) ρ) hcompat'
        let qb := quoteTmWith ν (k + 1) (envCons (ν k) ρ) b
        let qb' := quoteTmWith ν (k + 1) (envCons (ν k) ρ) b'
        let closed := closeFVar 0 (ν k) qb
        let closed' := closeFVar 0 (ν k) qb'
        have hcanon : PureConv
            (openBVar 0 (.fvar (ν k)) closed)
            (openBVar 0 (.fvar (ν k)) closed') := by
          simpa [qb, qb', closed, closed',
            openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ b),
            openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ b')] using hconv
        exact ⟨by
          simpa [quoteTmWith, qb, qb', closed, closed'] using
            (PureConv.congLam (L := ∅) (fun x _ =>
              pureConv_openBVar_change_name hcanon
                (isFresh_closeFVar_self 0 (ν k) qb)
                (isFresh_closeFVar_self 0 (ν k) qb'))), .lam hb'cf⟩
  | @congAppFun n f f' a hf ih =>
      cases ht with
      | app hfcf hacf =>
        obtain ⟨hconv, hf'cf⟩ := ih hfcf k ρ hcompat
        exact ⟨by simpa [quoteTmWith] using (PureConv.congApp hconv
          (.refl _ (quoteTmWith_pure hacf _ _ _))), .app hf'cf hacf⟩
  | @congAppArg n f a a' ha ih =>
      cases ht with
      | app hfcf hacf =>
        obtain ⟨hconv, ha'cf⟩ := ih hacf k ρ hcompat
        exact ⟨by simpa [quoteTmWith] using (PureConv.congApp
          (.refl _ (quoteTmWith_pure hfcf _ _ _)) hconv), .app hfcf ha'cf⟩
  | @congPairFst n a a' b ha ih =>
      cases ht with
      | pair hacf hbcf =>
        obtain ⟨hconv, ha'cf⟩ := ih hacf k ρ hcompat
        exact ⟨by simpa [quoteTmWith] using (PureConv.congPair hconv
          (.refl _ (quoteTmWith_pure hbcf _ _ _))), .pair ha'cf hbcf⟩
  | @congPairSnd n a b b' hb ih =>
      cases ht with
      | pair hacf hbcf =>
        obtain ⟨hconv, hb'cf⟩ := ih hbcf k ρ hcompat
        exact ⟨by simpa [quoteTmWith] using (PureConv.congPair
          (.refl _ (quoteTmWith_pure hacf _ _ _)) hconv), .pair hacf hb'cf⟩
  | @congFst n p p' hp ih =>
      cases ht with
      | fst hpcf =>
        obtain ⟨hconv, hp'cf⟩ := ih hpcf k ρ hcompat
        exact ⟨by simpa [quoteTmWith] using PureConv.congFst hconv, .fst hp'cf⟩
  | @congSnd n p p' hp ih =>
      cases ht with
      | snd hpcf =>
        obtain ⟨hconv, hp'cf⟩ := ih hpcf k ρ hcompat
        exact ⟨by simpa [quoteTmWith] using PureConv.congSnd hconv, .snd hp'cf⟩
  | @congRefl n a a' ha ih =>
      cases ht with
      | refl hacf =>
        obtain ⟨hconv, ha'cf⟩ := ih hacf k ρ hcompat
        exact ⟨by simpa [quoteTmWith] using PureConv.congRefl hconv, .refl ha'cf⟩

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
