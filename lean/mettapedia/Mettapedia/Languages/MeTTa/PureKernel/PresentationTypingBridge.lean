import Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

/-!
# The regular intrinsic/Pattern Pure typing bridge

This module maps fragment-internal intrinsic reduction and conversion into the
locally nameless Pattern presentation.  Cofinite binder cases are transported
by the proved substitution principle, so no alpha-equivalence axiom or chosen
fresh-name convention enters the bridge.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationTypingBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.BinderOps
open Mettapedia.Languages.MeTTa.Pure.Fragment
open Mettapedia.Languages.MeTTa.Pure.Typing
open Mettapedia.Languages.MeTTa.Pure.SubjectReduction
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

/-- The intrinsic beta rule is mapped to Pattern beta conversion, with the
kernel `inst0`/locally-nameless opening square discharged explicitly. -/
theorem betaPi_quote
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

/-- Every fragment-internal intrinsic reduction step becomes Pattern
definitional equality, and its target remains declaration-free. -/
theorem red_quote
    {ν : Nat → String} (hinst0 : Inst0OpenBridgeCompat ν)
    {t u : PureTm n} (hred : Red t u) (ht : ConstantFree t)
    (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat ν k ρ) :
    PureConv (quoteTmWith ν k ρ t) (quoteTmWith ν k ρ u) ∧ ConstantFree u := by
  induction hred generalizing k with
  | betaPi body a =>
      cases ht with
      | app hlam ha =>
        cases hlam with
        | lam hbody => exact ⟨betaPi_quote hinst0 hbody ha k ρ hcompat, ha.inst0 hbody⟩
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
            (PureConv.congPi (L := ∅) hARefl (fun _ _ =>
              pureConv_openBVar_change_name hcanon
                (isFresh_closeFVar_self 0 (ν k) qB)
                (isFresh_closeFVar_self 0 (ν k) qB'))), .pi hAcf hB'cf⟩
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
            (PureConv.congSigma (L := ∅) hARefl (fun _ _ =>
              pureConv_openBVar_change_name hcanon
                (isFresh_closeFVar_self 0 (ν k) qB)
                (isFresh_closeFVar_self 0 (ν k) qB'))), .sigma hAcf hB'cf⟩
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
            (PureConv.congLam (L := ∅) (fun _ _ =>
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

/-- Fragment-internal intrinsic conversion maps to Pattern conversion.  The
source/target edge witnesses in `ConstantFreeConv` are exactly what make every
recursive proof-fibre step representable. -/
theorem conv_quote
    {ν : Nat → String} (hinst0 : Inst0OpenBridgeCompat ν)
    {t u : PureTm n} (hconv : ConstantFreeConv t u)
    (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat ν k ρ) :
    PureConv (quoteTmWith ν k ρ t) (quoteTmWith ν k ρ u) := by
  induction hconv with
  | rel hstep => exact (red_quote hinst0 hstep.1 hstep.2.1 k ρ hcompat).1
  | refl x hx => exact .refl _ (quoteTmWith_pure hx ν k ρ)
  | symm hxy ih => exact .symm ih
  | trans hxy hyz ihxy ihyz => exact .trans ihxy ihyz

/-- Quoting an intrinsic telescope one level below a binder gives exactly the
locally nameless extended context expected by Pattern typing. -/
theorem quotePureCtx_snoc_next
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (Γ : Ctx n) (A : PureTm n) :
    quotePureCtx ν (k + 1) (envCons (ν k) ρ) (.snoc Γ A) =
      (ν k, quoteTmWith ν k ρ A) :: quotePureCtx ν k ρ Γ := by
  have hnext : QuoteCompat ν (k + 1) ρ :=
    Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary.QuoteCompat.mono
      hcompat (by omega)
  simp only [quotePureCtx_snoc]
  change (ν k, quoteTmWith ν (k + 1) ρ A) :: quotePureCtx ν (k + 1) ρ Γ = _
  rw [quoteTmWith_depth_indep hnext hcompat A]
  rw [quotePureCtx_depth_indep hnext hcompat Γ]

/-- The regular intrinsic spine is preserved by contextual quotation into the
Pattern Pure presentation.  The theorem is parameterized by the proven
`inst0` bridge and a compatible naming environment; no chosen binder name is
trusted by the typing relation. -/
theorem regularHasType_quote
    {ν : Nat → String} (hinst0 : Inst0OpenBridgeCompat ν)
    {Γ : Ctx n} {t A : PureTm n} (h : RegularHasType Γ t A)
    (hΓ : ConstantFreeCtx Γ)
    (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat ν k ρ) :
    PureHasType (quotePureCtx ν k ρ Γ)
      (quoteTmWith ν k ρ t) (quoteTmWith ν k ρ A) := by
  induction h generalizing k with
  | u0_type Γ => exact .u0_type _
  | @var n Γ i =>
      exact .fvar _ (ρ i) (quoteTmWith ν k ρ (lookup Γ i))
        (quote_lookup_mem ν k ρ Γ i)
        (quoteTmWith_pure (hΓ.lookup i) ν k ρ)
        (lc_quoteTmWith ν k ρ (lookup Γ i))
  | @pi_form n Γ A B hA hB ihA ihB =>
      have hAcf := (RegularHasType.constantFree_both hA hΓ).1
      have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
      have hAq := ihA hΓ k ρ hcompat
      have hBq := ihB ⟨hΓ, hAcf⟩ (k + 1) (envCons (ν k) ρ) hcompat'
      rw [quotePureCtx_snoc_next hcompat Γ A] at hBq
      let qA := quoteTmWith ν k ρ A
      let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
      let closedB := closeFVar 0 (ν k) qB
      have hcanon : PureHasType
          ((ν k, qA) :: quotePureCtx ν k ρ Γ)
          (openBVar 0 (.fvar (ν k)) closedB) u1 := by
        simpa [qA, qB, closedB,
          openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B),
          quoteTmWith, u1] using hBq
      have hcanonOpen : PureHasType
          ((ν k, qA) :: quotePureCtx ν k ρ Γ)
          (openBVar 0 (.fvar (ν k)) closedB)
          (openBVar 0 (.fvar (ν k)) u1) := by
        simpa [u1, openBVar] using hcanon
      refine .pi_form _ {ν k} qA closedB u1 (by simpa [qA, quoteTmWith] using hAq) ?_
      intro x hx
      have hchanged := typing_openBVar_change_name
        (A := qA) (body := closedB) (B := u1)
        (old := ν k) (fresh := x)
        (by simpa [qA] using quoteTmWith_pure hAcf ν k ρ)
        (by simpa [qA] using lc_quoteTmWith ν k ρ A) hcanonOpen
        (quotePureCtx_current_not_mem_ctxNames hcompat Γ)
        (isFresh_quoteTmWith_future hcompat A (j := k) (by omega))
        (quotePureCtx_current_fresh hcompat Γ)
        (isFresh_closeFVar_self 0 (ν k) qB)
        (by simp [u1, isFresh, freeVars]) (by
          intro heq
          subst heq
          exact hx (by simp))
      simpa [u1, openBVar] using hchanged
  | @sigma_form n Γ A B hA hB ihA ihB =>
      have hAcf := (RegularHasType.constantFree_both hA hΓ).1
      have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
      have hAq := ihA hΓ k ρ hcompat
      have hBq := ihB ⟨hΓ, hAcf⟩ (k + 1) (envCons (ν k) ρ) hcompat'
      rw [quotePureCtx_snoc_next hcompat Γ A] at hBq
      let qA := quoteTmWith ν k ρ A
      let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
      let closedB := closeFVar 0 (ν k) qB
      have hcanon : PureHasType
          ((ν k, qA) :: quotePureCtx ν k ρ Γ)
          (openBVar 0 (.fvar (ν k)) closedB) u1 := by
        simpa [qA, qB, closedB,
          openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B),
          quoteTmWith, u1] using hBq
      have hcanonOpen : PureHasType
          ((ν k, qA) :: quotePureCtx ν k ρ Γ)
          (openBVar 0 (.fvar (ν k)) closedB)
          (openBVar 0 (.fvar (ν k)) u1) := by
        simpa [u1, openBVar] using hcanon
      refine .sigma_form _ {ν k} qA closedB u1
        (by simpa [qA, quoteTmWith] using hAq) ?_
      intro x hx
      have hchanged := typing_openBVar_change_name
        (A := qA) (body := closedB) (B := u1)
        (old := ν k) (fresh := x)
        (by simpa [qA] using quoteTmWith_pure hAcf ν k ρ)
        (by simpa [qA] using lc_quoteTmWith ν k ρ A) hcanonOpen
        (quotePureCtx_current_not_mem_ctxNames hcompat Γ)
        (isFresh_quoteTmWith_future hcompat A (j := k) (by omega))
        (quotePureCtx_current_fresh hcompat Γ)
        (isFresh_closeFVar_self 0 (ν k) qB)
        (by simp [u1, isFresh, freeVars]) (by
          intro heq
          subst heq
          exact hx (by simp))
      simpa [u1, openBVar] using hchanged
  | @lam_intro n Γ A body B hA hB hBody ihA ihB ihBody =>
      have hAcf := (RegularHasType.constantFree_both hA hΓ).1
      have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
      have hAq := ihA hΓ k ρ hcompat
      have hBodyq := ihBody ⟨hΓ, hAcf⟩ (k + 1) (envCons (ν k) ρ) hcompat'
      rw [quotePureCtx_snoc_next hcompat Γ A] at hBodyq
      let qA := quoteTmWith ν k ρ A
      let qbody := quoteTmWith ν (k + 1) (envCons (ν k) ρ) body
      let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
      let closedBody := closeFVar 0 (ν k) qbody
      let closedB := closeFVar 0 (ν k) qB
      have hcanon : PureHasType
          ((ν k, qA) :: quotePureCtx ν k ρ Γ)
          (openBVar 0 (.fvar (ν k)) closedBody)
          (openBVar 0 (.fvar (ν k)) closedB) := by
        simpa [qA, qbody, qB, closedBody, closedB,
          openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ body),
          openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B)] using hBodyq
      refine .lam_intro _ {ν k} qA closedBody closedB u1
        (by simpa [qA, quoteTmWith] using hAq) ?_
      intro x hx
      apply typing_openBVar_change_name
        (by simpa [qA] using quoteTmWith_pure hAcf ν k ρ)
        (by simpa [qA] using lc_quoteTmWith ν k ρ A) hcanon
      · exact quotePureCtx_current_not_mem_ctxNames hcompat Γ
      · exact isFresh_quoteTmWith_future hcompat A (j := k) (by omega)
      · exact quotePureCtx_current_fresh hcompat Γ
      · exact isFresh_closeFVar_self 0 (ν k) qbody
      · exact isFresh_closeFVar_self 0 (ν k) qB
      · intro heq
        subst heq
        exact hx (by simp)
  | @app_elim n Γ f a A B hA hf ha hB ihA ihf iha ihB =>
      have hAcf := (RegularHasType.constantFree_both hA hΓ).1
      have hfq := ihf hΓ k ρ hcompat
      have haq := iha hΓ k ρ hcompat
      have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
      have hBq := ihB ⟨hΓ, hAcf⟩ (k + 1) (envCons (ν k) ρ) hcompat'
      rw [quotePureCtx_snoc_next hcompat Γ A] at hBq
      let qA := quoteTmWith ν k ρ A
      let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
      let closedB := closeFVar 0 (ν k) qB
      have hcanon : PureHasType
          ((ν k, qA) :: quotePureCtx ν k ρ Γ)
          (openBVar 0 (.fvar (ν k)) closedB) u1 := by
        simpa [qA, qB, closedB,
          openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B),
          quoteTmWith, u1] using hBq
      have hforall : ∀ x, x ∉ ({ν k} : Finset String) →
          PureHasType ((x, qA) :: quotePureCtx ν k ρ Γ)
            (openBVar 0 (.fvar x) closedB) u1 := by
        intro x hx
        have hcanonOpen : PureHasType
            ((ν k, qA) :: quotePureCtx ν k ρ Γ)
            (openBVar 0 (.fvar (ν k)) closedB)
            (openBVar 0 (.fvar (ν k)) u1) := by
          simpa [u1, openBVar] using hcanon
        have hchanged := typing_openBVar_change_name
          (A := qA) (body := closedB) (B := u1)
          (old := ν k) (fresh := x)
          (by simpa [qA] using quoteTmWith_pure hAcf ν k ρ)
          (by simpa [qA] using lc_quoteTmWith ν k ρ A) hcanonOpen
          (quotePureCtx_current_not_mem_ctxNames hcompat Γ)
          (isFresh_quoteTmWith_future hcompat A (j := k) (by omega))
          (quotePureCtx_current_fresh hcompat Γ)
          (isFresh_closeFVar_self 0 (ν k) qB)
          (by simp [u1, isFresh, freeVars]) (by
            intro heq
            subst heq
            exact hx (by simp))
        simpa [u1, openBVar] using hchanged
      have happ : PureHasType (quotePureCtx ν k ρ Γ)
          (mkApp (quoteTmWith ν k ρ f) (quoteTmWith ν k ρ a))
          (openBVar 0 (quoteTmWith ν k ρ a) closedB) :=
        .app _ {ν k} _ _ qA closedB u1
          (by simpa [qA, qB, closedB, quoteTmWith] using hfq)
          (by simpa [qA] using haq) hforall
      rw [hinst0 k ρ a B hcompat]
      simpa [quoteTmWith, qB, closedB] using happ
  | @pair_intro n Γ a b A B hA ha hb hB ihA iha ihb ihB =>
      have hAcf := (RegularHasType.constantFree_both hA hΓ).1
      have haq := iha hΓ k ρ hcompat
      have hbq := ihb hΓ k ρ hcompat
      have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
      have hBq := ihB ⟨hΓ, hAcf⟩ (k + 1) (envCons (ν k) ρ) hcompat'
      rw [quotePureCtx_snoc_next hcompat Γ A] at hBq
      let qA := quoteTmWith ν k ρ A
      let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
      let closedB := closeFVar 0 (ν k) qB
      have hcanon : PureHasType ((ν k, qA) :: quotePureCtx ν k ρ Γ)
          (openBVar 0 (.fvar (ν k)) closedB) u1 := by
        simpa [qA, qB, closedB,
          openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B),
          quoteTmWith, u1] using hBq
      have hforall : ∀ x, x ∉ ({ν k} : Finset String) →
          PureHasType ((x, qA) :: quotePureCtx ν k ρ Γ)
            (openBVar 0 (.fvar x) closedB) u1 := by
        intro x hx
        have hcanonOpen : PureHasType ((ν k, qA) :: quotePureCtx ν k ρ Γ)
            (openBVar 0 (.fvar (ν k)) closedB)
            (openBVar 0 (.fvar (ν k)) u1) := by simpa [u1, openBVar] using hcanon
        have hchanged := typing_openBVar_change_name
          (A := qA) (body := closedB) (B := u1)
          (old := ν k) (fresh := x)
          (by simpa [qA] using quoteTmWith_pure hAcf ν k ρ)
          (by simpa [qA] using lc_quoteTmWith ν k ρ A) hcanonOpen
          (quotePureCtx_current_not_mem_ctxNames hcompat Γ)
          (isFresh_quoteTmWith_future hcompat A (j := k) (by omega))
          (quotePureCtx_current_fresh hcompat Γ)
          (isFresh_closeFVar_self 0 (ν k) qB)
          (by simp [u1, isFresh, freeVars]) (by
            intro heq
            subst heq
            exact hx (by simp))
        simpa [u1, openBVar] using hchanged
      have hinst := hinst0 k ρ a B hcompat
      have hbq' : PureHasType (quotePureCtx ν k ρ Γ)
          (quoteTmWith ν k ρ b)
          (openBVar 0 (quoteTmWith ν k ρ a) closedB) := by
        rw [← hinst]
        exact hbq
      exact .pair_intro _ {ν k} _ _ qA closedB u1
        (by simpa [qA] using haq) hbq' hforall
  | @fst_elim n Γ p A B hA hp hB ihA ihp ihB =>
      have hAcf := (RegularHasType.constantFree_both hA hΓ).1
      have hpq := ihp hΓ k ρ hcompat
      have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
      have hBq := ihB ⟨hΓ, hAcf⟩ (k + 1) (envCons (ν k) ρ) hcompat'
      rw [quotePureCtx_snoc_next hcompat Γ A] at hBq
      let qA := quoteTmWith ν k ρ A
      let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
      let closedB := closeFVar 0 (ν k) qB
      have hcanon : PureHasType ((ν k, qA) :: quotePureCtx ν k ρ Γ)
          (openBVar 0 (.fvar (ν k)) closedB) u1 := by
        simpa [qA, qB, closedB,
          openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B),
          quoteTmWith, u1] using hBq
      have hforall : ∀ x, x ∉ ({ν k} : Finset String) →
          PureHasType ((x, qA) :: quotePureCtx ν k ρ Γ)
            (openBVar 0 (.fvar x) closedB) u1 := by
        intro x hx
        have hcanonOpen : PureHasType
            ((ν k, qA) :: quotePureCtx ν k ρ Γ)
            (openBVar 0 (.fvar (ν k)) closedB)
            (openBVar 0 (.fvar (ν k)) u1) := by
          simpa [u1, openBVar] using hcanon
        have hchanged := typing_openBVar_change_name
          (A := qA) (body := closedB) (B := u1)
          (old := ν k) (fresh := x)
          (by simpa [qA] using quoteTmWith_pure hAcf ν k ρ)
          (by simpa [qA] using lc_quoteTmWith ν k ρ A)
          hcanonOpen
          (quotePureCtx_current_not_mem_ctxNames hcompat Γ)
          (isFresh_quoteTmWith_future hcompat A (j := k) (by omega))
          (quotePureCtx_current_fresh hcompat Γ)
          (isFresh_closeFVar_self 0 (ν k) qB)
          (by simp [u1, isFresh, freeVars]) (by
            intro heq; subst heq; exact hx (by simp))
        simpa [u1, openBVar] using hchanged
      exact .fst_elim _ {ν k} _ qA closedB u1
        (by simpa [qA, qB, closedB, quoteTmWith] using hpq) hforall
  | @snd_elim n Γ p A B hA hp hB ihA ihp ihB =>
      have hAcf := (RegularHasType.constantFree_both hA hΓ).1
      have hpq := ihp hΓ k ρ hcompat
      have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
      have hBq := ihB ⟨hΓ, hAcf⟩ (k + 1) (envCons (ν k) ρ) hcompat'
      rw [quotePureCtx_snoc_next hcompat Γ A] at hBq
      let qA := quoteTmWith ν k ρ A
      let qB := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B
      let closedB := closeFVar 0 (ν k) qB
      have hcanon : PureHasType ((ν k, qA) :: quotePureCtx ν k ρ Γ)
          (openBVar 0 (.fvar (ν k)) closedB) u1 := by
        simpa [qA, qB, closedB,
          openBVar_closeBVar_cancel (lc_quoteTmWith ν (k + 1) _ B),
          quoteTmWith, u1] using hBq
      have hforall : ∀ x, x ∉ ({ν k} : Finset String) →
          PureHasType ((x, qA) :: quotePureCtx ν k ρ Γ)
            (openBVar 0 (.fvar x) closedB) u1 := by
        intro x hx
        have hcanonOpen : PureHasType
            ((ν k, qA) :: quotePureCtx ν k ρ Γ)
            (openBVar 0 (.fvar (ν k)) closedB)
            (openBVar 0 (.fvar (ν k)) u1) := by
          simpa [u1, openBVar] using hcanon
        have hchanged := typing_openBVar_change_name
          (A := qA) (body := closedB) (B := u1)
          (old := ν k) (fresh := x)
          (by simpa [qA] using quoteTmWith_pure hAcf ν k ρ)
          (by simpa [qA] using lc_quoteTmWith ν k ρ A) hcanonOpen
          (quotePureCtx_current_not_mem_ctxNames hcompat Γ)
          (isFresh_quoteTmWith_future hcompat A (j := k) (by omega))
          (quotePureCtx_current_fresh hcompat Γ)
          (isFresh_closeFVar_self 0 (ν k) qB)
          (by simp [u1, isFresh, freeVars]) (by
            intro heq; subst heq; exact hx (by simp))
        simpa [u1, openBVar] using hchanged
      have hsnd : PureHasType (quotePureCtx ν k ρ Γ)
          (mkSnd (quoteTmWith ν k ρ p))
          (openBVar 0 (mkFst (quoteTmWith ν k ρ p)) closedB) :=
        .snd_elim _ {ν k} _ qA closedB u1
          (by simpa [qA, qB, closedB, quoteTmWith] using hpq) hforall
      rw [hinst0 k ρ (.fst p) B hcompat]
      simpa [quoteTmWith, qB, closedB] using hsnd
  | @id_form n Γ A a b hA ha hb ihA iha ihb =>
      exact .id_form _ _ _ _ u1
        (by simpa [quoteTmWith] using ihA hΓ k ρ hcompat)
        (iha hΓ k ρ hcompat) (ihb hΓ k ρ hcompat)
  | @refl_intro n Γ a A hA ha ihA iha =>
      exact .refl_intro _ _ _ (iha hΓ k ρ hcompat)
  | @conv_type n Γ t A B ht hB hconv iht ihB =>
      exact .conv _ _ _ _ (iht hΓ k ρ hcompat)
        (conv_quote hinst0 hconv k ρ hcompat)
  | @conv_sort n Γ t A ht hconv iht =>
      exact .conv _ _ _ _ (iht hΓ k ρ hcompat)
        (conv_quote hinst0 hconv k ρ hcompat)

/-- The full presupposition-closed judgment boundary is preserved by the
presentation map.  Context formation remains explicit in the source theorem;
the Pattern target receives its concrete association-list context. -/
theorem regularJudgment_quote
    {ν : Nat → String} (hinst0 : Inst0OpenBridgeCompat ν)
    {Γ : Ctx n} {t A : PureTm n} (h : RegularJudgment Γ t A)
    (hΓ : ConstantFreeCtx Γ)
    (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat ν k ρ) :
    PureHasType (quotePureCtx ν k ρ Γ)
      (quoteTmWith ν k ρ t) (quoteTmWith ν k ρ A) :=
  regularHasType_quote hinst0 h.typing hΓ k ρ hcompat

/-- Positive nondegeneracy canary: the derived intrinsic identity judgment
crosses the actual quotation theorem into Pattern Pure. -/
theorem regular_identity_quotes
    {ν : Nat → String} (hinst0 : Inst0OpenBridgeCompat ν)
    (hν : Function.Injective ν) :
    PureHasType []
      (quoteTmWith ν 0 emptyEnv (.lam (.var 0)))
      (quoteTmWith ν 0 emptyEnv (.pi .u0 .u0)) := by
  exact regularJudgment_quote hinst0 regular_identity_judgment trivial
    0 emptyEnv (quoteCompat_empty ν hν 0)

/-! ## Why the reverse square needs a regular Pattern boundary -/

/-- The authored Pattern judgment permits conversion to a pure, locally
closed beta-redex even when that redex is not itself a well-formed type.  This
is a positive witness for the permissive conversion rule, not a defect in
beta conversion. -/
theorem pattern_accepts_conversion_to_unformed_type :
    PureHasType [] u0 (mkApp (mkLam u1) u0) := by
  apply PureHasType.conv [] u0 u1
  · exact .u0_type []
  · have hbeta := PureConv.betaPi u1 u0 .u1 .u0 (by rfl) (by rfl)
    simpa [openBVar, u1] using PureConv.symm hbeta

/-- The counterexample is in the exact image of the common intrinsic syntax;
it is not caused by global constants or by the legacy string quotation. -/
theorem untypedBetaType_quotes
    (ν : Nat → String) :
    quoteTmWith ν 0 emptyEnv
      Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary.untypedBetaType =
        mkApp (mkLam u1) u0 := by
  simp [Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary.untypedBetaType,
    quoteTmWith, mkApp, mkLam, u0, u1, closeFVar]

/-- Hence unrestricted reflection from the authored Pattern typing judgment
to the regular intrinsic kernel is false even on the exact common syntax.
The reverse presentation theorem must first make type-formation
presuppositions intrinsic on the Pattern side (or elaborate into the regular
intrinsic kernel). -/
theorem authored_pattern_does_not_reflect_regular
    (ν : Nat → String) :
    PureHasType [] u0 (quoteTmWith ν 0 emptyEnv
      Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary.untypedBetaType) ∧
      ¬ RegularHasType (.nil : Ctx 0) .u0
        Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary.untypedBetaType := by
  rw [untypedBetaType_quotes]
  exact ⟨pattern_accepts_conversion_to_unformed_type,
    Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary.regular_rejects_conversion_to_unformed_type⟩

end Mettapedia.Languages.MeTTa.PureKernel.PresentationTypingBridge
