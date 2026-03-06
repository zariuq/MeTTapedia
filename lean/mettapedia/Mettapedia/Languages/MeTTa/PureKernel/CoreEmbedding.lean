import Mettapedia.Languages.MeTTa.CoreProfile
import Mettapedia.Languages.MeTTa.PureKernel.TypedLangDef
import Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
import Mettapedia.Languages.MeTTa.PureKernel.Inst0BridgeDerived
import Mettapedia.Languages.MeTTa.PureKernel.Reduction
import Mettapedia.Languages.MeTTa.PureKernel.Renaming
import Mettapedia.Languages.MeTTa.PureKernel.Substitution
import Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# PureKernel Embedding Into MeTTa Core Profiles

Scaffold linking the trusted scoped kernel (`PureTm`) with the MeTTa profile
interface through contextual quotation.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.CoreProfile
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory
open Mettapedia.Languages.MeTTa.PureKernel.Assembly
open Mettapedia.Languages.MeTTa.Pure.Core

/-- Minimal embedding contract for closed PureKernel terms into a MeTTa profile. -/
structure KernelEmbedding where
  profile : MeTTaCoreProfile
  kernel : TypedKernelDef
  quoteClosed : PureTm 0 → Pattern
  quoteClosed_lc : ∀ t, lc_at 0 (quoteClosed t) = true

/-- Canonical embedding of PureKernel into the Pure core profile. -/
def pureKernelIntoPureProfile : KernelEmbedding where
  profile := pureProfile
  kernel := mettaPureKernelTyped
  quoteClosed := quoteClosedTm
  quoteClosed_lc := by
    intro t
    -- `quoteClosedTm` is `quoteTmWith defaultBinderName 0 emptyEnv`.
    simpa [quoteClosedTm, quoteTm, emptyEnv] using
      lc_quoteTmWith defaultBinderName 0 emptyEnv t

theorem pureKernel_embedding_target :
    pureKernelIntoPureProfile.profile.lang.name = "MeTTaPure" := by
  rfl

private def betaPiRule : RewriteRule :=
  { name := "BetaPi",
    typeContext := [("body", .base "Tm"), ("a", .base "Tm")],
    premises := [],
    left := .apply "App" [.apply "Lam" [.lambda (.fvar "body")], .fvar "a"],
    right := .subst (.fvar "body") (.fvar "a") }

private def betaSigmaFstRule : RewriteRule :=
  { name := "BetaSigmaFst",
    typeContext := [("a", .base "Tm"), ("b", .base "Tm")],
    premises := [],
    left := .apply "Fst" [.apply "Pair" [.fvar "a", .fvar "b"]],
    right := .fvar "a" }

private def betaSigmaSndRule : RewriteRule :=
  { name := "BetaSigmaSnd",
    typeContext := [("a", .base "Tm"), ("b", .base "Tm")],
    premises := [],
    left := .apply "Snd" [.apply "Pair" [.fvar "a", .fvar "b"]],
    right := .fvar "b" }

/-- Positive bridge example (βΠ identity): quoted kernel step is a `langReduces` step. -/
theorem langReduces_quoteClosed_betaPi_id (a : PureTm 0) :
    langReduces mettaPure (quoteClosedTm (.app (.lam (.var 0)) a)) (quoteClosedTm a) := by
  apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
  unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
  apply List.mem_append.mpr
  left
  rw [List.mem_flatMap]
  refine ⟨betaPiRule, ?_, ?_⟩
  · simp [betaPiRule, mettaPure]
  · unfold applyRuleWithPremisesUsing
    rw [List.mem_flatMap]
    let qbody : Pattern :=
      closeFVar 0 (defaultBinderName 0) (.fvar (defaultBinderName 0))
    let bs : Bindings := [("a", quoteClosedTm a), ("body", qbody)]
    refine ⟨bs, ?_, ?_⟩
    · simp [bs, qbody, betaPiRule, quoteClosedTm, quoteTm, quoteTmWith,
        mkApp, mkLam, matchPattern, matchArgs, mergeBindings, envCons, emptyEnv]
    · rw [List.mem_map]
      refine ⟨bs, ?_, ?_⟩
      · simp [applyPremisesWithEnv, bs, betaPiRule]
      · simp [bs, qbody, betaPiRule, applyBindings, closeFVar, openBVar]

/-- Positive bridge example (βΣ fst): quoted kernel step is a `langReduces` step. -/
theorem langReduces_quoteClosed_betaSigmaFst (a b : PureTm 0) :
    langReduces mettaPure (quoteClosedTm (.fst (.pair a b))) (quoteClosedTm a) := by
  apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
  unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
  apply List.mem_append.mpr
  left
  rw [List.mem_flatMap]
  refine ⟨betaSigmaFstRule, ?_, ?_⟩
  · simp [betaSigmaFstRule, mettaPure]
  · unfold applyRuleWithPremisesUsing
    rw [List.mem_flatMap]
    let bs : Bindings := [("b", quoteClosedTm b), ("a", quoteClosedTm a)]
    refine ⟨bs, ?_, ?_⟩
    · simp [bs, betaSigmaFstRule, quoteClosedTm, quoteTm, quoteTmWith,
        mkFst, mkPair, matchPattern, matchArgs, mergeBindings]
    · rw [List.mem_map]
      refine ⟨bs, ?_, ?_⟩
      · simp [applyPremisesWithEnv, bs, betaSigmaFstRule]
      · simp [bs, betaSigmaFstRule, applyBindings]

/-- Positive bridge example (βΣ snd): quoted kernel step is a `langReduces` step. -/
theorem langReduces_quoteClosed_betaSigmaSnd (a b : PureTm 0) :
    langReduces mettaPure (quoteClosedTm (.snd (.pair a b))) (quoteClosedTm b) := by
  apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
  unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
  apply List.mem_append.mpr
  left
  rw [List.mem_flatMap]
  refine ⟨betaSigmaSndRule, ?_, ?_⟩
  · simp [betaSigmaSndRule, mettaPure]
  · unfold applyRuleWithPremisesUsing
    rw [List.mem_flatMap]
    let bs : Bindings := [("b", quoteClosedTm b), ("a", quoteClosedTm a)]
    refine ⟨bs, ?_, ?_⟩
    · simp [bs, betaSigmaSndRule, quoteClosedTm, quoteTm, quoteTmWith,
        mkSnd, mkPair, matchPattern, matchArgs, mergeBindings]
    · rw [List.mem_map]
      refine ⟨bs, ?_, ?_⟩
      · simp [applyPremisesWithEnv, bs, betaSigmaSndRule]
      · simp [bs, betaSigmaSndRule, applyBindings]

/-- **A-layer (operational)**: the closed computational fragment executed as one
`langReduces` step by current `mettaPure` profile semantics. -/
inductive PureOpStep : PureTm 0 → PureTm 0 → Prop where
  | betaPiId (a : PureTm 0) :
      PureOpStep (.app (.lam (.var 0)) a) a
  | betaSigmaFst (a b : PureTm 0) :
      PureOpStep (.fst (.pair a b)) a
  | betaSigmaSnd (a b : PureTm 0) :
      PureOpStep (.snd (.pair a b)) b

/-- **B-layer (theory)**: congruence-theoretic kernel step relation. -/
abbrev PureTheoryStep : PureTm 0 → PureTm 0 → Prop := Red

/-- A-layer steps are B-layer steps. -/
theorem pureOpStep_to_pureTheoryStep {t u : PureTm 0}
    (h : PureOpStep t u) : PureTheoryStep t u :=
  match h with
  | .betaPiId a => by
      simpa [PureTheoryStep] using (Red.betaPi (.var 0) a)
  | .betaSigmaFst a b => by
      simpa [PureTheoryStep] using (Red.betaSigmaFst a b)
  | .betaSigmaSnd a b => by
      simpa [PureTheoryStep] using (Red.betaSigmaSnd a b)

/-- A-layer one-step soundness into declarative `langReduces`. -/
theorem pureOpStep_sound_langReduces_quoteClosed {t u : PureTm 0}
    (h : PureOpStep t u) :
    langReduces mettaPure (quoteClosedTm t) (quoteClosedTm u) :=
  match h with
  | .betaPiId a => by
      simpa using langReduces_quoteClosed_betaPi_id a
  | .betaSigmaFst a b => langReduces_quoteClosed_betaSigmaFst a b
  | .betaSigmaSnd a b => langReduces_quoteClosed_betaSigmaSnd a b

/-- Reflexive-transitive closure of the operational A-layer. -/
abbrev PureOpStepStar (t u : PureTm 0) : Prop := Relation.ReflTransGen PureOpStep t u

/-- Reflexive-transitive closure of the theory B-layer. -/
abbrev PureTheoryStepStar (t u : PureTm 0) : Prop := RedStar t u

/-- A-layer stars embed into B-layer stars. -/
theorem pureOpStepStar_to_pureTheoryStepStar {t u : PureTm 0}
    (h : PureOpStepStar t u) : PureTheoryStepStar t u := by
  induction h with
  | refl =>
      simpa [PureTheoryStepStar] using RedStar.refl t
  | tail hxy hyz ih =>
      exact RedStar.tail ih (pureOpStep_to_pureTheoryStep hyz)

/-- A-layer multi-step soundness into profile-level multi-step reduction. -/
theorem pureOpStepStar_sound_langReduces_quoteClosed {t u : PureTm 0}
    (h : PureOpStepStar t u) :
    PureProfileStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih
        (pureOpStep_sound_langReduces_quoteClosed hyz)

/-- A-layer one-step soundness into the sealed C1 base. -/
theorem pureOpStep_sound_pureProfileBaseStep_quoteClosed {t u : PureTm 0}
    (h : PureOpStep t u) :
    PureProfileBaseStep (quoteClosedTm t) (quoteClosedTm u) := by
  match h with
  | .betaPiId a =>
      let qbody : Pattern := closeFVar 0 (defaultBinderName 0) (.fvar (defaultBinderName 0))
      have hbase :
          PureProfileBaseStep (quoteClosedTm (.app (.lam (.var 0)) a))
            (openBVar 0 (quoteClosedTm a) qbody) := by
        simpa [qbody, quoteClosedTm, quoteTm, quoteTmWith, emptyEnv, envCons, mkApp, mkLam] using
          (PureProfileBaseStep.betaPi qbody (quoteClosedTm a))
      have hopen : openBVar 0 (quoteClosedTm a) qbody = quoteClosedTm a := by
        simp [qbody, closeFVar, openBVar]
      exact hopen ▸ hbase
  | .betaSigmaFst a b =>
      simpa [quoteClosedTm, quoteTm, quoteTmWith, mkFst, mkPair] using
        (PureProfileBaseStep.betaSigmaFst (quoteClosedTm a) (quoteClosedTm b))
  | .betaSigmaSnd a b =>
      simpa [quoteClosedTm, quoteTm, quoteTmWith, mkSnd, mkPair] using
        (PureProfileBaseStep.betaSigmaSnd (quoteClosedTm a) (quoteClosedTm b))

/-- A-layer one-step soundness into C1. -/
theorem pureOpStep_sound_pureProfileTheoryStep_quoteClosed {t u : PureTm 0}
    (h : PureOpStep t u) :
    PureProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u) := by
  exact .base (pureOpStep_sound_pureProfileBaseStep_quoteClosed h)

/-- A-layer multi-step soundness into C1 star closure. -/
theorem pureOpStepStar_sound_pureProfileTheoryStep_quoteClosed {t u : PureTm 0}
    (h : PureOpStepStar t u) :
    PureProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih
        (pureOpStep_sound_pureProfileTheoryStep_quoteClosed hyz)

/-- **B -> C1 (parametric)**:
If kernel `inst0` commutes with quotation/opening for a naming policy `ν`,
then every kernel one-step reduction is sound into C1 at that quotation. -/
private theorem pureTheoryStep_sound_pureProfileTheoryStep_quoteTmWith_assuming_inst0
    (ν : Nat → String)
    (hinst0 : Inst0OpenBridgeCompat ν)
    {n : Nat} (k : Nat) (ρ : QuoteEnv n) {t u : PureTm n}
    (hcompat : QuoteCompat ν k ρ)
    (h : Red t u) :
    PureProfileTheoryStep (quoteTmWith ν k ρ t) (quoteTmWith ν k ρ u) := by
  induction h generalizing k with
  | @betaPi n body a =>
      have hbase :
          PureProfileTheoryStep
            (quoteTmWith ν k ρ (.app (.lam body) a))
            (openBVar 0 (quoteTmWith ν k ρ a)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body))) := by
        exact .base (PureProfileBaseStep.betaPi
          (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body))
          (quoteTmWith ν k ρ a))
      have hq := hinst0 k ρ a body hcompat
      simpa [quoteTmWith, mkApp, mkLam, hq] using hbase
  | @betaSigmaFst n a b =>
      simpa [quoteTmWith, mkFst, mkPair] using
        (PureProfileTheoryStep.base
          (PureProfileBaseStep.betaSigmaFst (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)))
  | @betaSigmaSnd n a b =>
      simpa [quoteTmWith, mkSnd, mkPair] using
        (PureProfileTheoryStep.base
          (PureProfileBaseStep.betaSigmaSnd (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)))
  | @congPiDom n A A' B hAA' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx :
          PureProfileTheoryStep
            (mkPi (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)))
            (mkPi (quoteTmWith ν k ρ A')
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))) := by
        exact .ctx (K := .piDom .hole
          (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))) hstep
      simpa [quoteTmWith, mkPi] using hctx
  | @congPiCod n A B B' hBB' ih =>
      have hstep := ih (k := k + 1) (ρ := envCons (ν k) ρ)
        (QuoteCompat.envCons hcompat.1 hcompat)
      have hclose :
          PureProfileTheoryStep
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B')) := by
        exact .ctx (K := .close (ν k) .hole) hstep
      have hctx :
          PureProfileTheoryStep
            (mkPi (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)))
            (mkPi (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B'))) := by
        exact .ctx (K := .piCod (quoteTmWith ν k ρ A) .hole) hclose
      simpa [quoteTmWith, mkPi] using hctx
  | @congSigmaDom n A A' B hAA' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx :
          PureProfileTheoryStep
            (mkSigma (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)))
            (mkSigma (quoteTmWith ν k ρ A')
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))) := by
        exact .ctx (K := .sigmaDom .hole
          (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))) hstep
      simpa [quoteTmWith, mkSigma] using hctx
  | @congSigmaCod n A B B' hBB' ih =>
      have hstep := ih (k := k + 1) (ρ := envCons (ν k) ρ)
        (QuoteCompat.envCons hcompat.1 hcompat)
      have hclose :
          PureProfileTheoryStep
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B')) := by
        exact .ctx (K := .close (ν k) .hole) hstep
      have hctx :
          PureProfileTheoryStep
            (mkSigma (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)))
            (mkSigma (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B'))) := by
        exact .ctx (K := .sigmaCod (quoteTmWith ν k ρ A) .hole) hclose
      simpa [quoteTmWith, mkSigma] using hctx
  | @congIdTy n A A' a b hAA' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : PureProfileTheoryStep
          (mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b))
          (mkId (quoteTmWith ν k ρ A') (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)) := by
        exact .ctx (K := .idTy .hole (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)) hstep
      simpa [quoteTmWith, mkId] using hctx
  | @congIdLeft n A a a' b haa' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : PureProfileTheoryStep
          (mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b))
          (mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a') (quoteTmWith ν k ρ b)) := by
        exact .ctx (K := .idLeft (quoteTmWith ν k ρ A) .hole (quoteTmWith ν k ρ b)) hstep
      simpa [quoteTmWith, mkId] using hctx
  | @congIdRight n A a b b' hbb' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : PureProfileTheoryStep
          (mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b))
          (mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b')) := by
        exact .ctx (K := .idRight (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) .hole) hstep
      simpa [quoteTmWith, mkId] using hctx
  | @congLam n b b' hbb' ih =>
      have hstep := ih (k := k + 1) (ρ := envCons (ν k) ρ)
        (QuoteCompat.envCons hcompat.1 hcompat)
      have hclose :
          PureProfileTheoryStep
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) b))
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) b')) := by
        exact .ctx (K := .close (ν k) .hole) hstep
      have hctx :
          PureProfileTheoryStep
            (mkLam (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) b)))
            (mkLam (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) b'))) := by
        exact .ctx (K := .lam .hole) hclose
      simpa [quoteTmWith, mkLam] using hctx
  | @congAppFun n f f' a hff' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : PureProfileTheoryStep
          (mkApp (quoteTmWith ν k ρ f) (quoteTmWith ν k ρ a))
          (mkApp (quoteTmWith ν k ρ f') (quoteTmWith ν k ρ a)) := by
        exact .ctx (K := .appFun .hole (quoteTmWith ν k ρ a)) hstep
      simpa [quoteTmWith, mkApp] using hctx
  | @congAppArg n f a a' haa' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : PureProfileTheoryStep
          (mkApp (quoteTmWith ν k ρ f) (quoteTmWith ν k ρ a))
          (mkApp (quoteTmWith ν k ρ f) (quoteTmWith ν k ρ a')) := by
        exact .ctx (K := .appArg (quoteTmWith ν k ρ f) .hole) hstep
      simpa [quoteTmWith, mkApp] using hctx
  | @congPairFst n a a' b haa' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : PureProfileTheoryStep
          (mkPair (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b))
          (mkPair (quoteTmWith ν k ρ a') (quoteTmWith ν k ρ b)) := by
        exact .ctx (K := .pairFst .hole (quoteTmWith ν k ρ b)) hstep
      simpa [quoteTmWith, mkPair] using hctx
  | @congPairSnd n a b b' hbb' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : PureProfileTheoryStep
          (mkPair (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b))
          (mkPair (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b')) := by
        exact .ctx (K := .pairSnd (quoteTmWith ν k ρ a) .hole) hstep
      simpa [quoteTmWith, mkPair] using hctx
  | @congFst n p p' hpp' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : PureProfileTheoryStep
          (mkFst (quoteTmWith ν k ρ p))
          (mkFst (quoteTmWith ν k ρ p')) := by
        exact .ctx (K := .fst .hole) hstep
      simpa [quoteTmWith, mkFst] using hctx
  | @congSnd n p p' hpp' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : PureProfileTheoryStep
          (mkSnd (quoteTmWith ν k ρ p))
          (mkSnd (quoteTmWith ν k ρ p')) := by
        exact .ctx (K := .snd .hole) hstep
      simpa [quoteTmWith, mkSnd] using hctx
  | @congRefl n a a' haa' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : PureProfileTheoryStep
          (mkRefl (quoteTmWith ν k ρ a))
          (mkRefl (quoteTmWith ν k ρ a')) := by
        exact .ctx (K := .refl .hole) hstep
      simpa [quoteTmWith, mkRefl] using hctx

/-- Closed specialization of `pureTheoryStep_sound_pureProfileTheoryStep_quoteTmWith_assuming_inst0`
for the default binder naming policy. -/
private theorem pureTheoryStep_sound_pureProfileTheoryStep_quoteClosed_assuming_inst0
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : PureTm 0} (h : PureTheoryStep t u) :
    PureProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u) := by
  simpa [quoteClosedTm, quoteTm, emptyEnv] using
    pureTheoryStep_sound_pureProfileTheoryStep_quoteTmWith_assuming_inst0
      (ν := defaultBinderName) hinst0 (k := 0) (ρ := emptyEnv) hcompat0 h

/-- Star-closure transport for B -> C1 under the same `inst0` bridge assumption. -/
private theorem pureTheoryStepStar_sound_pureProfileTheoryStepStar_quoteClosed_assuming_inst0
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : PureTm 0} (h : PureTheoryStepStar t u) :
    PureProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih
        (pureTheoryStep_sound_pureProfileTheoryStep_quoteClosed_assuming_inst0 hinst0 hcompat0 hyz)

/-- B -> C1 transport (parameterized by an `inst0` bridge witness). -/
theorem pureTheoryStep_sound_pureProfileTheoryStep_quoteTmWith
    (ν : Nat → String) (hinst0 : Inst0OpenBridgeCompat ν)
    {n : Nat} (k : Nat) (ρ : QuoteEnv n) {t u : PureTm n}
    (hcompat : QuoteCompat ν k ρ)
    (h : Red t u) :
    PureProfileTheoryStep (quoteTmWith ν k ρ t) (quoteTmWith ν k ρ u) :=
  pureTheoryStep_sound_pureProfileTheoryStep_quoteTmWith_assuming_inst0
    (ν := ν) hinst0 (k := k) (ρ := ρ) hcompat h

private theorem defaultBinderName_quoteCompat0 :
    QuoteCompat defaultBinderName 0 emptyEnv :=
  quoteCompat_empty defaultBinderName defaultBinderName_injective 0

/-- Closed default-binder B -> C1 transport without external bridge arguments. -/
theorem pureTheoryStep_sound_pureProfileTheoryStep_quoteClosed
    {t u : PureTm 0} (h : PureTheoryStep t u) :
    PureProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u) :=
  pureTheoryStep_sound_pureProfileTheoryStep_quoteClosed_assuming_inst0
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0
    h

/-- Closed default-binder star transport B* -> C1* without external bridge arguments. -/
theorem pureTheoryStepStar_sound_pureProfileTheoryStepStar_quoteClosed
    {t u : PureTm 0} (h : PureTheoryStepStar t u) :
    PureProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) :=
  pureTheoryStepStar_sound_pureProfileTheoryStepStar_quoteClosed_assuming_inst0
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0
    h

private def betaPiOneNestedLamRedex : PureTm 0 :=
  .app (.lam (.lam (.var (Fin.succ (0 : Fin 1))))) .u0

private def betaPiOneNestedLamContractum : PureTm 0 :=
  .lam .u0

private def betaPiTwoNestedLamRedex : PureTm 0 :=
  .app (.lam (.lam (.lam (.var (Fin.succ (Fin.succ (0 : Fin 1))))))) .u0

private def betaPiTwoNestedLamContractum : PureTm 0 :=
  .lam (.lam .u0)

/-- Regression: one nested binder in βΠ body still transports to C1. -/
private theorem betaPi_bridge_regression_one_nestedLam_assuming_inst0
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv) :
    PureProfileTheoryStep
      (quoteClosedTm betaPiOneNestedLamRedex)
      (quoteClosedTm betaPiOneNestedLamContractum) := by
  have hred : Red betaPiOneNestedLamRedex betaPiOneNestedLamContractum := by
    simpa [betaPiOneNestedLamRedex, betaPiOneNestedLamContractum, inst0, subst, subst0, liftSub,
      rename, wk] using
      (Red.betaPi (.lam (.var (Fin.succ (0 : Fin 1)))) (.u0))
  exact pureTheoryStep_sound_pureProfileTheoryStep_quoteClosed_assuming_inst0 hinst0 hcompat0 hred

/-- Regression: two nested binders in βΠ body still transports to C1. -/
private theorem betaPi_bridge_regression_two_nestedLam_assuming_inst0
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv) :
    PureProfileTheoryStep
      (quoteClosedTm betaPiTwoNestedLamRedex)
      (quoteClosedTm betaPiTwoNestedLamContractum) := by
  have hred : Red betaPiTwoNestedLamRedex betaPiTwoNestedLamContractum := by
    simpa [betaPiTwoNestedLamRedex, betaPiTwoNestedLamContractum, inst0, subst, subst0, liftSub,
      rename, wk] using
      (Red.betaPi (.lam (.lam (.var (Fin.succ (Fin.succ (0 : Fin 1)))))) (.u0))
  exact pureTheoryStep_sound_pureProfileTheoryStep_quoteClosed_assuming_inst0 hinst0 hcompat0 hred

/-- Default-binder regression: one nested binder in βΠ body still transports to C1. -/
theorem betaPi_bridge_regression_one_nestedLam :
    PureProfileTheoryStep
      (quoteClosedTm betaPiOneNestedLamRedex)
      (quoteClosedTm betaPiOneNestedLamContractum) :=
  betaPi_bridge_regression_one_nestedLam_assuming_inst0
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0

/-- Default-binder regression: two nested binders in βΠ body still transports to C1. -/
theorem betaPi_bridge_regression_two_nestedLam :
    PureProfileTheoryStep
      (quoteClosedTm betaPiTwoNestedLamRedex)
      (quoteClosedTm betaPiTwoNestedLamContractum) :=
  betaPi_bridge_regression_two_nestedLam_assuming_inst0
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0

/-- Backwards-compatible name for the A-layer step relation. -/
abbrev ClosedComputationStep : PureTm 0 → PureTm 0 → Prop := PureOpStep

/-- Backwards-compatible name for A-layer star closure. -/
abbrev ClosedComputationStepStar (t u : PureTm 0) : Prop := PureOpStepStar t u

/-- Backwards-compatible theorem alias. -/
theorem closedComputationStep_to_red {t u : PureTm 0}
    (h : ClosedComputationStep t u) : Red t u := by
  simpa [ClosedComputationStep, PureTheoryStep] using
    (pureOpStep_to_pureTheoryStep (t := t) (u := u) h)

/-- Backwards-compatible theorem alias. -/
theorem closedComputationStepStar_to_redStar {t u : PureTm 0}
    (h : ClosedComputationStepStar t u) : RedStar t u := by
  simpa [ClosedComputationStepStar, PureTheoryStepStar] using
    (pureOpStepStar_to_pureTheoryStepStar (t := t) (u := u) h)

/-- Backwards-compatible theorem alias. -/
theorem closedComputationStep_sound_langReduces_quoteClosed {t u : PureTm 0}
    (h : ClosedComputationStep t u) :
    langReduces mettaPure (quoteClosedTm t) (quoteClosedTm u) := by
  simpa [ClosedComputationStep] using
    (pureOpStep_sound_langReduces_quoteClosed (t := t) (u := u) h)

/-- Backwards-compatible theorem alias. -/
theorem closedComputationStepStar_sound_langReduces_quoteClosed {t u : PureTm 0}
    (h : ClosedComputationStepStar t u) :
    PureProfileStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  simpa [ClosedComputationStepStar] using
    (pureOpStepStar_sound_langReduces_quoteClosed (t := t) (u := u) h)

/-- Negative bridge example:
the full kernel step relation (`Red`, with constructor congruence) is strictly
stronger than current `langReduces mettaPure` (top-level rewrite in this profile). -/
theorem not_all_pureTheoryStep_sound_to_langReduces_quoteClosed :
    ¬ (∀ {t u : PureTm 0}, PureTheoryStep t u →
        langReduces mettaPure (quoteClosedTm t) (quoteClosedTm u)) := by
  intro hsound
  let t : PureTm 0 := .app .u1 (.fst (.pair .u0 .u1))
  let u : PureTm 0 := .app .u1 .u0
  have hred : PureTheoryStep t u := by
    simpa [PureTheoryStep] using (Red.congAppArg (Red.betaSigmaFst _ _))
  have hlang : langReduces mettaPure (quoteClosedTm t) (quoteClosedTm u) := hsound hred
  have hexec : langReducesExecUsing RelationEnv.empty mettaPure (quoteClosedTm t) (quoteClosedTm u) :=
    langReducesUsing_to_exec (relEnv := RelationEnv.empty) (lang := mettaPure) hlang
  have hempty : rewriteWithContextWithPremisesUsing RelationEnv.empty mettaPure (quoteClosedTm t) = [] := by
    simp [t, quoteClosedTm, quoteTm, quoteTmWith, mkApp, mkFst, mkPair,
      rewriteWithContextWithPremisesUsing, rewriteStepWithPremisesUsing,
      applyRuleWithPremisesUsing, mettaPure, applyPremisesWithEnv]
    constructor
    · intro x hx
      simp [u1, matchArgs, matchPattern] at hx
    constructor
    · intro x hx
      simp [u1, matchPattern] at hx
    · intro x hx
      simp [u1, matchPattern] at hx
  have hfalse : False := by
    simp [langReducesExecUsing, hempty] at hexec
  exact False.elim hfalse

/-- Backwards-compatible name for the same mismatch fact. -/
theorem not_all_red_steps_sound_to_langReduces_quoteClosed :
    ¬ (∀ {t u : PureTm 0}, Red t u →
        langReduces mettaPure (quoteClosedTm t) (quoteClosedTm u)) := by
  intro h
  exact not_all_pureTheoryStep_sound_to_langReduces_quoteClosed (fun hred => h hred)

end Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
