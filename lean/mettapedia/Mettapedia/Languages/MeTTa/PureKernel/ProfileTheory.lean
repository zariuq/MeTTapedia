import Mettapedia.Languages.MeTTa.Pure.Core
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# PureKernel Profile-Theory Layer (C1)

This file defines the profile-side theory closure for MeTTa-Pure:

- a sealed base step relation with exactly the three pure β rules
- pure `Pattern` contexts (`PurePatCtx`)
- contextual closure (`PureProfileTheoryStep`)
- reflexive-transitive closure (`PureProfileTheoryStepStar`)

This is the C1 layer in the A/B/C architecture.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core

/-- Reflexive-transitive closure of profile-level one-step reduction for `mettaPure`. -/
abbrev PureProfileStepStar (p q : Pattern) : Prop :=
  Relation.ReflTransGen (langReduces mettaPure) p q

/-- Sealed base one-step relation for the pure profile:
exactly βΠ, βΣ-fst, βΣ-snd at the `Pattern` level. -/
inductive PureProfileBaseStep : Pattern → Pattern → Prop where
  | betaPi (body a : Pattern) :
      PureProfileBaseStep (mkApp (mkLam body) a) (openBVar 0 a body)
  | betaSigmaFst (a b : Pattern) :
      PureProfileBaseStep (mkFst (mkPair a b)) a
  | betaSigmaSnd (a b : Pattern) :
      PureProfileBaseStep (mkSnd (mkPair a b)) b

private def betaPiRule : RewriteRule :=
  { name := "BetaPi",
    typeContext := [("body", .base "Tm"), ("a", .base "Tm")],
    premises := [],
    left := .apply "App" [.apply "Lam" [.lambda none (.fvar "body")], .fvar "a"],
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

/-- Sealed base steps are sound for profile one-step reduction. -/
theorem pureProfileBaseStep_sound_langReduces {s t : Pattern}
    (h : PureProfileBaseStep s t) :
    langReduces mettaPure s t := by
  cases h with
  | betaPi body a =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaPiRule, ?_, ?_⟩
      · simp [betaPiRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("a", a), ("body", body)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaPiRule, mkApp, mkLam, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaPiRule]
          · simp [bs, betaPiRule, applyBindings]
  | @betaSigmaFst aa bb =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaSigmaFstRule, ?_, ?_⟩
      · simp [betaSigmaFstRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("b", bb), ("a", t)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaSigmaFstRule, mkFst, mkPair, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaSigmaFstRule]
          · simp [bs, betaSigmaFstRule, applyBindings]
  | @betaSigmaSnd aa bb =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaSigmaSndRule, ?_, ?_⟩
      · simp [betaSigmaSndRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("b", t), ("a", aa)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaSigmaSndRule, mkSnd, mkPair, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaSigmaSndRule]
          · simp [bs, betaSigmaSndRule, applyBindings]

/-- Pure term-contexts on the `Pattern` side (C1): exactly the constructor positions
corresponding to kernel congruence (`Red`). -/
inductive PurePatCtx : Type where
  | hole : PurePatCtx
  | piDom (K : PurePatCtx) (B : Pattern) : PurePatCtx
  | piCod (A : Pattern) (K : PurePatCtx) : PurePatCtx
  | sigmaDom (K : PurePatCtx) (B : Pattern) : PurePatCtx
  | sigmaCod (A : Pattern) (K : PurePatCtx) : PurePatCtx
  | idTy (K : PurePatCtx) (a b : Pattern) : PurePatCtx
  | idLeft (A : Pattern) (K : PurePatCtx) (b : Pattern) : PurePatCtx
  | idRight (A a : Pattern) (K : PurePatCtx) : PurePatCtx
  | lam (K : PurePatCtx) : PurePatCtx
  | appFun (K : PurePatCtx) (a : Pattern) : PurePatCtx
  | appArg (f : Pattern) (K : PurePatCtx) : PurePatCtx
  | pairFst (K : PurePatCtx) (b : Pattern) : PurePatCtx
  | pairSnd (a : Pattern) (K : PurePatCtx) : PurePatCtx
  | fst (K : PurePatCtx) : PurePatCtx
  | snd (K : PurePatCtx) : PurePatCtx
  | refl (K : PurePatCtx) : PurePatCtx
  | close (x : String) (K : PurePatCtx) : PurePatCtx

/-- Plug a `Pattern` into a pure term-context. -/
def plugPurePatCtx : PurePatCtx → Pattern → Pattern
  | .hole, p => p
  | .piDom K B, p => mkPi (plugPurePatCtx K p) B
  | .piCod A K, p => mkPi A (plugPurePatCtx K p)
  | .sigmaDom K B, p => mkSigma (plugPurePatCtx K p) B
  | .sigmaCod A K, p => mkSigma A (plugPurePatCtx K p)
  | .idTy K a b, p => mkId (plugPurePatCtx K p) a b
  | .idLeft A K b, p => mkId A (plugPurePatCtx K p) b
  | .idRight A a K, p => mkId A a (plugPurePatCtx K p)
  | .lam K, p => mkLam (plugPurePatCtx K p)
  | .appFun K a, p => mkApp (plugPurePatCtx K p) a
  | .appArg f K, p => mkApp f (plugPurePatCtx K p)
  | .pairFst K b, p => mkPair (plugPurePatCtx K p) b
  | .pairSnd a K, p => mkPair a (plugPurePatCtx K p)
  | .fst K, p => mkFst (plugPurePatCtx K p)
  | .snd K, p => mkSnd (plugPurePatCtx K p)
  | .refl K, p => mkRefl (plugPurePatCtx K p)
  | .close x K, p => closeFVar 0 x (plugPurePatCtx K p)

/-- C1 one-step profile-theory relation:
least contextual closure (under pure contexts) of the sealed base β rules. -/
inductive PureProfileTheoryStep : Pattern → Pattern → Prop where
  | base {s t : Pattern} :
      PureProfileBaseStep s t →
      PureProfileTheoryStep s t
  | ctx {K : PurePatCtx} {s t : Pattern} :
      PureProfileTheoryStep s t →
      PureProfileTheoryStep (plugPurePatCtx K s) (plugPurePatCtx K t)

/-- C1 star closure. -/
abbrev PureProfileTheoryStepStar (p q : Pattern) : Prop :=
  Relation.ReflTransGen PureProfileTheoryStep p q

/-- Any sealed base step is a C1 step. -/
theorem pureProfileBaseStep_to_pureProfileTheoryStep {s t : Pattern}
    (h : PureProfileBaseStep s t) :
    PureProfileTheoryStep s t :=
  .base h

/-- Any sealed base step is a C1-star step. -/
theorem pureProfileBaseStep_to_pureProfileTheoryStepStar {s t : Pattern}
    (h : PureProfileBaseStep s t) :
    PureProfileTheoryStepStar s t :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl (.base h)

end Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory
