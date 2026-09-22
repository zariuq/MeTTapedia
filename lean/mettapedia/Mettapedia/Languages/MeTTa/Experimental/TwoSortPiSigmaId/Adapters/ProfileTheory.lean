import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# TwoSortPiSigmaId Profile-Theory Layer (C1)

This file defines the profile-side theory closure for the two-sort experiment:

- a sealed base step relation with exactly the three two-sort β rules
- two-sort `Pattern` contexts (`TwoSortPatCtx`)
- contextual closure (`TwoSortProfileTheoryStep`)
- reflexive-transitive closure (`TwoSortProfileTheoryStepStar`)

This is the C1 layer in the A/B/C architecture.
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.ProfileTheory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core

/-- Reflexive-transitive closure of profile-level one-step reduction for `twoSortDependent`. -/
abbrev TwoSortProfileStepStar (p q : Pattern) : Prop :=
  Relation.ReflTransGen (langReduces twoSortDependent) p q

/-- Sealed base one-step relation for the two-sort profile:
exactly βΠ, βΣ-fst, βΣ-snd at the `Pattern` level. -/
inductive TwoSortProfileBaseStep : Pattern → Pattern → Prop where
  | betaPi (body a : Pattern) :
      TwoSortProfileBaseStep (mkApp (mkLam body) a) (instantiateBVar a body)
  | betaSigmaFst (a b : Pattern) :
      TwoSortProfileBaseStep (mkFst (mkPair a b)) a
  | betaSigmaSnd (a b : Pattern) :
      TwoSortProfileBaseStep (mkSnd (mkPair a b)) b

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

/-- Sealed base steps on genuine, locally closed terms are sound for profile
one-step reduction.  The scope hypothesis excludes dangling de Bruijn indices,
which are inhabitants of the raw representation but not the two-sort experiment terms. -/
theorem twoSortProfileBaseStep_sound_langReduces {s t : Pattern}
    (h : TwoSortProfileBaseStep s t) (hs : s.isWellScoped = true) :
    langReduces twoSortDependent s t := by
  cases h with
  | betaPi body a =>
      have hscope : body.isWellScopedAt 1 = true ∧ a.isWellScoped = true := by
        simpa [Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, mkApp, mkLam] using hs
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := twoSortDependent)
      refine ⟨1, ?_⟩
      rw [rewriteAt_one_eq_rewriteStepWithPremisesUsing]
      unfold rewriteStepWithPremisesUsing
      rw [List.mem_flatMap]
      refine ⟨betaPiRule, ?_, ?_⟩
      · simp [betaPiRule, twoSortDependent]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("a", a), ("body", body)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaPiRule, mkApp, mkLam, twoSortDependent,
            matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaPiRule]
          · rw [OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
              applyRuleBindings_eq_applyBindings betaPiRule _ (by decide)]
            simp [bs, betaPiRule, applyBindings,
              instantiateBVar_eq_openBVar_of_isWellScoped hscope.1 hscope.2]
  | @betaSigmaFst aa bb =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := twoSortDependent)
      refine ⟨1, ?_⟩
      rw [rewriteAt_one_eq_rewriteStepWithPremisesUsing]
      unfold rewriteStepWithPremisesUsing
      rw [List.mem_flatMap]
      refine ⟨betaSigmaFstRule, ?_, ?_⟩
      · simp [betaSigmaFstRule, twoSortDependent]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("b", bb), ("a", t)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaSigmaFstRule, mkFst, mkPair, twoSortDependent,
            matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaSigmaFstRule]
          · rw [OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
              applyRuleBindings_eq_applyBindings betaSigmaFstRule _ (by decide)]
            simp [bs, betaSigmaFstRule, applyBindings]
  | @betaSigmaSnd aa bb =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := twoSortDependent)
      refine ⟨1, ?_⟩
      rw [rewriteAt_one_eq_rewriteStepWithPremisesUsing]
      unfold rewriteStepWithPremisesUsing
      rw [List.mem_flatMap]
      refine ⟨betaSigmaSndRule, ?_, ?_⟩
      · simp [betaSigmaSndRule, twoSortDependent]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("b", t), ("a", aa)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaSigmaSndRule, mkSnd, mkPair, twoSortDependent,
            matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaSigmaSndRule]
          · rw [OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
              applyRuleBindings_eq_applyBindings betaSigmaSndRule _ (by decide)]
            simp [bs, betaSigmaSndRule, applyBindings]

/-- two-sort term-contexts on the `Pattern` side (C1): exactly the constructor positions
corresponding to kernel congruence (`Red`). -/
inductive TwoSortPatCtx : Type where
  | hole : TwoSortPatCtx
  | piDom (K : TwoSortPatCtx) (B : Pattern) : TwoSortPatCtx
  | piCod (A : Pattern) (K : TwoSortPatCtx) : TwoSortPatCtx
  | sigmaDom (K : TwoSortPatCtx) (B : Pattern) : TwoSortPatCtx
  | sigmaCod (A : Pattern) (K : TwoSortPatCtx) : TwoSortPatCtx
  | idTy (K : TwoSortPatCtx) (a b : Pattern) : TwoSortPatCtx
  | idLeft (A : Pattern) (K : TwoSortPatCtx) (b : Pattern) : TwoSortPatCtx
  | idRight (A a : Pattern) (K : TwoSortPatCtx) : TwoSortPatCtx
  | lam (K : TwoSortPatCtx) : TwoSortPatCtx
  | appFun (K : TwoSortPatCtx) (a : Pattern) : TwoSortPatCtx
  | appArg (f : Pattern) (K : TwoSortPatCtx) : TwoSortPatCtx
  | pairFst (K : TwoSortPatCtx) (b : Pattern) : TwoSortPatCtx
  | pairSnd (a : Pattern) (K : TwoSortPatCtx) : TwoSortPatCtx
  | fst (K : TwoSortPatCtx) : TwoSortPatCtx
  | snd (K : TwoSortPatCtx) : TwoSortPatCtx
  | refl (K : TwoSortPatCtx) : TwoSortPatCtx
  | close (x : String) (K : TwoSortPatCtx) : TwoSortPatCtx

/-- Plug a `Pattern` into a two-sort term-context. -/
def plugTwoSortPatCtx : TwoSortPatCtx → Pattern → Pattern
  | .hole, p => p
  | .piDom K B, p => mkPi (plugTwoSortPatCtx K p) B
  | .piCod A K, p => mkPi A (plugTwoSortPatCtx K p)
  | .sigmaDom K B, p => mkSigma (plugTwoSortPatCtx K p) B
  | .sigmaCod A K, p => mkSigma A (plugTwoSortPatCtx K p)
  | .idTy K a b, p => mkId (plugTwoSortPatCtx K p) a b
  | .idLeft A K b, p => mkId A (plugTwoSortPatCtx K p) b
  | .idRight A a K, p => mkId A a (plugTwoSortPatCtx K p)
  | .lam K, p => mkLam (plugTwoSortPatCtx K p)
  | .appFun K a, p => mkApp (plugTwoSortPatCtx K p) a
  | .appArg f K, p => mkApp f (plugTwoSortPatCtx K p)
  | .pairFst K b, p => mkPair (plugTwoSortPatCtx K p) b
  | .pairSnd a K, p => mkPair a (plugTwoSortPatCtx K p)
  | .fst K, p => mkFst (plugTwoSortPatCtx K p)
  | .snd K, p => mkSnd (plugTwoSortPatCtx K p)
  | .refl K, p => mkRefl (plugTwoSortPatCtx K p)
  | .close x K, p => closeFVar 0 x (plugTwoSortPatCtx K p)

/-- C1 one-step profile-theory relation:
least contextual closure (under two-sort contexts) of the sealed base β rules. -/
inductive TwoSortProfileTheoryStep : Pattern → Pattern → Prop where
  | base {s t : Pattern} :
      TwoSortProfileBaseStep s t →
      TwoSortProfileTheoryStep s t
  | ctx {K : TwoSortPatCtx} {s t : Pattern} :
      TwoSortProfileTheoryStep s t →
      TwoSortProfileTheoryStep (plugTwoSortPatCtx K s) (plugTwoSortPatCtx K t)

/-- C1 star closure. -/
abbrev TwoSortProfileTheoryStepStar (p q : Pattern) : Prop :=
  Relation.ReflTransGen TwoSortProfileTheoryStep p q

/-- Any sealed base step is a C1 step. -/
theorem twoSortProfileBaseStep_to_twoSortProfileTheoryStep {s t : Pattern}
    (h : TwoSortProfileBaseStep s t) :
    TwoSortProfileTheoryStep s t :=
  .base h

/-- Any sealed base step is a C1-star step. -/
theorem twoSortProfileBaseStep_to_twoSortProfileTheoryStepStar {s t : Pattern}
    (h : TwoSortProfileBaseStep s t) :
    TwoSortProfileTheoryStepStar s t :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl (.base h)

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.ProfileTheory
