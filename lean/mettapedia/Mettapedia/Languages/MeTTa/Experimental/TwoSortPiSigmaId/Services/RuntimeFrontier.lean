import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.ProfileTheory
import Mettapedia.PLN.Bridges.Languages.WorldModel.PLNWorldModelTwoSortBridge

/-!
# Two-sort calculus and runtime boundary

Classifies the current boundary between:
- the closed TwoSortPiSigmaId experiment, and
- the direct `R_exec₀` / MORK source-rule bridge.

This file is intentionally descriptive and theoremic. It does not try to force
two-sort beta rules through the runtime boundary when the current bridge hypotheses
are not satisfied.
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.RuntimeFrontier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.ProfileTheory
open Mettapedia.PLN.Bridges.Languages.WorldModel.PLNWorldModelTwoSortBridge
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Evidence.EvidenceClass

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

/-- Exact shape of the three `twoSortDependent` rewrites. -/
theorem twoSortDependent_rewrites_exact :
    twoSortDependent.rewrites = [betaPiRule, betaSigmaFstRule, betaSigmaSndRule] := rfl

/-- `BetaPi` uses `.subst` on the RHS, so it is outside the current
`morkTranslatable` fragment. -/
theorem betaPi_rhs_not_morkTranslatable :
    morkTranslatable betaPiRule.right = false := by
  rfl

/-- `BetaSigmaFst` has an atom-only RHS and is `morkTranslatable`. -/
theorem betaSigmaFst_rhs_morkTranslatable :
    morkTranslatable betaSigmaFstRule.right = true := by
  rfl

/-- `BetaSigmaSnd` has an atom-only RHS and is `morkTranslatable`. -/
theorem betaSigmaSnd_rhs_morkTranslatable :
    morkTranslatable betaSigmaSndRule.right = true := by
  rfl

/-- None of the current `twoSortDependent` rewrites has an `fvar` LHS, so none fits the
current direct MORK source-rule bridge entry condition. -/
theorem twoSortDependent_rewrite_lhs_not_fvar
    (r : RewriteRule) (hr : r ∈ twoSortDependent.rewrites) :
    ∀ x, r.left ≠ .fvar x := by
  intro x hx
  rw [twoSortDependent_rewrites_exact] at hr
  simp at hr
  rcases hr with rfl | rfl | rfl
  all_goals cases hx

/-- Summary theorem: no current `twoSortDependent` rewrite fits the direct `R_exec₀`
source-rule bridge hypotheses. The bridge requires an `fvar`-headed LHS, and
`BetaPi` additionally fails RHS translatability. -/
theorem no_twoSortDependent_rewrite_fits_direct_runtimeExec0_source_bridge
    (r : RewriteRule) (hr : r ∈ twoSortDependent.rewrites) :
    ¬ ∃ x, r.left = .fvar x ∧ morkTranslatable r.right = true := by
  intro hfit
  rcases hfit with ⟨x, hlhs, _⟩
  exact (twoSortDependent_rewrite_lhs_not_fvar r hr x) hlhs

/-- The real current overlap is the closed two-sort/TwoSortPiSigmaId bridge: one-step
closed two-sort computations already land in the quoted C1 interface. -/
theorem closedTwoSort_overlap_via_abc
    {t u : ScopedTerm 0} (h : TwoSortOpStep t u) :
    TwoSortProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u) :=
  twoSortOpStep_sound_twoSortProfileTheoryStep_quoteClosed h

/-- The real current overlap extends to WM through the existing A/B/C1 bridge,
not by direct source-rule firing on `R_exec₀`. -/
theorem closedTwoSort_overlap_via_abc_to_wm
    {State Query : Type*}
    [EvidenceType State] [BinaryWorldModel State Query]
    (I : TwoSortJudgmentWMInterface State Query)
    {W : State} (hW : I.side W)
    {t u : ScopedTerm 0} (h : TwoSortOpStep t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) := by
  exact twoSortTheoryStep_to_wmStrengthObligation_default I hW (twoSortOpStep_to_twoSortTheoryStep h)

/-- The same closed overlap extends to the strongest assumption-free
declaration-aware slice: when declaration values are absent, declaration
multi-step reduction collapses to core TwoSortPiSigmaId reduction, so the quoted
closed terms inherit the existing WM-strength obligation bridge. -/
theorem closedNoValuesDecl_overlap_via_abc_to_wm
    {State Query : Type*}
    [EvidenceType State] [BinaryWorldModel State Query]
    (I : TwoSortJudgmentWMInterface State Query)
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {W : State} (hW : I.side W)
    {t u : ScopedTerm 0}
    (h :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.RedStarDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) := by
  exact
    checkedNoValuesDeclKernelStar_to_wmStrengthObligation_default
      I hSig hNone hW h

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.RuntimeFrontier
