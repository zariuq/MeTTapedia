import Mettapedia.Languages.MeTTa.Pure.Core
import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary
import Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
import Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
import Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory
import Mettapedia.Logic.PLNWorldModelPureKernelBridge

/-!
# Pure ↔ Runtime Frontier

Classifies the current boundary between:
- the trusted closed Pure/PureKernel branch, and
- the direct `R_exec₀` / MORK source-rule bridge.

This file is intentionally descriptive and theoremic. It does not try to force
Pure beta rules through the runtime boundary when the current bridge hypotheses
are not satisfied.
-/

namespace Mettapedia.Languages.MeTTa.PureRuntimeFrontier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory
open Mettapedia.Logic.PLNWorldModelPureKernelBridge
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass

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

/-- Exact shape of the three `mettaPure` rewrites. -/
theorem mettaPure_rewrites_exact :
    mettaPure.rewrites = [betaPiRule, betaSigmaFstRule, betaSigmaSndRule] := rfl

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

/-- None of the current `mettaPure` rewrites has an `fvar` LHS, so none fits the
current direct MORK source-rule bridge entry condition. -/
theorem mettaPure_rewrite_lhs_not_fvar
    (r : RewriteRule) (hr : r ∈ mettaPure.rewrites) :
    ∀ x, r.left ≠ .fvar x := by
  intro x hx
  rw [mettaPure_rewrites_exact] at hr
  simp at hr
  rcases hr with rfl | rfl | rfl
  all_goals cases hx

/-- Summary theorem: no current `mettaPure` rewrite fits the direct `R_exec₀`
source-rule bridge hypotheses. The bridge requires an `fvar`-headed LHS, and
`BetaPi` additionally fails RHS translatability. -/
theorem no_mettaPure_rewrite_fits_direct_runtimeExec0_source_bridge
    (r : RewriteRule) (hr : r ∈ mettaPure.rewrites) :
    ¬ ∃ x, r.left = .fvar x ∧ morkTranslatable r.right = true := by
  intro hfit
  rcases hfit with ⟨x, hlhs, _⟩
  exact (mettaPure_rewrite_lhs_not_fvar r hr x) hlhs

/-- The real current overlap is the closed Pure/PureKernel bridge: one-step
closed Pure computations already land in the quoted C1 surface. -/
theorem closedPure_overlap_via_abc
    {t u : PureTm 0} (h : PureOpStep t u) :
    PureProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u) :=
  pureOpStep_sound_pureProfileTheoryStep_quoteClosed h

/-- The real current overlap extends to WM through the existing A/B/C1 bridge,
not by direct source-rule firing on `R_exec₀`. -/
theorem closedPure_overlap_via_abc_to_wm
    {State Query : Type*}
    [EvidenceType State] [BinaryWorldModel State Query]
    (I : PureJudgmentWMInterface State Query)
    {W : State} (hW : I.side W)
    {t u : PureTm 0} (h : PureOpStep t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) := by
  exact pureTheoryStep_to_wmStrengthObligation_default I hW (pureOpStep_to_pureTheoryStep h)

end Mettapedia.Languages.MeTTa.PureRuntimeFrontier
