-- LLM primer: Shape lemmas are root-local — one `.apply ctor argsV` where argsV
-- are already irreducible.  Each lemma gives an exact equality for `step`,
-- not membership.  No memo, no Expr, no recursive arg-evaluation.
--
-- Core result: under strict context (no external rewrites, irreducible args),
-- `step` produces exactly `intrinsicDirectPub`.
--
-- The per-dispatch-class lemmas relate DispatchClass conditions to what
-- `intrinsicDirectPub` and `step` produce.

import Algorithms.MeTTa.Simple.Backend.DeterministicBridge.Basics

namespace Algorithms.MeTTa.Simple.Backend.DeterministicBridge

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

-- ─── Strict context ──────────────────────────────────────────────────────────
-- Bundles the side conditions that recur in every shape lemma:
-- "no translateCall, no compatRewrite, no generatedRewrite, args are values."

/-- Side conditions under which `step` reduces to just `intrinsicDirect`:
    no external rewrite sources fire, and args are already irreducible. -/
structure StrictContext (s : Session) (ctor : String) (argsV : List Pattern) : Prop where
  /-- translateCall returns empty for this term. -/
  noTranslate : Session.stepTranslateCall s (.apply ctor argsV) = []
  /-- compatRewriteStep returns empty for this term. -/
  noCompat : Session.stepCompatRewrite s (.apply ctor argsV) = []
  /-- rewriteWithContext returns empty for this term. -/
  noGenerated : Session.stepGeneratedRewrite s (.apply ctor argsV) = []
  /-- Each arg is already irreducible (step returns []). -/
  argsIrreducible : ∀ a ∈ argsV, Session.step s a = []

-- ─── Core shape lemma ────────────────────────────────────────────────────────

/-- Under strict context, `step s (.apply ctor argsV) = intrinsicDirectPub s ctor argsV`. -/
theorem step_eq_intrinsicDirect_of_strict
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hCtx : StrictContext s ctor argsV) :
    Session.step s (.apply ctor argsV) = Session.intrinsicDirectPub s ctor argsV :=
  Session.step_apply_eq_intrinsicDirectPub_of_strict s ctor argsV
    hCtx.noTranslate hCtx.noCompat hCtx.noGenerated hCtx.argsIrreducible

-- ─── Dispatch-class shape lemmas ─────────────────────────────────────────────
-- These relate the DispatchClass classification (about DeterministicEval.Interface
-- fields) to what `step` produces (about the reference evaluator).
-- Under strict context + the dispatch class condition, we get exact step outputs.

/-- For `directIntrinsic` dispatch under strict context:
    `step` = `intrinsicDirectPub` and it's non-empty. -/
theorem step_directIntrinsic_of_strict
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hCtx : StrictContext s ctor argsV)
    (hDirect : (Session.intrinsicDirectPub s ctor argsV).isEmpty = false) :
    Session.step s (.apply ctor argsV) = Session.intrinsicDirectPub s ctor argsV ∧
    (Session.step s (.apply ctor argsV)).isEmpty = false :=
  ⟨step_eq_intrinsicDirect_of_strict s ctor argsV hCtx,
   by rw [step_eq_intrinsicDirect_of_strict s ctor argsV hCtx]; exact hDirect⟩

/-- For `unchanged` dispatch under strict context:
    `step` = [] (intrinsicDirect returns nothing, and nothing else fires). -/
theorem step_unchanged_of_strict
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hCtx : StrictContext s ctor argsV)
    (hNoDirect : Session.intrinsicDirectPub s ctor argsV = []) :
    Session.step s (.apply ctor argsV) = [] := by
  rw [step_eq_intrinsicDirect_of_strict s ctor argsV hCtx, hNoDirect]

/-- For `firstRule` dispatch under strict context:
    `step` = [] (intrinsicDirect returned nothing; rewrite rules don't appear in
    `intrinsicDirect` — they appear in compat/generated which are empty by StrictContext).
    The firstRuleReduction result only appears through compat/generated, not intrinsicDirect. -/
theorem step_firstRule_intrinsicDirect_empty_of_strict
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hCtx : StrictContext s ctor argsV)
    (hNoDirect : Session.intrinsicDirectPub s ctor argsV = []) :
    Session.step s (.apply ctor argsV) = [] :=
  step_unchanged_of_strict s ctor argsV hCtx hNoDirect

-- ─── Separation lemmas under noOverlap ──────────────────────────────────────
-- Under `noDeterministicReducerOverlap`, for a builtin-headed `.apply ctor argsV`:
--   translateCall = [], compatRewrite = [], generatedRewrite = []
-- Combined with `step_eq_components`, this shows `step = intrinsicDirect`.

open MeTTailCore.MeTTaIL.Match in
/-- matchPattern returns [] when the two .apply heads differ. -/
private theorem matchPattern_diff_head (h ctor : String) (pArgs tArgs : List Pattern)
    (hNe : h ≠ ctor) :
    matchPattern (.apply h pArgs) (.apply ctor tArgs) = [] := by
  unfold matchPattern
  simp [beq_iff_eq, hNe]

open MeTTailCore.MeTTaIL.Match in
/-- matchPattern returns [] for non-apply/non-fvar patterns against .apply terms. -/
private theorem matchPattern_nonApply_apply (p : Pattern) (ctor : String) (tArgs : List Pattern)
    (hNotApply : ∀ h as, p ≠ .apply h as) (hNotFvar : ∀ x, p ≠ .fvar x) :
    matchPattern p (.apply ctor tArgs) = [] := by
  cases p with
  | apply h as => exact absurd rfl (hNotApply h as)
  | fvar x => exact absurd rfl (hNotFvar x)
  | bvar n => simp [matchPattern]
  | lambda body => simp [matchPattern]
  | multiLambda n body => simp [matchPattern]
  | subst body repl => simp [matchPattern]
  | collection ct elems rest => simp [matchPattern]

open MeTTailCore.MeTTaIL.Match in
/-- matchPatternMeTTa returns [] when heads differ and pattern head is not "cons". -/
private theorem matchPatternMeTTa_diff_head (h ctor : String) (pArgs tArgs : List Pattern)
    (hNe : h ≠ ctor) (hNCons : h ≠ "cons") :
    matchPatternMeTTa (.apply h pArgs) (.apply ctor tArgs) = [] := by
  unfold matchPatternMeTTa
  have hDiff := matchPattern_diff_head h ctor pArgs tArgs hNe
  simp [hDiff]
  -- After simp: match on .apply h pArgs for "cons" check
  -- h ≠ "cons" so the cons branch doesn't fire
  split <;> simp_all

open MeTTailCore.MeTTaIL.Match in
/-- matchPatternMeTTa returns [] for non-apply/non-fvar patterns against .apply terms. -/
private theorem matchPatternMeTTa_nonApply_apply (p : Pattern) (ctor : String) (tArgs : List Pattern)
    (hNotApply : ∀ h as, p ≠ .apply h as) (hNotFvar : ∀ x, p ≠ .fvar x) :
    matchPatternMeTTa p (.apply ctor tArgs) = [] := by
  unfold matchPatternMeTTa
  simp [matchPattern_nonApply_apply p ctor tArgs hNotApply hNotFvar]
  -- After simp: match p for cons check. p is not .apply, so catch-all.
  cases p with
  | apply h as => exact absurd rfl (hNotApply h as)
  | fvar x => exact absurd rfl (hNotFvar x)
  | _ => simp

private abbrev builtinHeads := Semantics.DeterministicStrategy.intrinsicBuiltinHeads

/-- From `ruleDisjointFromBuiltins r = true` and `ctor ∈ builtins`, extract rule LHS conditions. -/
private theorem ruleDisjointFromBuiltins_conditions (r : MeTTailCore.MeTTaIL.Syntax.RewriteRule)
    (hD : Backend.SessionDeterministic.ruleDisjointFromBuiltins r = true)
    (ctor : String) (hBuiltin : builtinHeads.contains ctor = true) :
    (∀ h as, r.left = .apply h as → h ≠ ctor ∧ h.startsWith "$" = false ∧ h ≠ "cons") ∧
    (∀ x, r.left ≠ .fvar x) := by
  simp only [Backend.SessionDeterministic.ruleDisjointFromBuiltins] at hD
  refine ⟨fun h as hL => ?_, fun x hL => ?_⟩
  · rw [hL] at hD; simp only [Bool.and_eq_true] at hD
    obtain ⟨hNC, hND⟩ := hD
    refine ⟨?_, ?_, ?_⟩
    · intro hEq; subst hEq; simp_all
    · revert hND; cases h.startsWith "$" <;> simp
    · intro hEq; subst hEq
      have : builtinHeads.contains "cons" = true := by decide
      simp_all
  · rw [hL] at hD; simp at hD

private abbrev theOBI := Session.optimizedBackendInterface

/-- Under noOverlap and builtin `ctor`, `stepTranslateCall` returns `[]`. -/
theorem stepTranslateCall_empty_of_noOverlap_builtin
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hNoOverlap : theOBI.noDeterministicReducerOverlap s = true)
    (hBuiltin : builtinHeads.contains ctor = true) :
    Session.stepTranslateCall s (.apply ctor argsV) = [] := by
  have hRules := Session.noOverlap_implies_disjoint_rules s hNoOverlap
  exact Semantics.TranslatorOps.translateCall_empty_of_no_head_match
    _ s _ ctor argsV
    (fun r hr => by
      have hD := hRules r hr
      obtain ⟨hHead, hNoFvar⟩ := ruleDisjointFromBuiltins_conditions r hD ctor hBuiltin
      exact ⟨fun h as hL => ⟨(hHead h as hL).1, (hHead h as hL).2.1⟩, hNoFvar⟩)

/-- Under noOverlap and builtin `ctor`, `stepCompatRewrite` returns `[]`. -/
theorem stepCompatRewrite_empty_of_noOverlap_builtin
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hNoOverlap : theOBI.noDeterministicReducerOverlap s = true)
    (hBuiltin : builtinHeads.contains ctor = true) :
    Session.stepCompatRewrite s (.apply ctor argsV) = [] := by
  have hRules := Session.noOverlap_implies_disjoint_rules s hNoOverlap
  exact Semantics.Dispatch.compatRewriteStep_empty_of_disjoint_heads
    _ s ctor argsV
    (fun r hr => ruleDisjointFromBuiltins_conditions r (hRules r hr) ctor hBuiltin)
    (fun h pArgs hNe hNCons => matchPatternMeTTa_diff_head h ctor pArgs argsV hNe hNCons)
    (fun p hNotApply hNotFvar => matchPatternMeTTa_nonApply_apply p ctor argsV hNotApply hNotFvar)

open MeTTailCore.MeTTaIL.Match in
open MeTTailCore.MeTTaIL.Engine in
/-- Under noOverlap and builtin `ctor`, `stepGeneratedRewrite` returns `[]`. -/
theorem stepGeneratedRewrite_empty_of_noOverlap_builtin
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hNoOverlap : theOBI.noDeterministicReducerOverlap s = true)
    (hBuiltin : builtinHeads.contains ctor = true) :
    Session.stepGeneratedRewrite s (.apply ctor argsV) = [] := by
  have hRules := Session.noOverlap_implies_disjoint_rules s hNoOverlap
  -- Each rule's matchPattern returns [] against builtin-headed term
  have hMatchNil : ∀ r ∈ s.bundle.language.rewrites,
      matchPattern r.left (.apply ctor argsV) = [] := by
    intro r hr
    have hD := hRules r hr
    obtain ⟨hHead, hNoFvar⟩ := ruleDisjointFromBuiltins_conditions r hD ctor hBuiltin
    cases hL : r.left with
    | apply h as =>
        exact matchPattern_diff_head h ctor as argsV (hHead h as hL).1
    | fvar x => exact absurd hL (hNoFvar x)
    | bvar n => exact matchPattern_nonApply_apply _ ctor argsV (fun h as hc => by cases hc) (fun x hc => by cases hc)
    | lambda body => exact matchPattern_nonApply_apply _ ctor argsV (fun h as hc => by cases hc) (fun x hc => by cases hc)
    | multiLambda n body => exact matchPattern_nonApply_apply _ ctor argsV (fun h as hc => by cases hc) (fun x hc => by cases hc)
    | subst body repl => exact matchPattern_nonApply_apply _ ctor argsV (fun h as hc => by cases hc) (fun x hc => by cases hc)
    | collection ct elems rest => exact matchPattern_nonApply_apply _ ctor argsV (fun h as hc => by cases hc) (fun x hc => by cases hc)
  -- stepGeneratedRewrite = SpecBundle.rewriteWithContext = flatMap over rules via matchPattern
  -- Each rule contributes [] because matchPattern returns []
  show MeTTailCore.MeTTaIL.Profile.SpecBundle.rewriteWithContext s.bundle (.apply ctor argsV) = []
  unfold MeTTailCore.MeTTaIL.Profile.SpecBundle.rewriteWithContext
  simp only [rewriteWithContextWithPremisesUsing, rewriteStepWithPremisesUsing, List.append_nil]
  apply Algorithms.MeTTa.Simple.Semantics.TranslatorOps.flatMap_eq_nil_of_forall
  intro rule hrule
  simp only [applyRuleWithPremisesUsing, hMatchNil rule hrule, List.flatMap_nil]

/-- Under noOverlap and builtin ctor, `StrictContext` holds:
    translateCall, compatRewrite, and generatedRewrite are all empty. -/
theorem strictContext_of_noOverlap_builtin
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hNoOverlap : theOBI.noDeterministicReducerOverlap s = true)
    (hBuiltin : builtinHeads.contains ctor = true)
    (hIrreducible : ∀ a ∈ argsV, Session.step s a = []) :
    StrictContext s ctor argsV :=
  { noTranslate := stepTranslateCall_empty_of_noOverlap_builtin s ctor argsV hNoOverlap hBuiltin
    noCompat := stepCompatRewrite_empty_of_noOverlap_builtin s ctor argsV hNoOverlap hBuiltin
    noGenerated := stepGeneratedRewrite_empty_of_noOverlap_builtin s ctor argsV hNoOverlap hBuiltin
    argsIrreducible := hIrreducible }

/-- Under noOverlap, builtin ctor, and `CoreIntrinsicDirectSingleton`, `step` returns
    at most one result.  This is the key bridge from singleton semantics to step cardinality. -/
theorem step_length_le_one_of_noOverlap_builtin
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hNoOverlap : theOBI.noDeterministicReducerOverlap s = true)
    (hBuiltin : builtinHeads.contains ctor = true)
    (hIrreducible : ∀ a ∈ argsV, Session.step s a = [])
    (hCore : CoreIntrinsicDirectSingleton s) :
    (Session.step s (.apply ctor argsV)).length ≤ 1 := by
  have hCtx := strictContext_of_noOverlap_builtin s ctor argsV hNoOverlap hBuiltin hIrreducible
  rw [step_eq_intrinsicDirect_of_strict s ctor argsV hCtx]
  exact hCore ctor argsV

end Algorithms.MeTTa.Simple.Backend.DeterministicBridge
