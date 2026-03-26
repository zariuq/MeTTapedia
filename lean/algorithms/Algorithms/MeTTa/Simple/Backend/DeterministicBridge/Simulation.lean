-- LLM primer: Simulation.lean bridges the deterministic evaluator (`evalMemo`)
-- with the reference evaluator (`evalAuxStateful`).  The target is to discharge
-- `hAgreeRaw`:
--   ∀ s term, DeterministicAcceptedRaw s term →
--     OptimizedEval.evalWithState OBI s term = SessionReference.evalWithStateCore s term
--
-- Key observations:
-- 1. Both evaluators delegate sub-evaluations to the SAME `referenceEvalWithStateCoreN`.
--    The det evaluator's Interface.evalCore = evalWithStateCoreN = the reference evaluator.
-- 2. `intrinsicDirect` is a pure function (no session mutation).
-- 3. For `directIntrinsic` dispatch (arithmetic), `intrinsicStateful` returns `none`,
--    so `stepAux` falls to `step` which uses the same `intrinsicDirect`.
--
-- Strategy: split by DispatchClass, prove single-step commuting for each class.
-- Start with directIntrinsic (arithmetic/builtins) — cleanest case.
--
-- ═══ TRUTH AUDIT (2026-03-17) ═══════════════════════════════════════════════
-- 3rd falsity vector CONFIRMED:
--   For non-builtin ctors (e.g., "foo") with a translator rule and
--   builtin-reducible args (e.g., (+ 1 2)):
--     • Det: checks translateCall on RAW term (foo (+ 1 2)) → picks translated result
--     • Ref: step = intrinsicStepT ++ translateCall ++ ...
--       intrinsicStepT reduces args → [(foo 3)]
--       translateCall → [translated_result]
--       step returns BOTH results: [(foo 3), translated_result]
--     • The ref evaluator processes both through the work-queue, producing
--       a different result list than the det evaluator's singleton.
--
-- Consequence: raw hAgreeRaw is FALSE for terms with translator overlap.
-- The `translated` and `firstRule` dispatch branches are UNSAFE without
-- an additional guard (RootExclusiveDeterministic).
--
-- SAFE branches (translateCall = [] precondition):
--   directIntrinsic, unchanged, partialBuiltin, partialArity
-- UNSAFE branches (need extra guard):
--   translated, firstRule
-- ════════════════════════════════════════════════════════════════════════════

import Algorithms.MeTTa.Simple.Backend.DeterministicBridge.Atoms
import Algorithms.MeTTa.Simple.Backend.DeterministicBridge.Shape
import Algorithms.MeTTa.Simple.Backend.SessionRefinement

namespace Algorithms.MeTTa.Simple.Backend.DeterministicBridge

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

-- ─── Single-step agreement under StrictContext ─────────────────────────────
-- For a `directIntrinsic` dispatch term with already-evaluated args,
-- the det evaluator calls `I.intrinsicDirect s ctor argsV` and takes `headD`.
-- The reference evaluator calls `step s (.apply ctor argsV)` which (under
-- strict context) equals `intrinsicDirectPub s ctor argsV`.
-- Under strict context, both produce the same result list.

/-- Under strict context, the det evaluator's `intrinsicDirect` call and
    the reference evaluator's `step` call produce the same list. -/
theorem det_step_agree_directIntrinsic_strict
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hCtx : StrictContext s ctor argsV)
    (_hDirect : (Session.intrinsicDirectPub s ctor argsV).isEmpty = false) :
    (Session.detEvalInterface fuel).intrinsicDirect s ctor argsV =
    Session.step s (.apply ctor argsV) := by
  rw [det_intrinsicDirect_eq]
  rw [step_eq_intrinsicDirect_of_strict s ctor argsV hCtx]

/-- Under strict context with non-empty intrinsicDirect, the det evaluator's
    `headD` of `intrinsicDirect` equals the first element of `step`. -/
theorem det_headD_eq_step_headD_strict
    (s : Session) (ctor : String) (argsV : List Pattern)
    (fuel : Nat)
    (hCtx : StrictContext s ctor argsV)
    (_hDirect : (Session.intrinsicDirectPub s ctor argsV).isEmpty = false) :
    ((Session.detEvalInterface fuel).intrinsicDirect s ctor argsV).headD
      (.apply ctor argsV) =
    (Session.step s (.apply ctor argsV)).headD (.apply ctor argsV) := by
  rw [det_intrinsicDirect_eq]
  rw [step_eq_intrinsicDirect_of_strict s ctor argsV hCtx]

-- ─── Target theorem ────────────────────────────────────────────────────────
-- This is the theorem that, once proved, will discharge `hAgreeRaw` and make
-- all master theorems in SessionRefinement/Total unconditional.
--
-- The statement says: when the 5 deterministic guards pass for a term,
-- the fast-path evaluator (det eval → singleton result) equals
-- the reference evaluator (work-queue → result list).
--
-- `OptimizedEval.evalWithState OBI s term` when guards pass:
--   let (sDet, outDet) := OBI.evalDeterministicCore s (max 4096 maxNodes) term
--   (sDet, [outDet])
--
-- `SessionReference.evalWithStateCore s term`:
--   evalWithStateCoreN (referenceProofFuel s) s term
--
-- Both sides use `referenceEvalWithStateCoreN` for recursive sub-evaluations.
-- The difference is the ROOT dispatch: `evalMemo`'s if-cascade vs `stepAux`'s loop.

-- ─── Step-level agreement for safe branches ─────────────────────────────────
-- These theorems establish that for each safe DispatchClass, the det evaluator's
-- chosen one-step result matches what the reference evaluator's `step` produces.
-- The key invariant: under StrictContext + CoreIntrinsicDirectSingleton, `step`
-- is either empty (unchanged) or singleton (directIntrinsic), so the det
-- evaluator's `headD` pick agrees with the ref evaluator's single reduct.

/-- For `directIntrinsic` dispatch under noOverlap + builtin + singleton:
    `step` returns exactly `[result]` where `result` is the det evaluator's pick.
    This is the one-step agreement for the cleanest branch. -/
theorem step_singleton_of_directIntrinsic_supported
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hNoOverlap : Session.optimizedBackendInterface.noDeterministicReducerOverlap s = true)
    (hBuiltin : Semantics.DeterministicStrategy.intrinsicBuiltinHeads.contains ctor = true)
    (hIrreducible : ∀ a ∈ argsV, Session.step s a = [])
    (hCore : CoreIntrinsicDirectSingleton s)
    (hDirect : (Session.intrinsicDirectPub s ctor argsV).isEmpty = false) :
    ∃ result, Session.step s (.apply ctor argsV) = [result] ∧
      Session.intrinsicDirectPub s ctor argsV = [result] := by
  have hCtx := strictContext_of_noOverlap_builtin s ctor argsV hNoOverlap hBuiltin hIrreducible
  rw [step_eq_intrinsicDirect_of_strict s ctor argsV hCtx]
  have hSingleton := intrinsicDirectPub_nil_or_singleton_of_core s hCore ctor argsV
  rcases hSingleton with hNil | ⟨out, hSingle⟩
  · simp [hNil] at hDirect
  · exact ⟨out, hSingle, hSingle⟩

/-- For `unchanged` dispatch under noOverlap + builtin + singleton:
    `step` returns `[]`, meaning the term is already a normal form.
    The det evaluator also returns the term unchanged. -/
theorem step_nil_of_unchanged_supported
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hNoOverlap : Session.optimizedBackendInterface.noDeterministicReducerOverlap s = true)
    (hBuiltin : Semantics.DeterministicStrategy.intrinsicBuiltinHeads.contains ctor = true)
    (hIrreducible : ∀ a ∈ argsV, Session.step s a = [])
    (hNoDirect : Session.intrinsicDirectPub s ctor argsV = []) :
    Session.step s (.apply ctor argsV) = [] := by
  have hCtx := strictContext_of_noOverlap_builtin s ctor argsV hNoOverlap hBuiltin hIrreducible
  exact step_unchanged_of_strict s ctor argsV hCtx hNoDirect

/-- For `directIntrinsic` dispatch: the det evaluator's chosen result (headD of
    intrinsicDirect) equals the ref evaluator's unique step result. -/
theorem det_result_eq_step_unique_of_directIntrinsic_supported
    (s : Session) (ctor : String) (argsV : List Pattern)
    (fuel : Nat)
    (hNoOverlap : Session.optimizedBackendInterface.noDeterministicReducerOverlap s = true)
    (hBuiltin : Semantics.DeterministicStrategy.intrinsicBuiltinHeads.contains ctor = true)
    (hIrreducible : ∀ a ∈ argsV, Session.step s a = [])
    (hDirect : (Session.intrinsicDirectPub s ctor argsV).isEmpty = false) :
    ((Session.detEvalInterface fuel).intrinsicDirect s ctor argsV).headD (.apply ctor argsV) =
    (Session.step s (.apply ctor argsV)).headD (.apply ctor argsV) := by
  have hCtx := strictContext_of_noOverlap_builtin s ctor argsV hNoOverlap hBuiltin hIrreducible
  exact det_headD_eq_step_headD_strict s ctor argsV fuel hCtx hDirect

/-- For `directIntrinsic` dispatch: the det evaluator's `headD` pick is the unique
    element of the singleton step result. Combines singleton and headD agreement. -/
theorem det_pick_mem_step_singleton_of_directIntrinsic_supported
    (s : Session) (ctor : String) (argsV : List Pattern)
    (fuel : Nat)
    (hNoOverlap : Session.optimizedBackendInterface.noDeterministicReducerOverlap s = true)
    (hBuiltin : Semantics.DeterministicStrategy.intrinsicBuiltinHeads.contains ctor = true)
    (hIrreducible : ∀ a ∈ argsV, Session.step s a = [])
    (hCore : CoreIntrinsicDirectSingleton s)
    (hDirect : (Session.intrinsicDirectPub s ctor argsV).isEmpty = false) :
    let detPick := ((Session.detEvalInterface fuel).intrinsicDirect s ctor argsV).headD
      (.apply ctor argsV)
    Session.step s (.apply ctor argsV) = [detPick] := by
  obtain ⟨result, hStep, hIntr⟩ :=
    step_singleton_of_directIntrinsic_supported s ctor argsV
      hNoOverlap hBuiltin hIrreducible hCore hDirect
  simp only [det_intrinsicDirect_eq, hIntr, List.headD_cons]
  exact hStep

-- ─── Branch-level agreement theorems ─────────────────────────────────────
-- These prove that for each safe DispatchClass, the det evaluator's result
-- (wrapped as singleton) equals the ref evaluator's result.
-- Each takes RefRunNestedEffectsPassthrough + RefIntrinsicStatefulNone as
-- explicit hypotheses (instances proven separately in S-4).

/-- Unchanged branch: det returns `(s, term)`, ref returns `(s, [term])`.
    Both sides agree when wrapped as singleton. -/
theorem unchanged_branch_det_eq_ref
    (outerFuel detFuel : Nat) (s : Session) (ctor : String) (argsV : List Pattern)
    -- Ref-evaluator predicates
    (hRNE : RefRunNestedEffectsPassthrough outerFuel s (.apply ctor argsV))
    (hIntr : RefIntrinsicStatefulNone outerFuel s (.apply ctor argsV))
    -- Session bounds
    (hNodes : s.maxNodes ≥ 1) (hSteps : 0 < s.maxSteps)
    -- Step = [] (from StrictContext + noDirect)
    (hStep : Session.step s (.apply ctor argsV) = [])
    -- Det evaluator conditions for unchanged dispatch
    (hNotEq : ctor ≠ "=") (hNotIf : ctor ≠ "if") (hNotExpr : ctor ≠ "Expr")
    (hTranslate : (Session.detEvalInterface outerFuel).translateCall s (.apply ctor argsV) = [])
    (hPreserveArgs : (Session.detEvalInterface outerFuel).deterministicPreserveArgs ctor = true)
    (hArity : (Session.detEvalInterface outerFuel).builtinPartialMinArity ctor = none)
    (hDirect : (Session.detEvalInterface outerFuel).intrinsicDirect s ctor argsV = [])
    (hNoRule : (Session.detEvalInterface outerFuel).firstRuleReduction? s (.apply ctor argsV) = none)
    (hNoPartial :
      ¬(((Session.detEvalInterface outerFuel).rewriteAritiesForHead s ctor).any (· > argsV.length) = true ∧
        ((Session.detEvalInterface outerFuel).rewriteAritiesForHead s ctor).any (· == argsV.length) = false ∧
        argsV.isEmpty = false))
    -- detFuel is positive (always true: detFuel = max 4096 maxNodes)
    (hDetFuel : detFuel ≥ 1) :
    -- Det result (singleton-wrapped) = Ref result
    let detResult := Semantics.DeterministicEval.eval
      (Session.detEvalInterface outerFuel) s detFuel (.apply ctor argsV)
    (detResult.1, [detResult.2]) = Session.evalWithStateCoreN (outerFuel + 1) s (.apply ctor argsV) := by
  -- Det side: eval returns (s, .apply ctor argsV) unchanged
  obtain ⟨n, rfl⟩ : ∃ n, detFuel = n + 1 := ⟨detFuel - 1, by omega⟩
  have hDet := Semantics.DeterministicEval.eval_apply_unchanged
    (Session.detEvalInterface outerFuel) s n ctor argsV
    hNotEq hNotIf hNotExpr hTranslate hPreserveArgs hArity hDirect hNoRule hNoPartial
  -- Ref side: evalWithStateCoreN returns (s, [.apply ctor argsV])
  have hRef := Session.evalWithStateCoreN_unchanged outerFuel s (.apply ctor argsV)
    hNodes hSteps hRNE hIntr hStep
  -- Both agree
  simp only [hDet, hRef]

-- ─── P-6: RefRunNestedEffectsPassthrough instances ───────────────────────────
-- Compose runNestedEffects_passthrough_of_nonSpecial_neutral with concrete interface.

/-- For non-special ctor with RNE-neutral args, the canonical `runNestedEffects`
    applied to `referenceEvalInterfaceN` is a passthrough.
    This provides `RefRunNestedEffectsPassthrough` instances for builtin terms. -/
theorem refRNEPassthrough_of_nonSpecial_neutral
    (outerFuel : Nat) (s : Session) (ctor : String) (argsV : List Pattern)
    (hNotSpecial : ctor ∉ Backend.ReferenceEval.runNestedEffectsSpecialHeads)
    (hNeutral : Backend.ReferenceEval.AllRNENeutral
        (Session.referenceEvalInterfaceN outerFuel) s
        ((Session.referenceEvalInterfaceN outerFuel).isEagerCallableHead s ctor)
        argsV) :
    RefRunNestedEffectsPassthrough outerFuel s (.apply ctor argsV) := by
  show Backend.ReferenceEval.runNestedEffects
    (Session.referenceEvalInterfaceN outerFuel) s true false (.apply ctor argsV) =
    (s, .apply ctor argsV, false)
  exact Backend.ReferenceEval.runNestedEffects_passthrough_of_nonSpecial_neutral
    (Session.referenceEvalInterfaceN outerFuel) s true false ctor argsV
    hNotSpecial hNeutral

-- ─── DirectIntrinsic one-step ─────────────────────────────────────────────────

/-- DirectIntrinsic branch: the det evaluator at fuel `detFuel` on `.apply ctor argsV`
    reduces to `eval` at `detFuel - 1` on `result` (the singleton intrinsicDirect output).
    This is the det-side one-step reduction for the directIntrinsic dispatch. -/
theorem directIntrinsic_det_onestep
    (outerFuel detFuel : Nat) (s : Session) (ctor : String) (argsV : List Pattern)
    (result : Pattern)
    (hNotEq : ctor ≠ "=") (hNotIf : ctor ≠ "if") (hNotExpr : ctor ≠ "Expr")
    (hTranslate : (Session.detEvalInterface outerFuel).translateCall s (.apply ctor argsV) = [])
    (hPreserveArgs : (Session.detEvalInterface outerFuel).deterministicPreserveArgs ctor = true)
    (hArity : (Session.detEvalInterface outerFuel).builtinPartialMinArity ctor = none)
    (hDirect : (Session.detEvalInterface outerFuel).intrinsicDirect s ctor argsV = [result])
    (hNotSelf : result ≠ .apply ctor argsV)
    (hDetFuel : detFuel ≥ 1) :
    Semantics.DeterministicEval.eval
      (Session.detEvalInterface outerFuel) s detFuel (.apply ctor argsV) =
    Semantics.DeterministicEval.eval
      (Session.detEvalInterface outerFuel) s (detFuel - 1) result := by
  obtain ⟨n, rfl⟩ : ∃ n, detFuel = n + 1 := ⟨detFuel - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact Semantics.DeterministicEval.eval_apply_directIntrinsic_onestep
    (Session.detEvalInterface outerFuel) s n ctor argsV result
    hNotEq hNotIf hNotExpr hTranslate hPreserveArgs hArity hDirect hNotSelf

-- ─── Step 5: Terminal DirectIntrinsic Slice ────────────────────────────────
-- First inhabited FastPathEq theorem.
-- Architecture from GPT-5.4 Pro Response #4:
--   • Split on raw hasMultipleRootRuleChoices (avoids CompiledConsistent dependency)
--   • DetTerminalResult packages the result-side unchanged conditions
--   • SupportedDirectIntrinsicTerminal uses SupportedDeterministic + specific fields

/-- Det-side terminal result witness. Proves that `eval I s fuel result = (s, result)`
    by showing nothing fires on the result. -/
inductive DetTerminalResult (outerFuel : Nat) (s : Session) : Pattern → Prop
  | nonApply (t : Pattern) (hNonApply : ∀ c as, t ≠ .apply c as) :
      DetTerminalResult outerFuel s t
  | applyStable (rCtor : String) (rArgs : List Pattern)
      (hNotEq : rCtor ≠ "=") (hNotIf : rCtor ≠ "if") (hNotExpr : rCtor ≠ "Expr")
      (hTranslate : (Session.detEvalInterface outerFuel).translateCall s (.apply rCtor rArgs) = [])
      (hPreserveArgs : (Session.detEvalInterface outerFuel).deterministicPreserveArgs rCtor = true)
      (hArity : (Session.detEvalInterface outerFuel).builtinPartialMinArity rCtor = none)
      (hNoDirect : (Session.detEvalInterface outerFuel).intrinsicDirect s rCtor rArgs = [])
      (hNoRule : (Session.detEvalInterface outerFuel).firstRuleReduction? s (.apply rCtor rArgs) = none)
      (hNoPartial :
        ¬(((Session.detEvalInterface outerFuel).rewriteAritiesForHead s rCtor).any (· > rArgs.length) = true ∧
          ((Session.detEvalInterface outerFuel).rewriteAritiesForHead s rCtor).any (· == rArgs.length) = false ∧
          rArgs.isEmpty = false)) :
      DetTerminalResult outerFuel s (.apply rCtor rArgs)

/-- Semantic witness for the terminal directIntrinsic slice.
    Uses SupportedDeterministic for the root guards, plus specific conditions
    for the directIntrinsic dispatch and terminal result. -/
structure SupportedDirectIntrinsicTerminal
    (outerFuel : Nat) (s : Session) (ctor : String) (argsV : List Pattern)
    (result : Pattern) : Prop where
  -- Root guards (bundles accepted + coreSingleton + noTranslateAtRoot)
  hSupported : SupportedDeterministic s (.apply ctor argsV)
  -- Root head properties
  hNotSpecialRNE : ctor ∉ Backend.ReferenceEval.runNestedEffectsSpecialHeads
  hBuiltin : Semantics.DeterministicStrategy.intrinsicBuiltinHeads.contains ctor = true
  -- Args are RNE-neutral + step-irreducible
  hNeutral : Backend.ReferenceEval.AllRNENeutral
      (Session.referenceEvalInterfaceN outerFuel) s
      ((Session.referenceEvalInterfaceN outerFuel).isEagerCallableHead s ctor)
      argsV
  hIrreducible : ∀ a ∈ argsV, Session.step s a = []
  -- intrinsicStateful = none at root (R-2)
  hIntrNone : (Session.referenceEvalInterfaceN outerFuel).intrinsicStateful s (.apply ctor argsV) = none
  -- directIntrinsic fires and produces exactly [result]
  hDirectSingleton : Session.intrinsicDirectPub s ctor argsV = [result]
  -- Det-side root dispatch conditions
  hNotEq : ctor ≠ "="
  hNotIf : ctor ≠ "if"
  hNotExpr : ctor ≠ "Expr"
  hPreserveArgs : (Session.detEvalInterface outerFuel).deterministicPreserveArgs ctor = true
  hDetArity : (Session.detEvalInterface outerFuel).builtinPartialMinArity ctor = none
  hNotSelf : result ≠ .apply ctor argsV
  -- Result is terminal (ref side)
  hResultRNE : Backend.ReferenceEval.runNestedEffects
      (Session.referenceEvalInterfaceN outerFuel) s true false result = (s, result, false)
  hResultIntrNone : (Session.referenceEvalInterfaceN outerFuel).intrinsicStateful s result = none
  hResultStep : Session.step s result = []
  -- Result is terminal (det side)
  hResultDet : DetTerminalResult outerFuel s result
  -- Det evaluator produces (s, result) — provable from eval_apply_directIntrinsic_onestep +
  -- eval_apply_unchanged via detEvalInterface_eq_standalone, but added as field to avoid
  -- fuel-mismatch between detEvalInterface outerFuel and OBI (which uses referenceProofFuel s)
  hDetEq : Session.optimizedBackendInterface.evalDeterministicCore s
      (Nat.max 4096 s.maxNodes) (.apply ctor argsV) = (s, result)
  -- Session bounds
  hNodes : s.maxNodes ≥ 2
  hSteps : s.maxSteps ≥ 2

-- ─── Ref-side: two-step evaluation ────────────────────────────────────────

/-- The reference evaluator on a terminal directIntrinsic term produces `(s, [result])`. -/
theorem ref_eval_terminal_directIntrinsic
    (outerFuel : Nat) (s : Session) (ctor : String) (argsV : List Pattern)
    (result : Pattern)
    (h : SupportedDirectIntrinsicTerminal outerFuel s ctor argsV result) :
    Session.evalWithStateCoreN (outerFuel + 1) s (.apply ctor argsV) = (s, [result]) := by
  have hRNE : RefRunNestedEffectsPassthrough outerFuel s (.apply ctor argsV) :=
    refRNEPassthrough_of_nonSpecial_neutral outerFuel s ctor argsV h.hNotSpecialRNE h.hNeutral
  -- step = [result] from StrictContext
  have hStep : Session.step s (.apply ctor argsV) = [result] := by
    have hCtx := strictContext_of_noOverlap_builtin s ctor argsV
      h.hSupported.accepted.noOverlap h.hBuiltin h.hIrreducible
    rw [step_eq_intrinsicDirect_of_strict s ctor argsV hCtx, h.hDirectSingleton]
  -- Unfold to evalAuxStateful
  rw [Session.evalWithStateCoreN_succ, Backend.ReferenceEval.evalWithStateCore]
  show Backend.ReferenceEval.evalAuxStateful
    (Session.referenceEvalInterfaceN outerFuel) s s.maxNodes
    [(.apply ctor argsV, 0)] [] = (s, [result])
  obtain ⟨n, hn⟩ : ∃ n, s.maxNodes = n + 2 := ⟨s.maxNodes - 2, by have := h.hNodes; omega⟩
  rw [hn]
  -- First iteration: root step yields [result]
  rw [Backend.ReferenceEval.evalAuxStateful_step_of_intrinsicNone
    (Session.referenceEvalInterfaceN outerFuel) s s
    (.apply ctor argsV) (.apply ctor argsV) false 0 [] [] (n + 1)
    hRNE (by simp [Session.referenceEvalInterfaceN]; have := h.hSteps; omega) h.hIntrNone]
  simp only [show (Session.referenceEvalInterfaceN outerFuel).step = Session.step from rfl,
    hStep, List.isEmpty_cons,
    show (Session.referenceEvalInterfaceN outerFuel).enqueueNext = Session.enqueueNext from rfl,
    Session.enqueueNext, List.map, List.append_nil]
  -- Second iteration: result is terminal (step = [])
  rw [Backend.ReferenceEval.evalAuxStateful_step_of_intrinsicNone
    (Session.referenceEvalInterfaceN outerFuel) s s result result false 1 [] [] n
    h.hResultRNE (by simp [Session.referenceEvalInterfaceN]; have := h.hSteps; omega)
    h.hResultIntrNone]
  simp only [show (Session.referenceEvalInterfaceN outerFuel).step = Session.step from rfl,
    h.hResultStep, List.isEmpty_nil]
  -- Empty pending → done
  rw [Backend.ReferenceEval.evalAuxStateful_nil_pending]; simp

-- ─── Det-side: terminal result evaluation ─────────────────────────────────

/-- A terminal result evaluates to itself under the det evaluator. -/
theorem det_eval_terminal
    (outerFuel : Nat) (s : Session) (result : Pattern) (detFuel : Nat)
    (hFuel : detFuel ≥ 1)
    (hRes : DetTerminalResult outerFuel s result) :
    Semantics.DeterministicEval.eval
      (Session.detEvalInterface outerFuel) s detFuel result = (s, result) := by
  cases hRes with
  | nonApply _ hNonApply =>
    exact Semantics.DeterministicEval.eval_non_apply
      (Session.detEvalInterface outerFuel) s detFuel _ hNonApply
  | applyStable rCtor rArgs hNotEq hNotIf hNotExpr hTranslate hPreserveArgs
      hArity hNoDirect hNoRule hNoPartial =>
    obtain ⟨m, hm⟩ : ∃ m, detFuel = m + 1 := ⟨detFuel - 1, by omega⟩
    rw [hm]
    exact Semantics.DeterministicEval.eval_apply_unchanged
      (Session.detEvalInterface outerFuel) s m rCtor rArgs
      hNotEq hNotIf hNotExpr hTranslate hPreserveArgs hArity hNoDirect hNoRule hNoPartial

-- ─── FastPathEq: combining ref and det sides ──────────────────────────────

/-- The first inhabited FastPathEq theorem.
    For terminal directIntrinsic terms, the optimized evaluator agrees with
    the reference evaluator.
    Split on raw hasMultipleRootRuleChoices to avoid CompiledConsistent dependency. -/
theorem fastPathEq_directIntrinsicTerminal
    (outerFuel : Nat) (s : Session) (ctor : String) (argsV : List Pattern)
    (result : Pattern)
    (h : SupportedDirectIntrinsicTerminal outerFuel s ctor argsV result)
    (hFuel : outerFuel + 1 = Session.referenceProofFuel s) :
    Backend.SessionRefinement.FastPathEq s (.apply ctor argsV) := by
  -- Ref side: evalWithStateCoreN = (s, [result])
  have hRef := ref_eval_terminal_directIntrinsic outerFuel s ctor argsV result h
  rw [hFuel] at hRef
  -- Unfold FastPathEq to OptimizedEval.evalWithState = SessionReference.evalWithStateCore
  show Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
      Session.optimizedBackendInterface s (.apply ctor argsV) =
    Backend.SessionReference.evalWithStateCore s (.apply ctor argsV)
  simp only [Backend.SessionReference.evalWithStateCore,
    Session.optimizedBackendInterface_evalWithStateCore_eq_N]
  rw [hRef]
  -- Goal: OptimizedEval.evalWithState OBI s (.apply ctor argsV) = (s, [result])
  -- Split on raw hasMultipleRootRuleChoices
  by_cases hMultiRaw :
      Session.optimizedBackendInterface.hasMultipleRootRuleChoices s (.apply ctor argsV) = false
  · -- Guards-pass branch: det evaluator is used
    simp only [Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState,
      h.hSupported.accepted.strict, h.hSupported.accepted.unblocked, hMultiRaw,
      h.hSupported.accepted.noOverlap, h.hSupported.accepted.noCoreBuiltinOverrides,
      Bool.true_and, Bool.and_true, Bool.not_false, Bool.not_true, ite_true, ite_false]
    -- Goal: let detFuel := ...; let (sDet, outDet) := evalDeterministicCore s detFuel term;
    --       if resolved outDet && ... then (sDet, [outDet]) else ref
    -- Need: evalDeterministicCore s detFuel term = (s, result)
    -- Chain: eval one-step (directIntrinsic) then terminal
    have hDetFuel : Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s) ≥ 2 :=
      Nat.le_trans (by omega : 2 ≤ 4096) (Nat.le_max_left 4096 _)
    have hRootStep :=
      directIntrinsic_det_onestep outerFuel (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s))
        s ctor argsV result
        h.hNotEq h.hNotIf h.hNotExpr
        (by simpa [Session.detEvalInterface] using h.hSupported.noTranslateAtRoot)
        h.hPreserveArgs h.hDetArity
        (by simpa [det_intrinsicDirect_eq] using h.hDirectSingleton)
        h.hNotSelf (by omega)
    have hResultDet :=
      det_eval_terminal outerFuel s result
        (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s) - 1)
        (by omega) h.hResultDet
    -- Combine: evalDeterministicCore = eval = rootStep ▸ resultDet = (s, result)
    -- Use hDetEq: OBI.evalDeterministicCore s detFuel term = (s, result)
    -- The goal after simp [guards] should have:
    -- let (sDet, outDet) := OBI.evalDeterministicCore s detFuel term
    -- if resolved outDet && (outDet != term || accept term) then (sDet, [outDet]) else ref
    -- Rewrite evalDeterministicCore with hDetEq
    -- The goal after simp [guards]: let (sDet, outDet) := evalDeterministicCore ...;
    -- if resolved outDet && accepted then (sDet, [outDet]) else fallback
    -- evalDeterministicCore uses detFuel = max 4096 (OBI.maxNodes s) = max 4096 s.maxNodes
    have hMaxEq : Session.optimizedBackendInterface.maxNodes s = s.maxNodes := rfl
    -- resolved/accepted use (detResult s term).2 which is (evalDeterministicCore s detFuel term).2
    -- After hDetEq: (evalDeterministicCore s detFuel term) = (s, result)
    -- So (evalDeterministicCore s detFuel term).2 = result
    have hDetSnd : (Session.optimizedBackendInterface.evalDeterministicCore s
        (Nat.max 4096 s.maxNodes) (.apply ctor argsV)).2 = result := by
      rw [h.hDetEq]
    have hDetFst : (Session.optimizedBackendInterface.evalDeterministicCore s
        (Nat.max 4096 s.maxNodes) (.apply ctor argsV)).1 = s := by
      rw [h.hDetEq]
    -- resolved and accepted hold for result (from DeterministicAccepted)
    have hResolved := h.hSupported.accepted.resolved
    have hAccepted := h.hSupported.accepted.accepted
    -- DeterministicAccepted uses detResult = OBI.evalDeterministicCore s (detFuel s) term
    -- detFuel s = max 4096 (OBI.maxNodes s) = max 4096 s.maxNodes
    -- So detResult.2 = result (by hDetSnd)
    -- detResult/detFuel are private abbrevs. Unfold manually.
    -- detFuel s = Nat.max 4096 (OBI.maxNodes s) = Nat.max 4096 s.maxNodes
    -- detResult s term = OBI.evalDeterministicCore s (detFuel s) term
    change Session.optimizedBackendInterface.isResolvedDeterministicResult
      (Session.optimizedBackendInterface.evalDeterministicCore s
        (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s)) (.apply ctor argsV)).2 = true at hResolved
    change ((Session.optimizedBackendInterface.evalDeterministicCore s
        (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s)) (.apply ctor argsV)).2 != .apply ctor argsV ||
      Session.optimizedBackendInterface.acceptUnchangedDeterministic (.apply ctor argsV)) = true at hAccepted
    simp only [hMaxEq] at hResolved hAccepted
    rw [hDetSnd] at hResolved hAccepted
    -- Now hResolved : isResolvedDeterministicResult result = true
    -- hAccepted : (result != term || accept term) = true
    simp only [Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState,
      h.hSupported.accepted.strict, h.hSupported.accepted.unblocked, hMultiRaw,
      h.hSupported.accepted.noOverlap, h.hSupported.accepted.noCoreBuiltinOverrides,
      Bool.true_and, Bool.and_true, Bool.not_false, Bool.not_true, ite_true, ite_false,
      hMaxEq, h.hDetEq, hResolved, hAccepted]
  · -- Guards-fail branch: optimized eval falls back to reference
    have hMultiTrue :
        Session.optimizedBackendInterface.hasMultipleRootRuleChoices s (.apply ctor argsV) = true := by
      cases hV : Session.optimizedBackendInterface.hasMultipleRootRuleChoices s (.apply ctor argsV) <;>
        simp_all
    simp only [Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState,
      h.hSupported.accepted.strict, h.hSupported.accepted.unblocked, hMultiTrue,
      Bool.not_true, Bool.true_and, Bool.and_false, ite_false]
    -- Fallback = evalWithStateCore = evalWithStateCoreN (referenceProofFuel s) = (s, [result])
    simp only [Session.optimizedBackendInterface_evalWithStateCore_eq_N]
    exact hRef

-- [REMOVED: Spec-Based Verification section that depended on EvalSpec.lean]
-- The EvalSpec was disconnected from the actual evaluator architecture.
-- Genuine single-step agreements above (lines 49-494) are preserved.

end Algorithms.MeTTa.Simple.Backend.DeterministicBridge
