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
-- SessionRefinement imported for DeterministicAcceptedRaw (used in target theorem)
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

-- ─── Target theorem ────────────────────────────────────────────────────────
-- TRUTH AUDIT RESULT: raw hAgreeRaw is FALSE (3rd falsity vector confirmed).
-- The target is now `hAgreeSupported` gated by `SupportedDeterministic`.
-- Safe branches: directIntrinsic, unchanged, partialBuiltin, partialArity.
-- Unsafe branches (translated, firstRule): BLOCKED until RootExclusiveDeterministic added.

end Algorithms.MeTTa.Simple.Backend.DeterministicBridge
