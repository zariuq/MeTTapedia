-- LLM primer: Atoms.lean establishes that `detEvalInterface` fields are
-- definitionally equal to the `*Pub` wrappers from Session.lean.  These are
-- thin `rfl` lemmas — the real work is making the correspondence explicit
-- so Simulation.lean can rewrite cleanly.
--
-- Additionally provides the `translateCall` field ↔ `stepTranslateCall`
-- correspondence and the `translateCallFor` ↔ det interface correspondence.

import Algorithms.MeTTa.Simple.Backend.DeterministicBridge.Basics

namespace Algorithms.MeTTa.Simple.Backend.DeterministicBridge

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

-- ─── Det interface field = public wrapper (all rfl) ────────────────────────

/-- The det evaluator's `intrinsicDirect` field is the public wrapper. -/
theorem det_intrinsicDirect_eq (fuel : Nat) :
    (Session.detEvalInterface fuel).intrinsicDirect = Session.intrinsicDirectPub := by
  rfl

/-- The det evaluator's `firstRuleReduction?` field is the public wrapper. -/
theorem det_firstRuleReduction_eq (fuel : Nat) :
    (Session.detEvalInterface fuel).firstRuleReduction? = Session.firstRuleReductionPub := by
  rfl

/-- The det evaluator's `builtinPartialMinArity` field is the public wrapper. -/
theorem det_builtinPartialMinArity_eq (fuel : Nat) :
    (Session.detEvalInterface fuel).builtinPartialMinArity = Session.builtinPartialMinArityPub := by
  rfl

/-- The det evaluator's `rewriteAritiesForHead` field is the public wrapper. -/
theorem det_rewriteAritiesForHead_eq (fuel : Nat) :
    (Session.detEvalInterface fuel).rewriteAritiesForHead = Session.rewriteAritiesForHeadPub := by
  rfl

/-- The det evaluator's `partialPattern` field is the public wrapper. -/
theorem det_partialPattern_eq (fuel : Nat) :
    (Session.detEvalInterface fuel).partialPattern = Session.partialPatternPub := by
  rfl

-- ─── translateCall correspondence ──────────────────────────────────────────

/-- The det evaluator's `translateCall` field matches `stepTranslateCall`. -/
theorem det_translateCall_eq (fuel : Nat) (s : Session) (term : Pattern) :
    (Session.detEvalInterface fuel).translateCall s term =
    Session.stepTranslateCall s term := by
  rfl

/-- `translateCallFor` (from Basics.lean) equals the det evaluator's translateCall. -/
theorem translateCallFor_eq_det (fuel : Nat) (s : Session)
    (ctor : String) (argsV : List Pattern) :
    translateCallFor s ctor argsV =
    (Session.detEvalInterface fuel).translateCall s (.apply ctor argsV) := by
  rfl

-- ─── Dispatch class → det interface preconditions ──────────────────────────
-- These lemmas let Simulation.lean translate a DispatchClass witness into
-- the exact `if`-conditions that `DeterministicEval.evalMemo` checks.

/-- For `directIntrinsic` dispatch: the det evaluator's `intrinsicDirect` is non-empty. -/
theorem det_intrinsicDirect_nonempty_of_directIntrinsic
    {s : Session} {ctor : String} {argsV : List Pattern}
    (fuel : Nat)
    (hDirect : (Session.intrinsicDirectPub s ctor argsV).isEmpty = false) :
    ((Session.detEvalInterface fuel).intrinsicDirect s ctor argsV).isEmpty = false := by
  rw [det_intrinsicDirect_eq]; exact hDirect

/-- For `directIntrinsic` dispatch: translateCall is empty. -/
theorem det_translateCall_empty_of_noTranslate
    {s : Session} {ctor : String} {argsV : List Pattern}
    (fuel : Nat)
    (hT : translateCallFor s ctor argsV = []) :
    (Session.detEvalInterface fuel).translateCall s (.apply ctor argsV) = [] := by
  rw [← translateCallFor_eq_det fuel]; exact hT

/-- For `firstRule` dispatch: the det evaluator's `firstRuleReduction?` gives `some rhs`. -/
theorem det_firstRuleReduction_some_of_firstRule
    {s : Session} {ctor : String} {argsV : List Pattern}
    (fuel : Nat) (rhs : Pattern)
    (hRule : Session.firstRuleReductionPub s (.apply ctor argsV) = some rhs) :
    (Session.detEvalInterface fuel).firstRuleReduction? s (.apply ctor argsV) = some rhs := by
  rw [det_firstRuleReduction_eq]; exact hRule

/-- For `unchanged` dispatch: intrinsicDirect is empty. -/
theorem det_intrinsicDirect_empty_of_noDirect
    {s : Session} {ctor : String} {argsV : List Pattern}
    (fuel : Nat)
    (hD : Session.intrinsicDirectPub s ctor argsV = []) :
    (Session.detEvalInterface fuel).intrinsicDirect s ctor argsV = [] := by
  rw [det_intrinsicDirect_eq]; exact hD

/-- For `unchanged` dispatch: firstRuleReduction? is none. -/
theorem det_firstRuleReduction_none_of_noRule
    {s : Session} {ctor : String} {argsV : List Pattern}
    (fuel : Nat)
    (hR : Session.firstRuleReductionPub s (.apply ctor argsV) = none) :
    (Session.detEvalInterface fuel).firstRuleReduction? s (.apply ctor argsV) = none := by
  rw [det_firstRuleReduction_eq]; exact hR

end Algorithms.MeTTa.Simple.Backend.DeterministicBridge
