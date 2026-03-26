import Algorithms.MeTTa.Simple.Session
import Algorithms.MeTTa.Simple.Backend.SessionRefinement

namespace Algorithms.MeTTa.Simple.Backend.DeterministicBridge

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

-- ─── Abbreviations ───────────────────────────────────────────────────────────

private abbrev OBI := Session.optimizedBackendInterface

private abbrev detFuel (s : Session) : Nat :=
  Nat.max 4096 (OBI.maxNodes s)

private abbrev detResult (s : Session) (term : Pattern) : Session × Pattern :=
  OBI.evalDeterministicCore s (detFuel s) term

-- ─── Singleton semantic predicate ───────────────────────────────────────────

/-- Semantic predicate: `intrinsicDirectPub` returns at most one result for every call.
    This is the proof-layer invariant; the runtime flag `noCoreBuiltinOverrides` is a
    Bool approximation.  Bridge theorems connect the two separately.
    Use this predicate in bridge proofs — never the raw Bool flag directly. -/
def CoreIntrinsicDirectSingleton (s : Session) : Prop :=
  ∀ ctor args, (Session.intrinsicDirectPub s ctor args).length ≤ 1

-- ─── Builtin surface predicate ──────────────────────────────────────────────
-- Bridges the runtime Bool flag to the semantic singleton invariant.
-- States that for all intrinsic:* relations, the session's builtin table
-- returns at most one row — matching the core builtins' behavior.

/-- The session's builtin table returns ≤1 row for every `intrinsic:*` relation.
    This holds when builtins are `coreIntrinsicBuiltins` (possibly merged with
    user builtins that don't define `intrinsic:*` relations). -/
def CoreBuiltinSurface (s : Session) : Prop :=
  ∀ rel args, (s.bundle.builtins.relation (intrinsicRelationName rel) args).length ≤ 1

/-- `CoreBuiltinSurface` implies `CoreIntrinsicDirectSingleton`.
    Pure math: `intrinsicDirectPub` is `filterMap` over the builtin rows,
    so its length is bounded by the row count. -/
theorem coreIntrinsicDirectSingleton_of_surface
    (s : Session) (hSurf : CoreBuiltinSurface s) :
    CoreIntrinsicDirectSingleton s := by
  intro ctor args
  exact Nat.le_trans (Session.intrinsicDirectPub_length_le s ctor args) (hSurf ctor args)

/-- Sessions whose builtins ARE `coreIntrinsicBuiltins` satisfy `CoreBuiltinSurface`. -/
theorem coreBuiltinSurface_of_coreBuiltins
    (s : Session) (hB : s.bundle.builtins = coreIntrinsicBuiltins) :
    CoreBuiltinSurface s := by
  intro rel args
  simp [hB]
  exact coreIntrinsicBuiltins_relation_length_le_one (intrinsicRelationName rel) args

/-- For sessions built with `mergeBuiltinTables coreIntrinsicBuiltins extra` where
    `extra` returns `[]` for all `intrinsic:*` relations, `CoreBuiltinSurface` holds. -/
theorem coreBuiltinSurface_of_merge_noIntrinsic
    (s : Session)
    (extra : MeTTailCore.MeTTaIL.Profile.BuiltinTable)
    (hB : s.bundle.builtins = mergeBuiltinTables coreIntrinsicBuiltins extra)
    (hExtra : ∀ rel args, extra.relation (intrinsicRelationName rel) args = []) :
    CoreBuiltinSurface s := by
  intro rel args
  simp [hB, mergeBuiltinTables, hExtra]
  exact coreIntrinsicBuiltins_relation_length_le_one (intrinsicRelationName rel) args

-- ─── Witness structure ───────────────────────────────────────────────────────

/-- Structured version of the 7 deterministic-acceptance guards.
    Each field corresponds to one guard in `OptimizedEval.evalWithState`. -/
structure DeterministicAccepted (s : Session) (term : Pattern) : Prop where
  strict : OBI.shouldUseDeterministicInStrict term = true
  unblocked : OBI.hasDeterministicBlockingRewriteBodies s = false
  uniqueRoot : OBI.hasMultipleRootRuleChoices (Session.withCompiledIndexes s false) term = false
  noOverlap : OBI.noDeterministicReducerOverlap s = true
  noCoreBuiltinOverrides : OBI.noCoreBuiltinOverrides s = true
  resolved : OBI.isResolvedDeterministicResult (detResult s term).2 = true
  accepted : ((detResult s term).2 != term || OBI.acceptUnchangedDeterministic term) = true

/-- `DeterministicAccepted` is equivalent to `SessionRefinement.DeterministicAcceptedRaw`. -/
theorem DeterministicAccepted_iff_Raw (s : Session) (term : Pattern) :
    DeterministicAccepted s term ↔
      Backend.SessionRefinement.DeterministicAcceptedRaw s term :=
  ⟨fun ⟨h1, h2, h3, h4, h4b, h5, h6⟩ => ⟨h1, h2, h3, h4, h4b, h5, h6⟩,
   fun ⟨h1, h2, h3, h4, h4b, h5, h6⟩ => ⟨h1, h2, h3, h4, h4b, h5, h6⟩⟩

-- ─── Ref-evaluator semantic predicates (Option E: canonical abstract semantics) ──
-- These capture ref-evaluator behavior that the simulation proof needs.
-- Stated in terms of the CANONICAL `ReferenceEval` functions applied to the
-- named `referenceEvalInterfaceN` — NOT the copied `referenceRunNestedEffectsN`.
-- See GPT-5.4 Pro Option E rationale.

/-- At the root level, `intrinsicStateful` (interface field) returns `none` for this term.
    Holds for arithmetic/comparison builtins not handled by PeTTaCore/StateEffects/etc.
    Uses the interface field directly — no impedance mismatch (GPT-5.4 Pro confirmed). -/
def RefIntrinsicStatefulNone (outerFuel : Nat) (s : Session) (term : Pattern) : Prop :=
  (Session.referenceEvalInterfaceN outerFuel).intrinsicStateful s term = none

/-- At the root level, the canonical `ReferenceEval.runNestedEffects` is a passthrough:
    returns `(s, term, false)` without modifying state or term.
    Uses the abstract FUNCTION (not the interface field) — this is what `stepAux` calls. -/
def RefRunNestedEffectsPassthrough (outerFuel : Nat) (s : Session) (term : Pattern) : Prop :=
  Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
    (Session.referenceEvalInterfaceN outerFuel) s true false term = (s, term, false)

-- ─── Supported witness (semantic refinement of DeterministicAccepted) ────────

/-- Semantic witness for the deterministic fast-path correctness argument.
    Extends `DeterministicAccepted` with proof-layer invariants that are not
    derivable from runtime bools alone.

    TRUTH AUDIT (2026-03-17): raw `hAgreeRaw` is CONFIRMED FALSE.
    The `translated` and `firstRule` branches have a falsity vector where
    `translateCall` fires on raw term while `intrinsicStepT` also reduces args.
    `noTranslateAtRoot` excludes the unsafe branches.

    Safe branches (covered by this structure):
      directIntrinsic, unchanged, partialBuiltin, partialArity -/
structure SupportedDeterministic (s : Session) (term : Pattern) : Prop where
  /-- All 7 runtime gate conditions hold. -/
  accepted : DeterministicAccepted s term
  /-- Semantic singleton invariant: intrinsicDirectPub returns ≤1 result. -/
  coreSingleton : CoreIntrinsicDirectSingleton s
  /-- No translator fires at the root level (excludes unsafe translated/firstRule branches). -/
  noTranslateAtRoot : Session.stepTranslateCall s term = []

/-- Project to the runtime accepted component. -/
theorem SupportedDeterministic.toAccepted {s : Session} {term : Pattern}
    (h : SupportedDeterministic s term) : DeterministicAccepted s term :=
  h.accepted

/-- Under `CoreIntrinsicDirectSingleton`, `intrinsicDirectPub` is either empty or singleton. -/
theorem intrinsicDirectPub_nil_or_singleton_of_core
    (s : Session) (hCore : CoreIntrinsicDirectSingleton s)
    (ctor : String) (argsV : List Pattern) :
    Session.intrinsicDirectPub s ctor argsV = [] ∨
    ∃ out, Session.intrinsicDirectPub s ctor argsV = [out] := by
  have hLen := hCore ctor argsV
  match h : Session.intrinsicDirectPub s ctor argsV with
  | [] => exact Or.inl rfl
  | [out] => exact Or.inr ⟨out, rfl⟩
  | _ :: _ :: _ => simp [h] at hLen

-- ─── Dispatch helpers ───────────────────────────────────────────────────────

/-- translateCall result for a given term (uses the public stepTranslateCall). -/
def translateCallFor (s : Session) (ctor : String) (argsV : List Pattern) : List Pattern :=
  Session.stepTranslateCall s (.apply ctor argsV)

-- ─── Dispatch classification ─────────────────────────────────────────────────
-- Classifies which branch of DeterministicEval.evalMemo fires for a given
-- `.apply ctor argsV` (where argsV are the already-evaluated args).
--
-- Exact mirror of the if-cascade in DeterministicEval.evalMemo lines 91-156.
-- Dispatch order:
--   1. translateCall non-empty          → translated
--   2. builtinPartialMinArity short     → partialBuiltin
--   3. intrinsicDirect non-empty        → directIntrinsic
--   4. firstRuleReduction? = some rhs   → firstRule
--   5. arity partial-application triple → partialArity
--   6. otherwise                        → unchanged

/-- Classification of the deterministic evaluator's root dispatch for
    `.apply ctor argsV`.  Mirrors `DeterministicEval.evalMemo`. -/
inductive DispatchClass (s : Session) (ctor : String) (argsV : List Pattern) where
  /-- `translateCall` returned a non-empty list. -/
  | translated
      (hTranslated : (translateCallFor s ctor argsV).isEmpty = false)
  /-- `builtinPartialMinArity?` says `some minArity` and args are too few. -/
  | partialBuiltin
      (hNoTranslate : translateCallFor s ctor argsV = [])
      (minArity : Nat)
      (hPartial : Session.builtinPartialMinArityPub ctor = some minArity)
      (hTooFew : argsV.length < minArity)
  /-- `intrinsicDirect` returned a non-empty list. -/
  | directIntrinsic
      (hNoTranslate : translateCallFor s ctor argsV = [])
      (hNotShort : ∀ m, Session.builtinPartialMinArityPub ctor = some m → argsV.length ≥ m)
      (hDirect : (Session.intrinsicDirectPub s ctor argsV).isEmpty = false)
  /-- `firstRuleReduction?` returned `some rhs`. -/
  | firstRule
      (hNoTranslate : translateCallFor s ctor argsV = [])
      (hNotShort : ∀ m, Session.builtinPartialMinArityPub ctor = some m → argsV.length ≥ m)
      (hNoDirect : Session.intrinsicDirectPub s ctor argsV = [])
      (rhs : Pattern)
      (hRule : Session.firstRuleReductionPub s (.apply ctor argsV) = some rhs)
  /-- Arities indicate partial application (hasLarger, no exact match, non-empty args). -/
  | partialArity
      (hNoTranslate : translateCallFor s ctor argsV = [])
      (hNotShort : ∀ m, Session.builtinPartialMinArityPub ctor = some m → argsV.length ≥ m)
      (hNoDirect : Session.intrinsicDirectPub s ctor argsV = [])
      (hNoRule : Session.firstRuleReductionPub s (.apply ctor argsV) = none)
      (hHasLarger : (Session.rewriteAritiesForHeadPub s ctor).any (· > argsV.length) = true)
      (hNoExact : (Session.rewriteAritiesForHeadPub s ctor).any (· == argsV.length) = false)
      (hNonEmpty : argsV.isEmpty = false)
  /-- Nothing fires; term is returned unchanged. -/
  | unchanged
      (hNoTranslate : translateCallFor s ctor argsV = [])
      (hNotShort : ∀ m, Session.builtinPartialMinArityPub ctor = some m → argsV.length ≥ m)
      (hNoDirect : Session.intrinsicDirectPub s ctor argsV = [])
      (hNoRule : Session.firstRuleReductionPub s (.apply ctor argsV) = none)
      (hNoPartialArity :
        ¬((Session.rewriteAritiesForHeadPub s ctor).any (· > argsV.length) = true ∧
          (Session.rewriteAritiesForHeadPub s ctor).any (· == argsV.length) = false ∧
          argsV.isEmpty = false))

/-- Every `.apply ctor argsV` term falls into exactly one dispatch class.
    Follows the exact if-cascade order from `DeterministicEval.evalMemo`. -/
def classifyDispatch (s : Session) (ctor : String) (argsV : List Pattern) :
    DispatchClass s ctor argsV := by
  -- 1. translateCall
  by_cases hT : (translateCallFor s ctor argsV).isEmpty = false
  · exact .translated hT
  · simp at hT
    -- 2. builtinPartialMinArity short-circuit
    match hP : Session.builtinPartialMinArityPub ctor with
    | some minArity =>
        by_cases hLt : argsV.length < minArity
        · exact .partialBuiltin hT minArity hP hLt
        · -- minArity satisfied → proceed to intrinsicDirect etc.
          have hNotShort : ∀ m, Session.builtinPartialMinArityPub ctor = some m → argsV.length ≥ m := by
            intro m hm; rw [hP] at hm; cases hm; exact Nat.le_of_not_lt hLt
          exact classifyDispatchTail s ctor argsV hT hNotShort
    | none =>
        have hNotShort : ∀ m, Session.builtinPartialMinArityPub ctor = some m → argsV.length ≥ m := by
          intro m hm; rw [hP] at hm; cases hm
        exact classifyDispatchTail s ctor argsV hT hNotShort
where
  /-- The tail of the dispatch cascade (after translateCall and builtinPartialMinArity). -/
  classifyDispatchTail (s : Session) (ctor : String) (argsV : List Pattern)
      (hT : translateCallFor s ctor argsV = [])
      (hNotShort : ∀ m, Session.builtinPartialMinArityPub ctor = some m → argsV.length ≥ m) :
      DispatchClass s ctor argsV := by
    -- 3. intrinsicDirect
    by_cases hD : (Session.intrinsicDirectPub s ctor argsV).isEmpty = false
    · exact .directIntrinsic hT hNotShort hD
    · simp at hD
      -- 4. firstRuleReduction?
      match hR : Session.firstRuleReductionPub s (.apply ctor argsV) with
      | some rhs => exact .firstRule hT hNotShort hD rhs hR
      | none =>
          -- 5/6. arity partial vs unchanged
          by_cases hPA :
              (Session.rewriteAritiesForHeadPub s ctor).any (· > argsV.length) = true ∧
              (Session.rewriteAritiesForHeadPub s ctor).any (· == argsV.length) = false ∧
              argsV.isEmpty = false
          · exact .partialArity hT hNotShort hD hR hPA.1 hPA.2.1 hPA.2.2
          · exact .unchanged hT hNotShort hD hR hPA

end Algorithms.MeTTa.Simple.Backend.DeterministicBridge
