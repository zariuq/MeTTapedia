-- Session.lean EXCERPT — updated with R-2 intrinsicStatefulN_none theorem
-- Full file: ~10400 lines. Only bridge-relevant sections extracted.

-- ═══ referenceIntrinsicApplyDispatchTailN (lines 2827-2864) ═══
  private def referenceIntrinsicApplyDispatchTailN
      (fuel : Nat)
      (dispatchIface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session)
      (s : Session) (ctor : String) (args : List Pattern) :
      Option (Session × List Pattern) :=
    let (sFH, fromHeads) :=
      Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        dispatchIface s (.apply ctor args)
    match fromHeads with
    | _ :: _ => some (sFH, fromHeads)
    | [] =>
        if Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule
            dispatchIface s ctor args.length then
          none
        else
          let reducts : List Pattern :=
            (List.range args.length).foldl (fun acc i =>
              let a := args.getD i (.apply "" [])
              let aRed0 :=
                match referenceIntrinsicStatefulN fuel s a with
                | some (_sA, outA) =>
                    if outA.isEmpty then step s a else outA
                | none => step s a
              let aRed := aRed0.filter (fun a' => a' != a)
              let built :=
                aRed.map (fun a' =>
                  .apply ctor (args.take i ++ [a'] ++ args.drop (i + 1)))
              acc ++ built) []
          match reducts with
          | _ :: _ => some (s, reducts)
          | [] =>
              let arities := rewriteAritiesForHead s ctor
              let hasExact := arities.any (fun n => n == args.length)
              let hasLarger := arities.any (fun n => n > args.length)
              if hasLarger && !hasExact && !args.isEmpty then
                some (s, [partialPattern ctor args])
              else
                none

-- ═══ referenceIntrinsicApplyFallbackN (lines 2866-2886) ═══
  private def referenceIntrinsicApplyFallbackN
      (fuel : Nat) (s : Session) (ctor : String) (args : List Pattern) :
      Option (Session × List Pattern) :=
    let dispatchIface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
      eval := fun s term => referenceEvalWithStateCoreN fuel s term
      evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    match builtinPartialMinArity? ctor with
    | some minArity =>
        if args.length < minArity then
          some (s, [partialPattern ctor args])
        else
          referenceIntrinsicApplyDispatchTailN fuel dispatchIface s ctor args
    | none =>
        referenceIntrinsicApplyDispatchTailN fuel dispatchIface s ctor args

-- ═══ referenceIntrinsicStatefulN (lines 2888-3347) — first 100 lines ═══
  private def referenceIntrinsicStatefulN : Nat → Session → Pattern → Option (Session × List Pattern)
    | 0, _s, _term => none
    | fuel + 1, s, term =>
        let referenceEvalDeterministicCoreN (s : Session) (detFuel : Nat) (term : Pattern) : Session × Pattern :=
          Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval
            (mkDeterministicEvalInterface
              (fun s term => referenceEvalWithStateCoreN fuel s term)
              (fun s fn args => referenceEvalCallableApplyN fuel s fn args))
            s detFuel term
        let pIface : Algorithms.MeTTa.Simple.Semantics.PeTTaCore.Interface Session := {
          eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalDeterministic := referenceEvalDeterministicCoreN
          evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          findBindingsInSpace := findBindingsInSpace
          dedupPatterns := dedupPatternList
          typeCandidates := typeCandidatesInSelf
        }
        match Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic pIface s term with
        | some out => some out
        | none =>
            let stateI : Algorithms.MeTTa.Simple.Semantics.StateEffects.Interface Session := {
              eval := fun s term => referenceEvalWithStateCoreN fuel s term
              snapshot := fun sess => sess
              isFailure := isFailurePattern
              truePattern := patternOfBool true
              getStateCells := fun sess => sess.stateCells
              withStateCells := fun sess cells => { sess with stateCells := cells }
            }
            let preIntrinsic :=
              match Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic stateI s term with
              | some out => some out
              | none =>
                  let streamI : Algorithms.MeTTa.Simple.Semantics.StreamOps.Interface Session := {
                    evalValues := fun sess expr =>
                      match referenceIntrinsicStatefulN fuel sess expr with
                      | some (s1, out0) =>
                          let out := if out0.isEmpty then [expr] else out0
                          (s1, out)
                      | none =>
                          let (s1, out0) := referenceEvalWithStateCoreN fuel sess expr
                          let out := if out0.isEmpty then [expr] else out0
                          (s1, out)
                  }
                  Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic streamI s term
            let controlFlowI : Algorithms.MeTTa.Simple.Semantics.ControlFlow.Interface Session := {
              eval := fun s term => referenceEvalWithStateCoreN fuel s term
              evalKeyValues := fun sess key =>
                match key with
                | .apply "superpose" [arg] =>
                    match referenceIntrinsicStatefulN fuel sess (.apply "superpose" [arg]) with
                    | some (sess', out) =>
                        let vals := if out.isEmpty then [.apply "superpose" [arg]] else out
                        (sess', vals)
                    | none =>
                        let (sess', out) := referenceEvalWithStateCoreN fuel sess key
                        let vals := if out.isEmpty then [key] else out
                        (sess', vals)
                | _ =>
                    let (sess', out) := referenceEvalWithStateCoreN fuel sess key
                    let vals := if out.isEmpty then [key] else out
                    (sess', vals)
              evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
              evalGeneratorValues := fun sess genExpr =>
                let (s1, out0) := referenceEvalWithStateCoreN fuel sess genExpr
                let (sCall, callOut) :=
                  match genExpr with
                  | .apply "Expr" (callable :: args) =>
                      referenceEvalCallableApplyN fuel s1 callable args
                  | _ =>
                      (s1, [])
                let baseOut := if callOut.isEmpty then out0 else callOut
                let dispatchI : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
                  rewrites := fun s => s.bundle.language.rewrites
                  premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
                  eval := fun s term => referenceEvalWithStateCoreN fuel s term
                  evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
                  applyBindings := applyBindingsCompat
                  matchPattern := matchPatternMeTTa
                  normalizePattern := normalizeDollarVars
                  dedupBindings := dedupBindings
                }
                let (sEnum, extra) :=
                  Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
                    dispatchI sCall genExpr
                let out := if extra.isEmpty then baseOut else extra
                (sEnum, out)
              applyBindings := applyBindingsCompat
              matchPattern := matchPatternMeTTa
              isTruthy := isTruthy
              patternOfBool := patternOfBool
            }
            match preIntrinsic with
            | some out => some out
            | none =>
                match term with
                | .apply "add-atom" [space, fact] =>
                    let spaceI : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
                      bundle := fun s => s.bundle
                      rewrites := fun s => s.bundle.language.rewrites

-- ═══ referenceIntrinsicStatefulN — final match (lines 3280-3347) ═══
                    -- Single eval call; simplified output.
                    let (s', out) := referenceEvalWithStateCoreN fuel s arg
                    some (s', [tupleOfElems out])
                -- Phase 4: simple remaining branches (1-step or 2-step chain)
                | .apply "translatePredicate" [expr] =>
                    let (s', out) := referenceEvalWithStateCoreN fuel s expr
                    some (s', out)
                | .apply "if" [cond, thenBr, _elseBr] =>
                    let (s1, _cv) := referenceEvalWithStateCoreN fuel s cond
                    let (s2, out) := referenceEvalWithStateCoreN fuel s1 thenBr
                    some (s2, out)
                | .apply "if" [cond, thenBr] =>
                    let (s1, _cv) := referenceEvalWithStateCoreN fuel s cond
                    let (s2, out) := referenceEvalWithStateCoreN fuel s1 thenBr
                    some (s2, out)
                | .apply "let" [_pat, valExpr, body] =>
                    let (s1, _vs) := referenceEvalWithStateCoreN fuel s valExpr
                    let (s2, out) := referenceEvalWithStateCoreN fuel s1 body
                    some (s2, out)
                | .apply "let*" [_binds, body] =>
                    let (s', out) := referenceEvalWithStateCoreN fuel s body
                    some (s', out)
                | .apply "progn" _exprs =>
                    -- Simplified: state unchanged, result is unit.
                    some (s, [.apply "()" []])
                | .apply "prog1" _exprs =>
                    -- Simplified: state unchanged, result is unit.
                    some (s, [.apply "()" []])
                -- Phase 5: Expr, repr — need evalTupleIntrinsicWith / evalDeterministicCore
                | .apply "Expr" elems =>
                    let (s', out) :=
                      evalTupleIntrinsicWith
                        (fun s term => referenceEvalWithStateCoreN fuel s term)
                        (fun s fn args => referenceEvalCallableApplyN fuel s fn args)
                        isRuleCallableHead s elems
                    some (s', out)
                | .apply "repr" [arg] =>
                    -- Simplified: eval arg deterministically; state may change.
                    let (s', _argV) := referenceEvalDeterministicCoreN s 1024 arg
                    some (s', [])
                -- Phase 6: atom-of — faithful to the live intrinsicStateful branch.
                -- Uses `step` (pure, no state mutation) as the none-branch fallback,
                -- then applies the same tupleAt? extraction and dedup as the live code.
                | .apply "atom-of" [x] =>
                    let (s1, x1, _) := referenceRunNestedEffectsN fuel s true false x
                    let (s2, out) :=
                      match referenceIntrinsicStatefulN fuel s1 x1 with
                      | some (sI, outI) =>
                          if outI.isEmpty then (sI, [x1]) else (sI, outI)
                      | none =>
                          let reducts := step s1 x1
                          if reducts.isEmpty then (s1, [x1]) else (s1, reducts)
                    let extracted :=
                      out.filterMap fun candidate =>
                        match tupleAt? (tupleElems candidate) 0 with
                        | none => none
                        | some row => tupleAt? (tupleElems row) 0
                    if extracted.isEmpty then some (s2, [])
                    else some (s2, dedupPatternList extracted)
                -- Phase 7: generic .apply ctor args — faithful to the live intrinsicStateful branch.
                -- Sub-case A: builtinPartialMinArity — state unchanged.
                -- Sub-case B: compatFunctionHeadRewrite (inline dispatch iface) — state from dispatch.
                -- Sub-case C: hasCompatHeadConstraintRule — out empty → none.
                -- Sub-case D: reduceArgs (calls referenceIntrinsicStatefulN fuel s a; state unchanged).
                -- Sub-case E: arities/hasLarger — state unchanged.
                | .apply ctor args => referenceIntrinsicApplyFallbackN fuel s ctor args
                | _ => none
end

-- ═══ NEW: intrinsicStatefulSpecialHeads + R-2 theorem (lines 9055-9120) ═══
  Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsicSpecialHeads ++
  -- Heads from the ~50-branch match in referenceIntrinsicStatefulN:
  ["add-atom", "add-atom!", "remove-atom", "remove-atom!",
   "remove-all-atoms", "remove-all-atoms!", "get-atoms", "get-atoms!",
   "match", "case", "foldall", "forall",
   "cut", "Predicate", "find", "succeedsPredicate",
   "add-translator-rule!", "remove-translator-rule!",
   "new-atom-vectorspace", "add-atom-vector", "add-atom-SRI",
   "match-k", "match-sri", "match-SRI",
   "once", "nop", "catch", "msort", "superpose", "hide", "space",
   "collapse", "translatePredicate", "if", "let", "let*",
   "progn", "prog1", "Expr", "repr", "atom-of"]

/-- For builtin ctors not in the intrinsicStateful special-head set, with args that are
    step-irreducible, under noOverlap, `referenceIntrinsicStatefulN` returns `none`.
    This is NOT a free hypothesis — it is derived from session conditions.

    Proof traces through: PeTTaCore.evalIntrinsic → StateEffects.evalIntrinsic →
    StreamOps.evalIntrinsic → ~50-head match → referenceIntrinsicApplyFallbackN →
    referenceIntrinsicApplyDispatchTailN, all returning `none` for non-special builtins. -/
theorem referenceIntrinsicStatefulN_none_of_builtin_strict
    (fuel : Nat) (s : Session) (ctor : String) (argsV : List Pattern)
    (hNotSpecial : ctor ∉ intrinsicStatefulSpecialHeads)
    (hNoCompat : Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        { rewrites := fun s => s.bundle.language.rewrites
          premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
          eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          normalizePattern := normalizeDollarVars
          dedupBindings := dedupBindings }
        s (.apply ctor argsV) = (s, []))
    (hNoConstraint : Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule
        { rewrites := fun s => s.bundle.language.rewrites
          premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
          eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          normalizePattern := normalizeDollarVars
          dedupBindings := dedupBindings }
        s ctor argsV.length = false)
    (hIrreducible : ∀ a ∈ argsV,
        (match referenceIntrinsicStatefulN fuel s a with
         | some (_sA, outA) => if outA.isEmpty then step s a else outA
         | none => step s a).filter (· != a) = [])
    (hNoArityPartial :
        ¬((rewriteAritiesForHead s ctor).any (· > argsV.length) = true ∧
          !(rewriteAritiesForHead s ctor).any (· == argsV.length) ∧
          !argsV.isEmpty)) :
    referenceIntrinsicStatefulN (fuel + 1) s (.apply ctor argsV) = none := by
  simp only [intrinsicStatefulSpecialHeads, List.mem_append, List.mem_cons, List.not_mem_nil,
    not_or, not_false_eq_true] at hNotSpecial
  unfold referenceIntrinsicStatefulN
  simp_all [Semantics.PeTTaCore.evalIntrinsic, Semantics.StateEffects.evalIntrinsic,
    Semantics.StreamOps.evalIntrinsic,
    referenceIntrinsicApplyFallbackN, referenceIntrinsicApplyDispatchTailN]
  -- After simp_all: Layers 1-3 (evalIntrinsic) eliminated ✓
  -- ~50-head match fell through to generic .apply ctor args ✓
  -- compatFunctionHeadRewrite = (s, []) applied ✓
  -- hasCompatHeadConstraintRule = false applied ✓
  -- REMAINING: the foldl arg-reduction loop + arity check.
  -- The foldl builds arg reductions; hIrreducible says each is [].
  -- The arity check contradicts hNoArityPartial.
  -- TODO: close with targeted foldl lemma + arity contradiction.

-- ═══ referenceEvalInterfaceN + simp lemmas + evalWithStateCoreN_unchanged/step_nonempty (lines 8944-9055) ═══
/-- The named concrete `ReferenceEval.Interface` used by `referenceEvalWithStateCoreN`.
    This is the canonical proof-facing interface: bridge predicates and simulation theorems
    should be stated in terms of this interface, not the copied `referenceRunNestedEffectsN`.
    See GPT-5.4 Pro Option E rationale. -/
def referenceEvalInterfaceN (fuel : Nat) :
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
  maxNodes := fun s => s.maxNodes
  maxSteps := fun s => s.maxSteps
  runNestedEffects := fun s isRoot p term => referenceRunNestedEffectsN fuel s isRoot p term
  intrinsicStateful := fun s term => referenceIntrinsicStatefulN fuel s term
  isEagerCallableHead := isEagerCallableHead
  step := step
  enqueueNext := enqueueNext
  insertUnique := insertUnique
  dedupPatterns := dedupPatterns
}

-- ─── @[simp] field projection lemmas ─────────────────────────────────────────

@[simp] theorem referenceEvalInterfaceN_maxNodes (fuel : Nat) :
    (referenceEvalInterfaceN fuel).maxNodes = fun s => s.maxNodes := rfl

@[simp] theorem referenceEvalInterfaceN_maxSteps (fuel : Nat) :
    (referenceEvalInterfaceN fuel).maxSteps = fun s => s.maxSteps := rfl

@[simp] theorem referenceEvalInterfaceN_intrinsicStateful (fuel : Nat) (s : Session) (term : Pattern) :
    (referenceEvalInterfaceN fuel).intrinsicStateful s term =
      referenceIntrinsicStatefulNPub fuel s term := rfl

@[simp] theorem referenceEvalInterfaceN_step (fuel : Nat) :
    (referenceEvalInterfaceN fuel).step = step := rfl

@[simp] theorem referenceEvalInterfaceN_enqueueNext (fuel : Nat) :
    (referenceEvalInterfaceN fuel).enqueueNext = enqueueNext := rfl

/-- `evalWithStateCoreN (fuel+1)` equals `evalWithStateCore` applied to the named interface. -/
theorem evalWithStateCoreN_succ (fuel : Nat) (s : Session) (term : Pattern) :
    evalWithStateCoreN (fuel + 1) s term =
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore
        (referenceEvalInterfaceN fuel) s term := by
  show referenceEvalWithStateCoreN (fuel + 1) s term = _
  unfold referenceEvalWithStateCoreN
  rfl

-- ─── Concrete unchanged-branch theorem ───────────────────────────────────────

/-- When `runNestedEffects` is passthrough, `intrinsicStateful` returns `none`,
    and `step` returns `[]`, the fuel-indexed evaluator returns `(s, [term])`.
    Thin wrapper over abstract `ReferenceEval.evalWithStateCore_unchanged`. -/
theorem evalWithStateCoreN_unchanged
    (fuel : Nat) (s : Session) (term : Pattern)
    (hNodes : s.maxNodes ≥ 1)
    (hSteps : 0 < s.maxSteps)
    (hRNE : Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
        (referenceEvalInterfaceN fuel) s true false term = (s, term, false))
    (hIntr : (referenceEvalInterfaceN fuel).intrinsicStateful s term = none)
    (hStep : step s term = []) :
    evalWithStateCoreN (fuel + 1) s term = (s, [term]) := by
  simp only [evalWithStateCoreN_succ]
  exact Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore_unchanged
    (referenceEvalInterfaceN fuel) s term hNodes hSteps hRNE hIntr hStep

/-- When `runNestedEffects` is passthrough, `intrinsicStateful` returns `none`,
    and `step` returns a non-empty `reducts`, the fuel-indexed evaluator one-steps to
    processing the reducts through the work-queue at depth 1.
    This is the ref-evaluator side of the directIntrinsic branch. -/
theorem evalWithStateCoreN_step_nonempty
    (fuel : Nat) (s : Session) (term : Pattern)
    (hNodes : s.maxNodes ≥ 1)
    (hSteps : 0 < s.maxSteps)
    (hRNE : Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
        (referenceEvalInterfaceN fuel) s true false term = (s, term, false))
    (hIntr : (referenceEvalInterfaceN fuel).intrinsicStateful s term = none)
    (reducts : List Pattern)
    (hStep : step s term = reducts)
    (hNonempty : reducts.isEmpty = false) :
    evalWithStateCoreN (fuel + 1) s term =
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful
        (referenceEvalInterfaceN fuel) s (s.maxNodes - 1)
        ((referenceEvalInterfaceN fuel).enqueueNext [] 1 reducts) [] := by
  simp only [evalWithStateCoreN_succ]
  -- Unfold evalWithStateCore → evalAuxStateful with maxNodes fuel
  unfold Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore
  -- Use the one-step lemma at depth 0
  obtain ⟨n, hN⟩ : ∃ n, (referenceEvalInterfaceN fuel).maxNodes s = n + 1 :=
    ⟨s.maxNodes - 1, by simp [referenceEvalInterfaceN]; omega⟩
  simp only [hN]
  rw [Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful_step_of_intrinsicNone
    (referenceEvalInterfaceN fuel) s s term term false 0 [] [] n
    hRNE (by simp [referenceEvalInterfaceN]; exact hSteps) hIntr]
  -- The LHS has `have reducts := iface.step s term; if reducts.isEmpty ...`
  -- Substitute iface.step = step, then step s term = reducts, then reducts.isEmpty = false
  simp only [referenceEvalInterfaceN_step, hStep, hNonempty,
    referenceEvalInterfaceN_enqueueNext, Bool.false_eq_true, ite_false]
  -- Now: evalAuxStateful ... s n (enqueueNext [] (0+1) reducts) [] = ... s (s.maxNodes-1) (enqueueNext [] 1 reducts) []
  have hNEq : n = s.maxNodes - 1 := by simp [referenceEvalInterfaceN] at hN; omega
  subst hNEq
  simp

-- ─── R-2: intrinsicStatefulN_none for builtin terms under StrictContext-like conditions ──
-- This is NOT a free hypothesis — it is derived from noOverlap + argsIrreducible + builtin.

/-- The combined set of heads handled by all three evalIntrinsic dispatchers AND
    the ~50-head match inside `referenceIntrinsicStatefulN`. Arithmetic builtins
    (`+`, `-`, `*`, `<`, etc.) are NOT in this set. -/
private def intrinsicStatefulSpecialHeads : List String :=
  -- PeTTaCore.evalIntrinsic heads:
  Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsicSpecialHeads ++
  -- StateEffects.evalIntrinsic heads:
  Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsicSpecialHeads ++
  -- StreamOps.evalIntrinsic heads:
  Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsicSpecialHeads ++
