-- Session.lean EXCERPT — R-2 sorry + exact goal dump
-- Lines 9068-9160 (the R-2 theorem and its proof)
-- ─── Generic foldl identity lemma (GPT-5.4 Pro Package A) ────────────────────

private theorem foldl_eq_init_of_forall_eq_self
    {α β : Type} (xs : List β) (f : α → β → α) (init : α)
    (h : ∀ x ∈ xs, ∀ acc, f acc x = acc) :
    xs.foldl f init = init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    have hx : f init x = init := h x (by simp) init
    simp [List.foldl, hx]
    apply ih
    intro y hy acc
    exact h y (by simp [hy]) acc

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
    (hNoPartialArity :
        match builtinPartialMinArity? ctor with
        | some minArity => argsV.length ≥ minArity
        | none => True)
    (hNoArityPartial :
        ¬((rewriteAritiesForHead s ctor).any (· > argsV.length) = true ∧
          !(rewriteAritiesForHead s ctor).any (· == argsV.length) ∧
          !argsV.isEmpty)) :
    referenceIntrinsicStatefulN (fuel + 1) s (.apply ctor argsV) = none := by
  simp only [intrinsicStatefulSpecialHeads, List.mem_append, List.mem_cons, List.not_mem_nil,
    not_or, not_false_eq_true] at hNotSpecial
  -- The first simp destructured hNotSpecial into nested conjunctions.
  -- Extract memberships for the three evalIntrinsic modules.
  -- After simp, hNotSpecial has shape: ((¬∈PC ∧ ¬∈SE) ∧ ¬∈SO) ∧ (¬= heads...)
  -- But the sub-list memberships are still in ¬∈ form, not destructured.
  -- hNotSpecial : ((¬∈PC ∧ ¬∈SE) ∧ ¬∈SO) ∧ (¬= direct heads...)
  obtain ⟨⟨⟨hPC_not, hSE_not⟩, hSO_not⟩, hMatchHeads⟩ := hNotSpecial
  -- Unfold one level
  unfold referenceIntrinsicStatefulN
  -- Layer 1: PeTTaCore.evalIntrinsic returns none
  simp only [Semantics.PeTTaCore.evalIntrinsic_none_of_nonSpecial _ s ctor argsV hPC_not]
  -- Layer 2: StateEffects.evalIntrinsic returns none
  simp only [Semantics.StateEffects.evalIntrinsic_none_of_nonSpecial _ s ctor argsV hSE_not]
  -- Layer 3: StreamOps.evalIntrinsic returns none
  simp only [Semantics.StreamOps.evalIntrinsic_none_of_nonSpecial _ s ctor argsV hSO_not]
  -- Now preIntrinsic = none. The ~50-head match + referenceIntrinsicApplyFallbackN remain.
  -- Use a single simp_all that handles everything:
  -- 1. The ~50-head match (hMatchHeads contradicts each specific head)
  -- 2. referenceIntrinsicApplyFallbackN / referenceIntrinsicApplyDispatchTailN unfolding
  -- 3. hNoCompat, hNoConstraint, hIrreducible, hNoPartialArity, hNoArityPartial all applied
  -- Give simp_all large heartbeat budget for the ~50 branches + foldl simplification.
  simp_all [referenceIntrinsicApplyFallbackN, referenceIntrinsicApplyDispatchTailN]
  -- STUCK: simp_all eliminated layers 1-4, ~50-head match, hNoCompat, hNoConstraint.
  -- Remaining: foldl arg-reduction (now as List.map..flatten) + arity partial check.
  -- simp_all transformed hIrreducible into inverted form.
  -- See GPT54_REQUEST_4.md for exact goal + hypotheses.
  sorry

/-- Unconditional session-WF preservation for the fuel-indexed evaluator. -/
theorem evalWithStateCoreN_preserves
    (fuel : Nat) (s : Session) (term : Pattern) (hs : WF s) :
    WF (evalWithStateCoreN fuel s term).1 :=
  compiledConsistent_of_referenceEvalWithStateCoreN fuel s term hs


-- foldl_eq_init_of_forall_eq_self (lines 9053-9067)
  Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsicSpecialHeads ++
  -- StreamOps.evalIntrinsic heads:
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

