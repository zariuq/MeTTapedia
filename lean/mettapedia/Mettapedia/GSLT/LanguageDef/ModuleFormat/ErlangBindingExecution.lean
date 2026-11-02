import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangProgramCompilation
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement

/-! General argument binding and lexical lookup paths through the actual
authored Erlang structural rules. These laws do not execute a reference
interpreter to supply target steps. Complete instruction/service agreement
remains a separate qualification obligation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation.BindingExecution
open Mettapedia.OSLF.MeTTaIL Syntax Match ContextualStep
open ReflectiveCanonical ReflectiveSubstitution
open Mettapedia.Languages

private theorem root_step (base : BasePremiseEvaluator) (index : Nat)
    (bound : index < baseLanguage.rewrites.length) (bindings : Bindings) (source target : Pattern)
    (noPremises : baseLanguage.rewrites[index].premises = [])
    (aligned : ruleDepthAligned baseLanguage.rewrites[index] = true)
    (matched : bindings ∈ matchPattern baseLanguage.rewrites[index].left source)
    (applied : applyBindings bindings baseLanguage.rewrites[index].right = target) :
    ContextualStep.Step base baseLanguage source target := by
  refine ⟨1, StepAt.rule (rule := baseLanguage.rewrites[index])
    (initialBindings := bindings) (finalBindings := bindings) (List.getElem_mem _) ?_ ?_ ?_⟩
  · simpa only [matchPatternForRule_eq_syntactic] using matched
  · rw [noPremises]
    exact .nil bindings
  · rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings _ _ aligned]
    exact applied

theorem call_more (base : BasePremiseEvaluator) (head tail body original rest function scope remaining : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErBindCall" [(node "ErSucc" [remaining]), (node "ErValuesCons" [head, tail]), scope, body, function, original, rest])
      (node "ErBindCall" [remaining, tail, (node "ErEnvironmentCons" [head, scope]), body, function, original, rest]) := by
  let bs : Bindings := [("head", head), ("tail", tail), ("body", body), ("original", original), ("rest", rest), ("function", function), ("environment", scope), ("count", remaining)]
  refine root_step base 25 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErBindCall" [(.apply "ErSucc" [.fvar "count"]), (.apply "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "environment", .fvar "body", .fvar "function", .fvar "original", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErBindCall" [.fvar "count", .fvar "tail", (.apply "ErEnvironmentCons" [.fvar "head", .fvar "environment"]), .fvar "body", .fvar "function", .fvar "original", .fvar "rest"]) = _
    simp [bs, node, applyBindings]

theorem call_done (base : BasePremiseEvaluator) (body original rest function scope : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErBindCall" [(node "ErZero"), (node "ErValuesNil"), scope, body, function, original, rest])
      (node "ErEvaluate" [body, scope, rest]) := by
  let bs : Bindings := [("body", body), ("original", original), ("rest", rest), ("function", function), ("environment", scope)]
  refine root_step base 26 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErBindCall" [(.apply "ErZero" []), (.apply "ErValuesNil" []), .fvar "environment", .fvar "body", .fvar "function", .fvar "original", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErEvaluate" [.fvar "body", .fvar "environment", .fvar "rest"]) = _
    simp [bs, node, applyBindings]

theorem let_more (base : BasePremiseEvaluator) (head tail body original rest expected scope remaining : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErBindLet" [(node "ErSucc" [remaining]), (node "ErValuesCons" [head, tail]), scope, body, expected, original, rest])
      (node "ErBindLet" [remaining, tail, (node "ErEnvironmentCons" [head, scope]), body, expected, original, rest]) := by
  let bs : Bindings := [("head", head), ("tail", tail), ("body", body), ("original", original), ("rest", rest), ("expected", expected), ("environment", scope), ("count", remaining)]
  refine root_step base 29 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErBindLet" [(.apply "ErSucc" [.fvar "count"]), (.apply "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "environment", .fvar "body", .fvar "expected", .fvar "original", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErBindLet" [.fvar "count", .fvar "tail", (.apply "ErEnvironmentCons" [.fvar "head", .fvar "environment"]), .fvar "body", .fvar "expected", .fvar "original", .fvar "rest"]) = _
    simp [bs, node, applyBindings]

theorem let_done (base : BasePremiseEvaluator) (body original rest expected scope : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErBindLet" [(node "ErZero"), (node "ErValuesNil"), scope, body, expected, original, rest])
      (node "ErEvaluate" [body, scope, rest]) := by
  let bs : Bindings := [("body", body), ("original", original), ("rest", rest), ("expected", expected), ("environment", scope)]
  refine root_step base 30 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErBindLet" [(.apply "ErZero" []), (.apply "ErValuesNil" []), .fvar "environment", .fvar "body", .fvar "expected", .fvar "original", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErEvaluate" [.fvar "body", .fvar "environment", .fvar "rest"]) = _
    simp [bs, node, applyBindings]

theorem lookup_zero (base : BasePremiseEvaluator) (head tail full rest original : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErLookup" [(node "ErZero"), (node "ErEnvironmentCons" [head, tail]), original, full, rest])
      (node "ErReturn" [(node "ErValuesCons" [head, (node "ErValuesNil")]), rest]) := by
  let bs : Bindings := [("head", head), ("tail", tail), ("full", full), ("rest", rest), ("original", original)]
  refine root_step base 33 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErLookup" [(.apply "ErZero" []), (.apply "ErEnvironmentCons" [.fvar "head", .fvar "tail"]), .fvar "original", .fvar "full", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErReturn" [(.apply "ErValuesCons" [.fvar "head", (.apply "ErValuesNil" [])]), .fvar "rest"]) = _
    simp [bs, node, applyBindings]

theorem lookup_more (base : BasePremiseEvaluator) (head tail full rest original remaining : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErLookup" [(node "ErSucc" [remaining]), (node "ErEnvironmentCons" [head, tail]), original, full, rest])
      (node "ErLookup" [remaining, tail, original, full, rest]) := by
  let bs : Bindings := [("head", head), ("tail", tail), ("full", full), ("rest", rest), ("original", original), ("count", remaining)]
  refine root_step base 34 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErLookup" [(.apply "ErSucc" [.fvar "count"]), (.apply "ErEnvironmentCons" [.fvar "head", .fvar "tail"]), .fvar "original", .fvar "full", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErLookup" [.fvar "count", .fvar "tail", .fvar "original", .fvar "full", .fvar "rest"]) = _
    simp [bs, node, applyBindings]

theorem lookup_empty (base : BasePremiseEvaluator) (full rest original remaining : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErLookup" [remaining, (node "ErEnvironmentNil"), original, full, rest])
      (node "ErInvalid" [(node "ErUnboundIndex" [original])]) := by
  let bs : Bindings := [("full", full), ("rest", rest), ("original", original), ("count", remaining)]
  refine root_step base 35 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErLookup" [.fvar "count", (.apply "ErEnvironmentNil" []), .fvar "original", .fvar "full", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErInvalid" [(.apply "ErUnboundIndex" [.fvar "original"])]) = _
    simp [bs, node, applyBindings]

theorem call_short (base : BasePremiseEvaluator) (body original rest function scope remaining : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErBindCall" [(node "ErSucc" [remaining]), (node "ErValuesNil"), scope, body, function, original, rest])
      (node "ErRaise" [(node "ErBadarity" [function, original]), rest]) := by
  let bs : Bindings := [("body", body), ("original", original), ("rest", rest), ("function", function), ("environment", scope), ("count", remaining)]
  refine root_step base 27 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErBindCall" [(.apply "ErSucc" [.fvar "count"]), (.apply "ErValuesNil" []), .fvar "environment", .fvar "body", .fvar "function", .fvar "original", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErRaise" [(.apply "ErBadarity" [.fvar "function", .fvar "original"]), .fvar "rest"]) = _
    simp [bs, node, applyBindings]

theorem call_long (base : BasePremiseEvaluator) (body original rest function scope head tail : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErBindCall" [(node "ErZero"), (node "ErValuesCons" [head, tail]), scope, body, function, original, rest])
      (node "ErRaise" [(node "ErBadarity" [function, original]), rest]) := by
  let bs : Bindings := [("head", head), ("tail", tail), ("body", body), ("original", original), ("rest", rest), ("function", function), ("environment", scope)]
  refine root_step base 28 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErBindCall" [(.apply "ErZero" []), (.apply "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "environment", .fvar "body", .fvar "function", .fvar "original", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErRaise" [(.apply "ErBadarity" [.fvar "function", .fvar "original"]), .fvar "rest"]) = _
    simp [bs, node, applyBindings]

theorem let_short (base : BasePremiseEvaluator) (body original rest expected scope remaining : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErBindLet" [(node "ErSucc" [remaining]), (node "ErValuesNil"), scope, body, expected, original, rest])
      (node "ErInvalid" [(node "ErReturnArity" [expected, original])]) := by
  let bs : Bindings := [("body", body), ("original", original), ("rest", rest), ("expected", expected), ("environment", scope), ("count", remaining)]
  refine root_step base 31 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErBindLet" [(.apply "ErSucc" [.fvar "count"]), (.apply "ErValuesNil" []), .fvar "environment", .fvar "body", .fvar "expected", .fvar "original", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErInvalid" [(.apply "ErReturnArity" [.fvar "expected", .fvar "original"])]) = _
    simp [bs, node, applyBindings]

theorem let_long (base : BasePremiseEvaluator) (body original rest expected scope head tail : Pattern) :
    ContextualStep.Step base baseLanguage
      (node "ErBindLet" [(node "ErZero"), (node "ErValuesCons" [head, tail]), scope, body, expected, original, rest])
      (node "ErInvalid" [(node "ErReturnArity" [expected, original])]) := by
  let bs : Bindings := [("head", head), ("tail", tail), ("body", body), ("original", original), ("rest", rest), ("expected", expected), ("environment", scope)]
  refine root_step base 32 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErBindLet" [(.apply "ErZero" []), (.apply "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "environment", .fvar "body", .fvar "expected", .fvar "original", .fvar "rest"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErInvalid" [(.apply "ErReturnArity" [.fvar "expected", .fvar "original"])]) = _
    simp [bs, node, applyBindings]

abbrev Path (base : BasePremiseEvaluator) :=
  Relation.ReflTransGen (ContextualStep.Step base baseLanguage)

/-- Each argument becomes one lexical slot; earlier arguments end up deeper. -/
theorem call_path (base : BasePremiseEvaluator) (arguments : List Pattern)
    (scope body function original rest : Pattern) :
    Path base (node "ErBindCall"
      [count arguments.length, values arguments, scope, body, function, original, rest])
      (node "ErEvaluate" [body, extend arguments scope, rest]) := by
  induction arguments generalizing scope with
  | nil => exact .single (call_done base body original rest function scope)
  | cons head tail ih =>
      have path := (Relation.ReflTransGen.single
        (call_more base head (values tail) body original rest function scope (count tail.length))).trans
        (ih (node "ErEnvironmentCons" [head, scope]))
      simpa only [List.length_cons, count, values, linked, List.foldr_cons,
        extend, List.foldl_cons] using path

theorem let_path (base : BasePremiseEvaluator) (arguments : List Pattern)
    (scope body expected original rest : Pattern) :
    Path base (node "ErBindLet"
      [count arguments.length, values arguments, scope, body, expected, original, rest])
      (node "ErEvaluate" [body, extend arguments scope, rest]) := by
  induction arguments generalizing scope with
  | nil => exact .single (let_done base body original rest expected scope)
  | cons head tail ih =>
      have path := (Relation.ReflTransGen.single
        (let_more base head (values tail) body original rest expected scope (count tail.length))).trans
        (ih (node "ErEnvironmentCons" [head, scope]))
      simpa only [List.length_cons, count, values, linked, List.foldr_cons,
        extend, List.foldl_cons] using path

/-- Calls either bind exactly the declared arity or retain the original
function and argument pack in the arity fault. -/
theorem call_total_path (base : BasePremiseEvaluator) (arity : Nat) (arguments : List Pattern)
    (scope body function original rest : Pattern) :
    Path base (node "ErBindCall" [count arity, values arguments, scope, body, function, original, rest])
      (if arguments.length = arity then node "ErEvaluate" [body, extend arguments scope, rest]
       else node "ErRaise" [node "ErBadarity" [function, original], rest]) := by
  induction arity generalizing arguments scope with
  | zero =>
      cases arguments with
      | nil => exact .single (call_done base body original rest function scope)
      | cons head tail =>
          simpa only [List.length_cons, Nat.add_one_ne_zero, ↓reduceIte, count, values,
            linked, List.foldr_cons] using
            Relation.ReflTransGen.single (call_long base body original rest function scope head (values tail))
  | succ arity ih =>
      cases arguments with
      | nil =>
          simpa only [List.length_nil, Nat.zero_ne_add_one, ↓reduceIte, count, values,
            linked, List.foldr_nil] using
            Relation.ReflTransGen.single (call_short base body original rest function scope (count arity))
      | cons head tail =>
          have path := (Relation.ReflTransGen.single
            (call_more base head (values tail) body original rest function scope (count arity))).trans
            (ih tail (node "ErEnvironmentCons" [head, scope]))
          simpa only [List.length_cons, Nat.succ.injEq, count, values, linked, List.foldr_cons,
            extend, List.foldl_cons] using path

theorem let_total_path (base : BasePremiseEvaluator) (arity : Nat) (arguments : List Pattern)
    (scope body expected original rest : Pattern) :
    Path base (node "ErBindLet" [count arity, values arguments, scope, body, expected, original, rest])
      (if arguments.length = arity then node "ErEvaluate" [body, extend arguments scope, rest]
       else node "ErInvalid" [node "ErReturnArity" [expected, original]]) := by
  induction arity generalizing arguments scope with
  | zero =>
      cases arguments with
      | nil => exact .single (let_done base body original rest expected scope)
      | cons head tail =>
          simpa only [List.length_cons, Nat.add_one_ne_zero, ↓reduceIte, count, values,
            linked, List.foldr_cons] using
            Relation.ReflTransGen.single (let_long base body original rest expected scope head (values tail))
  | succ arity ih =>
      cases arguments with
      | nil =>
          simpa only [List.length_nil, Nat.zero_ne_add_one, ↓reduceIte, count, values,
            linked, List.foldr_nil] using
            Relation.ReflTransGen.single (let_short base body original rest expected scope (count arity))
      | cons head tail =>
          have path := (Relation.ReflTransGen.single
            (let_more base head (values tail) body original rest expected scope (count arity))).trans
            (ih tail (node "ErEnvironmentCons" [head, scope]))
          simpa only [List.length_cons, Nat.succ.injEq, count, values, linked, List.foldr_cons,
            extend, List.foldl_cons] using path

/-- The compact source environment and emitted binding order agree. -/
theorem environment_extend (captured arguments : List Erlang.Value) :
    environment (Erlang.extend captured arguments) =
      extend (arguments.map value) (environment captured) := by
  induction arguments generalizing captured with
  | nil => rfl
  | cons head tail ih =>
      simpa only [Erlang.extend, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.map_cons, extend, List.foldl_cons, environment] using
        ih (head :: captured)

theorem valueList_eq_values (arguments : List Erlang.Value) :
    valueList arguments = values (arguments.map value) := by
  induction arguments with
  | nil => rfl
  | cons head tail ih =>
      simp only [valueList, List.map_cons, values, linked, List.foldr_cons] at *
      rw [ih]

/-- Source call binding is realized by the authored GSLT, for every arity. -/
theorem source_call_path (base : BasePremiseEvaluator) (captured arguments : List Erlang.Value)
    (body function original rest : Pattern) :
    Path base (node "ErBindCall"
      [count arguments.length, valueList arguments, environment captured, body, function, original, rest])
      (node "ErEvaluate" [body, environment (Erlang.extend captured arguments), rest]) := by
  simpa only [environment_extend, valueList_eq_values, List.length_map] using
    call_path base (arguments.map value) (environment captured) body function original rest

/-- Looking up a present slot preserves the original diagnostic context. -/
theorem lookup_path (base : BasePremiseEvaluator) (scope : List Erlang.Value)
    (index : Nat) (datum : Erlang.Value) (found : scope[index]? = some datum)
    (original full rest : Pattern) :
    Path base (node "ErLookup" [count index, environment scope, original, full, rest])
      (node "ErReturn" [valueList [datum], rest]) := by
  induction scope generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          have same : head = datum := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using found
          subst datum
          exact .single (lookup_zero base (value head) (environment tail) full rest original)
      | succ index =>
          have tailFound : tail[index]? = some datum := by simpa only [List.getElem?_cons_succ] using found
          exact (Relation.ReflTransGen.single
            (lookup_more base (value head) (environment tail) full rest original (count index))).trans
            (ih index tailFound)

/-- Missing slots become the declared diagnostic, never a fabricated value. -/
theorem lookup_missing_path (base : BasePremiseEvaluator) (scope : List Erlang.Value)
    (index : Nat) (missing : scope[index]? = none) (original full rest : Pattern) :
    Path base (node "ErLookup" [count index, environment scope, original, full, rest])
      (node "ErInvalid" [node "ErUnboundIndex" [original]]) := by
  induction scope generalizing index with
  | nil => exact .single (lookup_empty base full rest original (count index))
  | cons head tail ih =>
      cases index with
      | zero => simp at missing
      | succ index =>
          have tailMissing : tail[index]? = none := by simpa only [List.getElem?_cons_succ] using missing
          exact (Relation.ReflTransGen.single
            (lookup_more base (value head) (environment tail) full rest original (count index))).trans
            (ih index tailMissing)

theorem aligned : ReferenceStep.ReferenceProfile baseLanguage := by
  intro rule member
  have checked : baseLanguage.rewrites.all ReferenceStep.ruleAligned = true := by decide_cbv
  exact List.all_eq_true.mp checked rule member

theorem reference_path (relEnv : Engine.RelationEnv) {source target : Pattern}
    (path : Path (engineBasePremises relEnv) source target) :
    Relation.ReflTransGen (ReferenceStep.Step relEnv baseLanguage) source target := by
  induction path with
  | refl => exact .refl
  | tail _ step ih =>
      exact ih.tail ((ReferenceStep.contextualStep_iff_step relEnv baseLanguage aligned).mp step)

theorem source_let_path (base : BasePremiseEvaluator) (captured arguments : List Erlang.Value)
    (body expected original rest : Pattern) :
    Path base (node "ErBindLet"
      [count arguments.length, valueList arguments, environment captured, body, expected, original, rest])
      (node "ErEvaluate" [body, environment (Erlang.extend captured arguments), rest]) := by
  simpa only [environment_extend, valueList_eq_values, List.length_map] using
    let_path base (arguments.map value) (environment captured) body expected original rest

/-- Successful admission retains every authored structural row. -/
theorem prepared_rules (program : Erlang.Program) (depth : Nat) (prepared : Prepared)
    (admitted : prepare program depth = .ok prepared) :
    ∀ rule, rule ∈ baseLanguage.rewrites → rule ∈ prepared.compiled.rewrites := by
  unfold prepare at admitted
  dsimp at admitted
  split at admitted
  · split at admitted
    · cases admitted
      intro rule member
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl member)))
    · contradiction
  · contradiction

/-- The binding paths survive installation in any successfully prepared program. -/
theorem prepared_path (program : Erlang.Program) (depth : Nat) (prepared : Prepared)
    (admitted : prepare program depth = .ok prepared) (relEnv : Engine.RelationEnv)
    {source target : Pattern} (path : Path (engineBasePremises relEnv) source target) :
    Relation.ReflTransGen (ContextualStep.Step (engineBasePremises relEnv) prepared.compiled) source target := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.mono_rules (prepared_rules program depth prepared admitted))

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation.BindingExecution
