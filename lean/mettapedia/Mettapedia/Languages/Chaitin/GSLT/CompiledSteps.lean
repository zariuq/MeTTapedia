import Mettapedia.Languages.Chaitin.GSLT.LanguageDef

/-!
# Exact finite compilation of the authored Lisp configuration rules

Each schema has only data premises. Its interpretation is consequently
independent of contextual derivation depth. The correspondence below checks
the matcher and binding application, rather than postulating the encoded
configuration relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

private theorem premises_independent (base : BasePremiseEvaluator) (lang : LanguageDef)
    {premises : List Premise} (noncontextual : NoncontextualPremises premises)
    (first second : Pattern → List Pattern) (bindings : Bindings) :
    premisesUsing base lang first premises bindings = premisesUsing base lang second premises bindings := by
  induction noncontextual generalizing bindings with
  | nil => rfl
  | freshness rest ih =>
      simp only [premisesUsing, premiseStepUsing]
      apply List.flatMap_congr
      intro next _
      exact ih next
  | relationQuery rest ih =>
      simp only [premisesUsing, premiseStepUsing]
      apply List.flatMap_congr
      intro next _
      exact ih next
  | forAll rest ih =>
      simp only [premisesUsing, premiseStepUsing]
      apply List.flatMap_congr
      intro next _
      exact ih next

theorem rules_noncontextual (rule : RewriteRule) (member : rule ∈ language.rewrites) :
    NoncontextualPremises rule.premises := by
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact .nil | exact .relationQuery .nil

theorem rewriteAt_succ (fuel : Nat) (source : Pattern) :
    rewriteAt dataPremises language (fuel + 1) source = rewriteAt dataPremises language 1 source := by
  simp only [rewriteAt]
  apply List.flatMap_congr
  intro rule member
  simp only [applyRuleUsing]
  apply List.flatMap_congr
  intro bindings _
  rw [premises_independent _ _ (rules_noncontextual rule member)]

theorem step_iff_reduct (source target : Pattern) :
    Step dataPremises language source target ↔ target ∈ rewriteAt dataPremises language 1 source := by
  constructor
  · rintro ⟨fuel, step⟩
    have member := mem_rewriteAt_iff_stepAt.mpr step
    cases fuel with
    | zero => simp [rewriteAt] at member
    | succ fuel => simpa only [rewriteAt_succ] using member
  · intro member
    exact ⟨1, mem_rewriteAt_iff_stepAt.mp member⟩

def reducts (configuration : Configuration) : List Pattern :=
  rewriteAt dataPremises language 1 (encodeConfiguration configuration)

private theorem encode_cons (head : SExpr) (operands : List SExpr) :
    encode (.list (head :: operands)) =
      .apply "List" [.apply "Cons" [encode head, encodeValues operands]] := by
  rw [encode, encodeValues]

private theorem encode_symbol (word : String) :
    encode (.symbol word) = .apply "Word" [encodeWord word] := by rw [encode]

private theorem encode_number (number : Nat) :
    encode (.number number) = .apply "Number" [encodeNat number] := by rw [encode]

private theorem encode_empty : encode (.list []) = .apply "List" [.apply "Nil" []] := by
  rw [encode, encodeValues]

local macro "simp_compile" : tactic =>
  `(tactic| simp [reducts, rewriteAt, language, applyRuleUsing,
    atomRule, callRule, quoteRule, conditionalRule, functionNilRule, functionConsRule,
    positiveRule, negativeRule, argumentNilRule, argumentConsRule, primitiveRule, evalRule, lambdaRule,
    schema, node, metavariable, nilData, query,
    matchPatternForRule_eq_syntactic,
    applyRuleBindings, applyBindingsScoped_zero_of_binderFree, binderFree, binderFreeList,
    matchPattern, matchArgs, mergeBindings, premisesUsing, premiseStepUsing,
    dataPremises, dataBindings, inputCount, outputNames, Bindings.lookup, applyBindings,
    encodeConfiguration, encodeContinuation])

local macro "simp_values" : tactic =>
  `(tactic| simp_all [decode, decodeValues, argumentsConfiguration,
    encodeConfiguration, encodeContinuation, encodeValues, applyBindings,
    List.head?_eq_getElem?])

theorem reducts_call (head : SExpr) (operands : List SExpr) (environment : Environment)
    (continuation : Continuation) :
    reducts (.eval (.list (head :: operands)) environment continuation) =
      [encodeConfiguration (.eval head environment (.function operands environment continuation))] := by
  simp only [reducts, encodeConfiguration, encode_cons]
  simp_compile
  simp [SExpr.atom, decodeValues, decode]

theorem reducts_returned (value : SExpr) : reducts (.returned value .done) = [] := by
  simp_compile

theorem reducts_atom (expression : SExpr) (environment : Environment)
    (continuation : Continuation) (atomic : expression.atom = true) :
    reducts (.eval expression environment continuation) =
      [encodeConfiguration (.returned (lookup environment expression) continuation)] := by
  cases expression with
  | symbol word =>
      simp only [reducts, encodeConfiguration, encode_symbol]
      simp_compile
      simp [decode, SExpr.atom]
  | number number =>
      simp only [reducts, encodeConfiguration, encode_number]
      simp_compile
      simp [decode, SExpr.atom]
  | list values =>
      cases values with
      | nil =>
          simp only [reducts, encodeConfiguration, encode_empty]
          simp_compile
          simp [decode, decodeValues, SExpr.atom]
      | cons first rest => simp [SExpr.atom] at atomic

theorem reducts_function (function : SExpr) (operands : List SExpr) (environment : Environment)
    (continuation : Continuation) :
    reducts (.returned function (.function operands environment continuation)) =
      if function = .symbol "'" then
        [encodeConfiguration (.returned (operands.headD SExpr.nil) continuation)]
      else if function = .symbol "if" then
        [encodeConfiguration (.eval (operands.headD SExpr.nil) environment
          (.conditional (operands.tail.headD SExpr.nil)
            (operands.tail.tail.headD SExpr.nil) environment continuation))]
      else [encodeConfiguration (argumentsConfiguration function [] operands environment continuation)] := by
  cases operands with
  | nil =>
      simp only [reducts, encodeConfiguration, encodeContinuation, encodeValues]
      simp_compile
      by_cases quotation : function = .symbol "'"
      · simp_values
      · by_cases conditional : function = .symbol "if" <;>
          simp_values
  | cons first rest =>
      simp only [reducts, encodeConfiguration, encodeContinuation, encodeValues]
      simp_compile
      by_cases quotation : function = .symbol "'"
      · simp_values
      · by_cases conditional : function = .symbol "if" <;>
          simp_values

theorem reducts_branch (value positive negative : SExpr) (environment : Environment)
    (continuation : Continuation) :
    reducts (.returned value (.conditional positive negative environment continuation)) =
      [encodeConfiguration (.eval (if value.truth then positive else negative) environment continuation)] := by
  simp_compile
  cases truth : value.truth <;> simp_values

theorem reducts_argument (value function : SExpr) (reversed remaining : List SExpr)
    (environment : Environment) (continuation : Continuation) :
    reducts (.returned value (.argument function reversed remaining environment continuation)) =
      [encodeConfiguration (argumentsConfiguration function (value :: reversed) remaining environment continuation)] := by
  cases remaining with
  | nil =>
      simp only [reducts, encodeConfiguration, encodeContinuation, encodeValues]
      simp_compile
      simp_values
  | cons first rest =>
      simp only [reducts, encodeConfiguration, encodeContinuation, encodeValues]
      simp_compile
      simp_values

def LambdaCondition (function : SExpr) (arguments : List SExpr) : Prop :=
  function ≠ .symbol "read-bit" ∧ function ≠ .symbol "read-exp" ∧
  function ≠ .symbol "display" ∧ function ≠ .symbol "debug" ∧
  function ≠ .symbol "eval" ∧ function ≠ .symbol "try" ∧ purePrimitive function arguments = none

instance (function : SExpr) (arguments : List SExpr) : Decidable (LambdaCondition function arguments) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem lambdaCondition_iff (function : SExpr) (arguments : List SExpr) :
    LambdaCondition function arguments ↔ PureEvaluation.LambdaDispatch function arguments :=
  ⟨fun ⟨readBit, readExp, display, debug, eval, try_, primitive⟩ =>
    ⟨readBit, readExp, display, debug, eval, try_, primitive⟩,
    fun ⟨readBit, readExp, display, debug, eval, try_, primitive⟩ =>
      ⟨readBit, readExp, display, debug, eval, try_, primitive⟩⟩

theorem reducts_apply (function : SExpr) (arguments : List SExpr) (environment : Environment)
    (continuation : Continuation) :
    reducts (.apply function arguments environment continuation) =
      ((purePrimitive function arguments).toList.map fun value =>
        encodeConfiguration (.returned value continuation)) ++
      (if function = .symbol "eval" then
        [encodeConfiguration (.eval (arguments.headD SExpr.nil) cleanEnvironment continuation)] else []) ++
      (if LambdaCondition function arguments then
        [encodeConfiguration (.eval function.caddr (bind function.cadr (.list arguments) environment) continuation)]
      else []) := by
  simp_compile
  cases computed : purePrimitive function arguments <;>
    simp only [computed, Option.toList_none, Option.toList_some, List.map_nil,
      List.map_cons, List.nil_append, LambdaCondition,
      Option.some_ne_none, and_false, and_true]
  all_goals split_ifs <;> simp_values

end Mettapedia.Languages.Chaitin.GSLT
