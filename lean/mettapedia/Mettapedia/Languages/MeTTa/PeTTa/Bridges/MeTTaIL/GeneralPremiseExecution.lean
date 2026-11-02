import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseQueryExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMatchingExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseMachineRunExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionCoverage

/-! Source execution of the original general-premise machine with exact bounded state observations. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem specification_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (environment : Environment) (index : Nat) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [number index, encoded (encodeList specificationTerm environment.specifications)]) :
    PureReturns program caller state (a "gslt:premise:specification" [one, two]) state
      (encoded (encodeOption InferenceCettaWire.AuthoredRule.bindingSpecTerm (specification? environment index))) := by
  let values := [number index, encoded (encodeList specificationTerm environment.specifications)]
  let aliases : Subst := [("index", number index),
    ("specifications", encoded (encodeList specificationTerm environment.specifications))]
  have aliased := captured_call_returns _ [] aliases state state "gslt:premise:specification"
    values [v "index", v "specifications"] _ (by decide +kernel) (by decide) (by
      intro offset argument selected
      have bounded : offset < values.length := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 := by simp only [values, List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl <;> exact Or.inl (by decide +kernel)) (by
      intro offset argument selected
      have small : offset = 0 ∨ offset = 1 := by
        have bounded := (List.getElem?_eq_some_iff.mp selected).1
        simp only [List.length_cons, List.length_nil] at bounded
        omega
      rcases small with rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl) (by
      simp [values, aliases, applySubst, Subst.lookup])
    (specification_returns state environment index)
  have lifted := premise_previous_returns (by
    simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
      List.all_nil, Bool.and_true]
    decide +kernel) aliased
  have transported : PureReturns program aliases state (a "gslt:premise:specification" [v "index", v "specifications"])
      state (encoded (encodeOption InferenceCettaWire.AuthoredRule.bindingSpecTerm (specification? environment index))) :=
    premise_returns_in_extension program agreement (by
      simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
        List.all_nil, Bool.and_true]
      decide +kernel) lifted
  apply captured_call_returns program aliases caller state state "gslt:premise:specification"
    [v "index", v "specifications"] [one, two] _ _ (by decide) _ _ _ transported
  · rw [← agreement.dispatch "gslt:premise:specification" (by decide)]
    decide +kernel
  · intro offset argument selected
    have small : offset = 0 ∨ offset = 1 := by
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl
  · intro offset argument selected
    have small : offset = 0 ∨ offset = 1 := by
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl
    all_goals apply Or.inl; rw [← agreement.demand "gslt:premise:specification" _ (by decide)]; decide +kernel
  · simpa [aliases, applySubst, Subst.lookup] using captured.symm


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

namespace Administration

theorem premises_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (environment : Environment) (outer : Execution.Goal)
    (free : List (String × TypeExpr))
    (context : GeneralPremise.Context) (premises : List Premise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premises context premises initial) outer)
    (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm environment.language.terms), encoded (DeclarationTyping.freeContextTerm free),
        goalValue (.premises context premises initial), continuationValue tail]) :
    PureReturns program caller state (a "gslt:premise:machine-evaluate" [one, two, three, four]) state
      (expansionValue (Execution.evaluate environment outer (.premises context premises initial) tail)) := by

  let values := [encoded (DeclarationTyping.declarationsTerm environment.language.terms),
    encoded (DeclarationTyping.freeContextTerm free), goalValue (.premises context premises initial), continuationValue tail]
  let aliases : Subst := [("one", values[0]!), ("two", values[1]!), ("three", values[2]!), ("four", values[3]!)]
  have aliased := captured_call_returns _ [] aliases state state "gslt:premise:machine-evaluate"
    values [v "one", v "two", v "three", v "four"] _ (by decide +kernel) (by decide) (by
      intro offset argument selected
      have bounded : offset < values.length := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
        simp only [values, List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide +kernel)) (by
      intro offset argument selected
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
        simp only [List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl) (by
      simp [values, aliases, applySubst, Subst.lookup])
    (evaluate_premises_free_returns state environment outer free context premises initial tail)
  have lifted := premise_previous_returns (by
    simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
      List.all_nil, Bool.and_true]; decide +kernel) aliased
  have transported : PureReturns program aliases state
      (a "gslt:premise:machine-evaluate" [v "one", v "two", v "three", v "four"]) state
      (expansionValue (Execution.evaluate environment outer (.premises context premises initial) tail)) :=
    premise_returns_in_extension program agreement (by
      simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
        List.all_nil, Bool.and_true]; decide +kernel) lifted
  apply captured_call_returns program aliases caller state state "gslt:premise:machine-evaluate"
    [v "one", v "two", v "three", v "four"] [one, two, three, four] _ _ (by decide) _ _ _ transported
  · rw [← agreement.dispatch "gslt:premise:machine-evaluate" (by decide)]; decide +kernel
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl | rfl
    all_goals apply Or.inl; rw [← agreement.demand "gslt:premise:machine-evaluate" _ (by decide)]; decide +kernel
  · simpa [aliases, values, applySubst, Subst.lookup] using captured.symm


theorem quantified_nil_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (environment : Environment) (outer : Execution.Goal)
    (free : List (String × TypeExpr))
    (context : GeneralPremise.Context) (parameter : String) (body : Premise) (index : Nat) (initial : Assignment)
    (tail : Execution.Continuation environment (.quantified context parameter body index [] initial) outer)
    (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm environment.language.terms), encoded (DeclarationTyping.freeContextTerm free),
        goalValue (.quantified context parameter body index [] initial), continuationValue tail]) :
    PureReturns program caller state (a "gslt:premise:machine-evaluate" [one, two, three, four]) state
      (expansionValue (Execution.evaluate environment outer (.quantified context parameter body index [] initial) tail)) := by

  let values := [encoded (DeclarationTyping.declarationsTerm environment.language.terms),
    encoded (DeclarationTyping.freeContextTerm free), goalValue (.quantified context parameter body index [] initial), continuationValue tail]
  let aliases : Subst := [("one", values[0]!), ("two", values[1]!), ("three", values[2]!), ("four", values[3]!)]
  have aliased := captured_call_returns _ [] aliases state state "gslt:premise:machine-evaluate"
    values [v "one", v "two", v "three", v "four"] _ (by decide +kernel) (by decide) (by
      intro offset argument selected
      have bounded : offset < values.length := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
        simp only [values, List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide +kernel)) (by
      intro offset argument selected
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
        simp only [List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl) (by
      simp [values, aliases, applySubst, Subst.lookup])
    (evaluate_quantified_nil_free_returns state environment outer free context parameter body index initial tail)
  have lifted := premise_previous_returns (by
    simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
      List.all_nil, Bool.and_true]; decide +kernel) aliased
  have transported : PureReturns program aliases state
      (a "gslt:premise:machine-evaluate" [v "one", v "two", v "three", v "four"]) state
      (expansionValue (Execution.evaluate environment outer (.quantified context parameter body index [] initial) tail)) :=
    premise_returns_in_extension program agreement (by
      simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
        List.all_nil, Bool.and_true]; decide +kernel) lifted
  apply captured_call_returns program aliases caller state state "gslt:premise:machine-evaluate"
    [v "one", v "two", v "three", v "four"] [one, two, three, four] _ _ (by decide) _ _ _ transported
  · rw [← agreement.dispatch "gslt:premise:machine-evaluate" (by decide)]; decide +kernel
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl | rfl
    all_goals apply Or.inl; rw [← agreement.demand "gslt:premise:machine-evaluate" _ (by decide)]; decide +kernel
  · simpa [aliases, values, applySubst, Subst.lookup] using captured.symm


theorem steps_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (environment : Environment) (outer : Execution.Goal)
    (free : List (String × TypeExpr))
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit : Nat)
    (tail : Execution.Continuation environment (.steps bound type source limit) outer)
    (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm environment.language.terms), encoded (DeclarationTyping.freeContextTerm free),
        goalValue (.steps bound type source limit), continuationValue tail]) :
    PureReturns program caller state (a "gslt:premise:machine-evaluate" [one, two, three, four]) state
      (expansionValue (Execution.evaluate environment outer (.steps bound type source limit) tail)) := by

  let values := [encoded (DeclarationTyping.declarationsTerm environment.language.terms),
    encoded (DeclarationTyping.freeContextTerm free), goalValue (.steps bound type source limit), continuationValue tail]
  let aliases : Subst := [("one", values[0]!), ("two", values[1]!), ("three", values[2]!), ("four", values[3]!)]
  have aliased := captured_call_returns _ [] aliases state state "gslt:premise:machine-evaluate"
    values [v "one", v "two", v "three", v "four"] _ (by decide +kernel) (by decide) (by
      intro offset argument selected
      have bounded : offset < values.length := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
        simp only [values, List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide +kernel)) (by
      intro offset argument selected
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
        simp only [List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl) (by
      simp [values, aliases, applySubst, Subst.lookup])
    (evaluate_steps_free_returns state environment outer free bound type source limit tail)
  have lifted := premise_previous_returns (by
    simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
      List.all_nil, Bool.and_true]; decide +kernel) aliased
  have transported : PureReturns program aliases state
      (a "gslt:premise:machine-evaluate" [v "one", v "two", v "three", v "four"]) state
      (expansionValue (Execution.evaluate environment outer (.steps bound type source limit) tail)) :=
    premise_returns_in_extension program agreement (by
      simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
        List.all_nil, Bool.and_true]; decide +kernel) lifted
  apply captured_call_returns program aliases caller state state "gslt:premise:machine-evaluate"
    [v "one", v "two", v "three", v "four"] [one, two, three, four] _ _ (by decide) _ _ _ transported
  · rw [← agreement.dispatch "gslt:premise:machine-evaluate" (by decide)]; decide +kernel
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl | rfl
    all_goals apply Or.inl; rw [← agreement.demand "gslt:premise:machine-evaluate" _ (by decide)]; decide +kernel
  · simpa [aliases, values, applySubst, Subst.lookup] using captured.symm


theorem forall_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (environment : Environment) (outer : Execution.Goal)
    (free : List (String × TypeExpr))
    (context : GeneralPremise.Context) (collection parameter : String) (body : Premise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.forAll collection parameter body) initial) outer)
    (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm environment.language.terms), encoded (DeclarationTyping.freeContextTerm free),
        goalValue (.premise context (.forAll collection parameter body) initial), continuationValue tail]) :
    PureReturns program caller state (a "gslt:premise:machine-evaluate" [one, two, three, four]) state
      (expansionValue (Execution.evaluate environment outer (.premise context (.forAll collection parameter body) initial) tail)) := by

  let values := [encoded (DeclarationTyping.declarationsTerm environment.language.terms),
    encoded (DeclarationTyping.freeContextTerm free), goalValue (.premise context (.forAll collection parameter body) initial), continuationValue tail]
  let aliases : Subst := [("one", values[0]!), ("two", values[1]!), ("three", values[2]!), ("four", values[3]!)]
  have aliased := captured_call_returns _ [] aliases state state "gslt:premise:machine-evaluate"
    values [v "one", v "two", v "three", v "four"] _ (by decide +kernel) (by decide) (by
      intro offset argument selected
      have bounded : offset < values.length := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
        simp only [values, List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide +kernel)) (by
      intro offset argument selected
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
        simp only [List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl) (by
      simp [values, aliases, applySubst, Subst.lookup])
    (evaluate_forall_free_returns state environment outer free context collection parameter body initial tail)
  have lifted := premise_previous_returns (by
    simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
      List.all_nil, Bool.and_true]; decide +kernel) aliased
  have transported : PureReturns program aliases state
      (a "gslt:premise:machine-evaluate" [v "one", v "two", v "three", v "four"]) state
      (expansionValue (Execution.evaluate environment outer (.premise context (.forAll collection parameter body) initial) tail)) :=
    premise_returns_in_extension program agreement (by
      simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
        List.all_nil, Bool.and_true]; decide +kernel) lifted
  apply captured_call_returns program aliases caller state state "gslt:premise:machine-evaluate"
    [v "one", v "two", v "three", v "four"] [one, two, three, four] _ _ (by decide) _ _ _ transported
  · rw [← agreement.dispatch "gslt:premise:machine-evaluate" (by decide)]; decide +kernel
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl | rfl
    all_goals apply Or.inl; rw [← agreement.demand "gslt:premise:machine-evaluate" _ (by decide)]; decide +kernel
  · simpa [aliases, values, applySubst, Subst.lookup] using captured.symm


theorem quantified_cons_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (environment : Environment) (outer : Execution.Goal)
    (free : List (String × TypeExpr))
    (context : GeneralPremise.Context) (parameter : String) (body : Premise) (index : Nat) (element : Pattern) (elements : List Pattern) (initial : Assignment)
    (tail : Execution.Continuation environment (.quantified context parameter body index (element :: elements) initial) outer)
    (same : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames
      (bindParameter parameter (localValue context.bound element) initial),
      (WellSorted.FreeTypeContext.ofList free) name = environment.free name)
    (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm environment.language.terms), encoded (DeclarationTyping.freeContextTerm free),
        goalValue (.quantified context parameter body index (element :: elements) initial), continuationValue tail]) :
    PureReturns program caller state (a "gslt:premise:machine-evaluate" [one, two, three, four]) state
      (expansionValue (Execution.evaluate environment outer (.quantified context parameter body index (element :: elements) initial) tail)) := by

  let values := [encoded (DeclarationTyping.declarationsTerm environment.language.terms),
    encoded (DeclarationTyping.freeContextTerm free), goalValue (.quantified context parameter body index (element :: elements) initial), continuationValue tail]
  let aliases : Subst := [("one", values[0]!), ("two", values[1]!), ("three", values[2]!), ("four", values[3]!)]
  have aliased := captured_call_returns _ [] aliases state state "gslt:premise:machine-evaluate"
    values [v "one", v "two", v "three", v "four"] _ (by decide +kernel) (by decide) (by
      intro offset argument selected
      have bounded : offset < values.length := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
        simp only [values, List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide +kernel)) (by
      intro offset argument selected
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
        simp only [List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl) (by
      simp [values, aliases, applySubst, Subst.lookup])
    (evaluate_quantified_cons_free_returns state environment outer free context parameter body index element elements initial tail same)
  have lifted := premise_previous_returns (by
    simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
      List.all_nil, Bool.and_true]; decide +kernel) aliased
  have transported : PureReturns program aliases state
      (a "gslt:premise:machine-evaluate" [v "one", v "two", v "three", v "four"]) state
      (expansionValue (Execution.evaluate environment outer (.quantified context parameter body index (element :: elements) initial) tail)) :=
    premise_returns_in_extension program agreement (by
      simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
        List.all_nil, Bool.and_true]; decide +kernel) lifted
  apply captured_call_returns program aliases caller state state "gslt:premise:machine-evaluate"
    [v "one", v "two", v "three", v "four"] [one, two, three, four] _ _ (by decide) _ _ _ transported
  · rw [← agreement.dispatch "gslt:premise:machine-evaluate" (by decide)]; decide +kernel
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl | rfl
    all_goals apply Or.inl; rw [← agreement.demand "gslt:premise:machine-evaluate" _ (by decide)]; decide +kernel
  · simpa [aliases, values, applySubst, Subst.lookup] using captured.symm


end Administration

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Administration

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open scoped ProgramQuotation

private def source : Program := RuleExecutionProgram.premiseAdministrationProgram
private def expandEquation : SpaceSemantics.Equation := source.equations[4]'(by decide +kernel)
private def expandNames : List String := ["declarations", "free", "task"]
private def expandCaller (values : List Atom) : Subst := (expandNames.zip values).reverse
private def expandCases : SpaceSemantics.Cases := sourceCases expandEquation.body
private def nextData : Atom := a "Some" [a "PremiseExpansion"
  [a "LCons" [a "PremiseEvaluate" [a "RootGoal" [v "bound", v "type", v "source", v "cursor"],
    a "PremiseSearchedRoot" [v "bound", v "type", v "source", v "cursor", v "limit", v "continuation"]],
    a "LCons" [a "PremiseScanChildren" [v "bound", v "type", v "source", v "limit", v "next", v "continuation"],
      .symbol "LNil"]], .symbol "LNil", .symbol "LNil"]]
private def emptyData : Atom := a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]
private def nextBody : Atom := a "let" [v "next", a "+" [v "cursor", number 1], nextData]
private def scanBody : Atom := a "if" [a "<" [v "cursor", v "limit"], nextBody, emptyData]
private theorem expand_shape : expandEquation.body = caseData (v "task") expandCases := by decide +kernel
private theorem expand_cases_syntax : expandCases =
    [(a "PremiseEvaluate" [v "goal", v "continuation"],
        a "gslt:premise:machine-evaluate" [v "declarations", v "free", v "goal", v "continuation"]),
      (a "PremiseDeliver" [v "result", v "continuation"], a "gslt:premise:machine-deliver" [v "result", v "continuation"]),
      (a "PremiseScanChildren" [v "bound", v "type", v "source", v "limit", v "cursor", v "continuation"], scanBody),
      (v "unsupported", .symbol "None")] := by decide +kernel

private theorem expand_call (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = 3) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (expandCaller values) state expandEquation.body state answer) :
    PureReturns program caller state (a "gslt:premise:machine-expand" arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (expandCaller values) state state
    "gslt:premise:machine-expand" arguments expandEquation.body answer
    (by decide) (by decide) (by decide) _ _ _ returned
  · rw [← agreement.dispatch "gslt:premise:machine-expand" (by decide)]; decide +kernel
  · intro index bounded
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rw [← agreement.demand "gslt:premise:machine-expand" index (by decide)]
    rcases small with rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    apply PureData.selected_clause_agreement agreement (by decide)
    exact PureData.named_equation_clause premiseRuntimeProgram "gslt:premise:machine-expand"
      expandEquation expandNames values rfl (by decide +kernel) (by decide) length

private def inertHeads : List String :=
  ["Some", "PremiseExpansion", "LCons", "PremiseEvaluate", "RootGoal", "PremiseSearchedRoot", "PremiseScanChildren"]
private theorem scan_data_template (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (head : String) (arguments : List Atom) (member : head ∈ inertHeads)
    (children : ∀ argument ∈ arguments, PureData.Template program argument) :
    PureData.Template program (a head arguments) := by
  apply PureData.Template.constructor head arguments _ _ children
  · have supported : premiseExecutionHeads head = true := by
      simp only [inertHeads, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← agreement.dispatch head supported]
    have all := List.all_eq_true.mp (show inertHeads.all (fun name => decide
        ((ioHead name || StdLib.known name || premiseRuntimeProgram.equations.any (·.head == name)) = false)) = true by decide +kernel)
    exact of_decide_eq_true (all head member)
  · simp only [inertHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
local macro "scan_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply scan_data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

private theorem natural_lt_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (left right : Nat)
    (first : applySubst caller (v "cursor") = number left)
    (second : applySubst caller (v "limit") = number right) :
    PureReturns program caller state (a "<" [v "cursor", v "limit"]) state (Effects.boolean (left < right)) := by
  apply native_binary_call_returns program caller state state state state "<"
    (v "cursor") (v "limit") (number left) (number right) _
    (by decide) (by decide) _ _ _ _ _ (by decide)
  · rw [← agreement.demand "<" 0 (by decide)]; decide +kernel
  · rw [← agreement.demand "<" 1 (by decide)]; decide +kernel
  · simpa only [first] using variable_returns program caller state "cursor"
  · simpa only [second] using variable_returns program caller state "limit"
  · have calculated : StdLib.apply state "<" [.grounded (.int (left : Int)), .grounded (.int (right : Int))] =
        .ok (state, [Effects.boolean ((left : Int) < (right : Int))]) := rfl
    have order : decide ((left : Int) < (right : Int)) = decide (left < right) := by
      by_cases ordered : left < right
      · have castOrdered : (left : Int) < (right : Int) := by omega
        simp [ordered, castOrdered]
      · have castUnordered : ¬ (left : Int) < (right : Int) := by omega
        simp [ordered, castUnordered]
    simpa only [number, encoded, CettaWireAtom.encode, order] using calculated
private theorem add_one_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (value : Nat)
    (captured : applySubst caller (v "cursor") = number value) :
    PureReturns program caller state (a "+" [v "cursor", number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns program caller state state state state "+"
    (v "cursor") (number 1) (number value) (number 1) (number (value + 1))
    (by decide) (by decide) _ _ _ _ _ (by decide)
  · rw [← agreement.demand "+" 0 (by decide)]; decide +kernel
  · rw [← agreement.demand "+" 1 (by decide)]; decide +kernel
  · simpa only [captured] using variable_returns program caller state "cursor"
  · exact grounded_returns program caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using StdLib.integer_addition state (value : Int) 1

theorem scan_children_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (state : State) (environment : Environment) (outer : Execution.Goal)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (limit cursor : Nat)
    (tail : Execution.Continuation environment (.steps bound type source limit) outer) :
    PureReturns program [] state (a "gslt:premise:machine-expand"
      [encoded (DeclarationTyping.declarationsTerm environment.language.terms), encoded (DeclarationTyping.freeContextTerm free),
        taskValue (.scanChildren bound type source limit cursor tail)]) state
      (expansionValue (Execution.expand environment outer (.scanChildren bound type source limit cursor tail))) := by
  let caller := expandCaller [encoded (DeclarationTyping.declarationsTerm environment.language.terms),
    encoded (DeclarationTyping.freeContextTerm free), taskValue (.scanChildren bound type source limit cursor tail)]
  let selected : Subst := [("continuation", continuationValue tail), ("cursor", number cursor), ("limit", number limit),
    ("source", patternValue source), ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm type)), ("bound", boundValue bound)] ++ caller
  let advanced := ("next", number (cursor + 1)) :: selected
  apply expand_call program agreement [] state _ _ _ rfl (QueryExecution.captured_closed _)
  rw [expand_shape]
  apply branch_returns program caller selected state _ (taskValue (.scanChildren bound type source limit cursor tail)) expandCases scanBody _
  · simpa [caller, expandCaller, expandNames, applySubst, Subst.lookup] using variable_returns program caller state "task"
  · simp [expand_cases_syntax, taskValue, taskTerm, selected, caller, expandCaller, expandNames,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · unfold scanBody
    apply bool_if_returns program selected state _ (decide (cursor < limit)) nextBody emptyData _
    · exact natural_lt_returns program agreement selected state cursor limit
        (by simp [selected, applySubst, Subst.lookup]) (by simp [selected, applySubst, Subst.lookup])
    · by_cases earlier : cursor < limit
      · simp only [earlier, decide_true, ↓reduceIte]
        unfold nextBody
        apply named_let_returns program selected state "next" _ (number (cursor + 1)) nextData _
        · simp [selected, caller, expandCaller, expandNames, Subst.lookup]
        · exact add_one_returns program agreement selected state cursor (by simp [selected, applySubst, Subst.lookup])
        · simpa [nextData, expansionValue, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, Execution.expand, earlier, taskTerm, goalTerm,
            continuationTerm, encodeOption, encodeList, advanced, selected, caller, expandCaller, expandNames,
            applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program advanced state nextData (by unfold nextData; scan_template (program) (agreement))
      · simp only [earlier, decide_false, Bool.false_eq_true, ↓reduceIte]
        simpa [emptyData, expansionValue, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, Execution.expand, earlier, encodeOption, encodeList,
          applySubst, applySubst.applySubstList, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program selected state emptyData (by unfold emptyData; scan_template (program) (agreement))


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Administration


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Administration

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem scan_children_captured_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (environment : Environment) (outer : Execution.Goal)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (limit cursor : Nat)
    (tail : Execution.Continuation environment (.steps bound type source limit) outer) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm environment.language.terms), encoded (DeclarationTyping.freeContextTerm free),
        taskValue (.scanChildren bound type source limit cursor tail)]) :
    PureReturns program caller state (a "gslt:premise:machine-expand" [one, two, three]) state
      (expansionValue (Execution.expand environment outer (.scanChildren bound type source limit cursor tail))) := by
  apply captured_call_returns program [] caller state state "gslt:premise:machine-expand"
    [encoded (DeclarationTyping.declarationsTerm environment.language.terms), encoded (DeclarationTyping.freeContextTerm free),
      taskValue (.scanChildren bound type source limit cursor tail)] [one, two, three] _ _ (by decide) _ _ _
    (scan_children_in_extension_returns program agreement state environment outer free bound type source limit cursor tail)
  · rw [← agreement.dispatch "gslt:premise:machine-expand" (by decide)]; decide +kernel
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    apply Or.inl
    rcases small with rfl | rfl | rfl
    all_goals rw [← agreement.demand "gslt:premise:machine-expand" _ (by decide)]; decide +kernel
  · intro offset argument selected
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    have small : offset = 0 ∨ offset = 1 ∨ offset = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    apply Or.inl
    rcases small with rfl | rfl | rfl
    all_goals rw [← agreement.demand "gslt:premise:machine-expand" _ (by decide)]; decide +kernel
  · simpa only [QueryExecution.captured_closed] using captured.symm


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Administration


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Administration

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem delivered_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (caller : Subst) (state : State) (environment : Environment) (goal outer : Execution.Goal)
    (result : Execution.Result environment goal) (tail : Execution.Continuation environment goal outer)
    (supported : administrativeContinuation tail = true) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [resultValue result, continuationValue tail]) :
    PureReturns program caller state (a "gslt:premise:machine-deliver" [one, two]) state
      (expansionValue (Execution.delivered environment outer result tail)) := by
  let values := [resultValue result, continuationValue tail]
  let aliases : Subst := [("result", resultValue result), ("continuation", continuationValue tail)]
  have aliased := captured_call_returns _ [] aliases state state "gslt:premise:machine-deliver"
    values [v "result", v "continuation"] _ (by decide +kernel) (by decide) (by
      intro offset argument selected
      have bounded : offset < values.length := (List.getElem?_eq_some_iff.mp selected).1
      have small : offset = 0 ∨ offset = 1 := by simp only [values, List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl <;> exact Or.inl (by decide +kernel)) (by
      intro offset argument selected
      have small : offset = 0 ∨ offset = 1 := by
        have bounded := (List.getElem?_eq_some_iff.mp selected).1
        simp only [List.length_cons, List.length_nil] at bounded
        omega
      rcases small with rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl) (by
      simp [values, aliases, applySubst, Subst.lookup])
    (delivered_administrative_returns state environment goal outer result tail supported)
  have lifted := premise_previous_returns (by
    simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
      List.all_nil, Bool.and_true]
    decide +kernel) aliased
  have transported : PureReturns program aliases state (a "gslt:premise:machine-deliver" [v "result", v "continuation"])
      state (expansionValue (Execution.delivered environment outer result tail)) :=
    premise_returns_in_extension program agreement (by
      simp only [v, codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons,
        List.all_nil, Bool.and_true]
      decide +kernel) lifted
  apply captured_call_returns program aliases caller state state "gslt:premise:machine-deliver"
    [v "result", v "continuation"] [one, two] _ _ (by decide) _ _ _ transported
  · rw [← agreement.dispatch "gslt:premise:machine-deliver" (by decide)]
    decide +kernel
  · intro offset argument selected
    have small : offset = 0 ∨ offset = 1 := by
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl
  · intro offset argument selected
    have small : offset = 0 ∨ offset = 1 := by
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl
    all_goals apply Or.inl; rw [← agreement.demand "gslt:premise:machine-deliver" _ (by decide)]; decide +kernel
  · simpa [aliases, applySubst, Subst.lookup] using captured.symm


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Administration


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

namespace Administration

theorem forwarded_shape (index : Nat) (selected : index = 2 ∨ index = 3 ∨ index = 4) :
    goalBody index = a "gslt:premise:machine-evaluate"
      [v "declarations", v "free", v "goal", v "continuation"] := by
  rcases selected with rfl | rfl | rfl <;> decide +kernel

theorem evaluate_premises_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (premiseAgreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (state : State) (environment : Environment) (outer : Execution.Goal)
    (context : GeneralPremise.Context) (premises : List Premise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premises context premises initial) outer)
    (free : List (String × TypeExpr)) :
    PureReturns program [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.premises context premises initial), continuationValue tail]) state
      (expansionValue (Execution.evaluate environment outer (.premises context premises initial) tail)) := by
  let caller := goalCaller environment outer (.premises context premises initial) tail free
  let selected : Subst := [("initial", assignmentValue initial),
    ("premises", encoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm premises)),
    ("context", contextValue context)] ++ caller
  apply evaluate_branch_returns program agreement state environment outer _ tail free selected (goalBody 2) _
  · rw [goal_cases_syntax]
    simp [caller, selected, goalValue, goalTerm, assignmentValue, contextValue,
      goalCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [forwarded_shape 2 (by simp)]
    exact premises_in_extension_returns program premiseAgreement selected state environment outer free
      context premises initial tail (v "declarations") (v "free") (v "goal") (v "continuation") (by
        simp [selected, caller, goalCaller, environmentCaller, callee, Helper.names,
          applySubst, Subst.lookup])

theorem evaluate_steps_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (premiseAgreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (state : State) (environment : Environment) (outer : Execution.Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit : Nat)
    (tail : Execution.Continuation environment (.steps bound type source limit) outer)
    (free : List (String × TypeExpr)) :
    PureReturns program [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.steps bound type source limit), continuationValue tail]) state
      (expansionValue (Execution.evaluate environment outer (.steps bound type source limit) tail)) := by
  let caller := goalCaller environment outer (.steps bound type source limit) tail free
  let selected : Subst := [("limit", number limit), ("source", patternValue source),
    ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm type)), ("bound", boundValue bound)] ++ caller
  apply evaluate_branch_returns program agreement state environment outer _ tail free selected (goalBody 4) _
  · rw [goal_cases_syntax]
    simp [caller, selected, goalValue, goalTerm, patternValue, boundValue,
      goalCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [forwarded_shape 4 (by simp)]
    exact steps_in_extension_returns program premiseAgreement selected state environment outer free
      bound type source limit tail (v "declarations") (v "free") (v "goal") (v "continuation") (by
        simp [selected, caller, goalCaller, environmentCaller, callee, Helper.names,
          applySubst, Subst.lookup])

theorem evaluate_quantified_within_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (premiseAgreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (state : State) (environment : Environment) (outer : Execution.Goal)
    (context : GeneralPremise.Context) (parameter : String) (body : Premise) (index : Nat)
    (elements : List Pattern) (initial : Assignment)
    (tail : Execution.Continuation environment (.quantified context parameter body index elements initial) outer)
    (footprint : List String)
    (covered : assignmentFreeWithin footprint initial ∧ patternsFreeWithin footprint elements) :
    PureReturns program [] state (a Helper.evaluate.head
      [environmentValue environment (environment.free.entriesOn footprint),
        goalValue (.quantified context parameter body index elements initial), continuationValue tail]) state
      (expansionValue (Execution.evaluate environment outer (.quantified context parameter body index elements initial) tail)) := by
  let free := environment.free.entriesOn footprint
  let caller := goalCaller environment outer (.quantified context parameter body index elements initial) tail free
  let selected : Subst := [("initial", assignmentValue initial), ("elements", patternsValue elements),
    ("index", number index), ("body", encoded (InferenceCettaWire.AuthoredRule.premiseTerm body)),
    ("parameter", stringValue parameter), ("context", contextValue context)] ++ caller
  apply evaluate_branch_returns program agreement state environment outer _ tail free selected (goalBody 3) _
  · rw [goal_cases_syntax]
    simp [caller, selected, goalValue, goalTerm, assignmentValue, patternsValue, contextValue,
      goalCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [forwarded_shape 3 (by simp)]
    cases elements with
    | nil =>
        exact quantified_nil_in_extension_returns program premiseAgreement selected state environment outer free
          context parameter body index initial tail (v "declarations") (v "free") (v "goal") (v "continuation") (by
            simp [selected, caller, goalCaller, environmentCaller, callee, Helper.names,
              applySubst, Subst.lookup])
    | cons element elements =>
        have same : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames
            (bindParameter parameter (localValue context.bound element) initial),
            (WellSorted.FreeTypeContext.ofList free) name = environment.free name := by
          intro name occurs
          have member : name ∈ footprint := by
            apply Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_free_names_covered footprint _ _ name occurs
            apply Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.bound_parameter_free_within footprint parameter _ initial covered.1
            exact covered.2 element List.mem_cons_self
          rw [WellSorted.FreeTypeContext.ofList_entriesOn, if_pos member]
        exact quantified_cons_in_extension_returns program premiseAgreement selected state environment outer free
          context parameter body index element elements initial tail same
          (v "declarations") (v "free") (v "goal") (v "continuation") (by
            simp [selected, caller, goalCaller, environmentCaller, callee, Helper.names,
              applySubst, Subst.lookup])


end Administration

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.RootFrame

open Mettapedia.GSLT.LanguageDef CettaWire WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise

def refusedValue (head : String) (index : Nat) : Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
    a "LCons" [a head [number index], .symbol "LNil"]]]

theorem rule_unavailable_wire (environment : Environment) (outer : Execution.Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Execution.Continuation environment (.root bound type source index) outer)
    (declared : environment.language.rewrites[index]? = none) :
    expansionValue (Execution.evaluate environment outer (.root bound type source index) tail) =
      refusedValue "PremiseRuleUnavailable" index := by
  simp only [expansionValue, Execution.evaluate]
  unfold Execution.evaluateRoot
  split
  · rfl
  · rename_i rule found
    simp [declared] at found

theorem specification_unavailable_wire (environment : Environment) (outer : Execution.Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Execution.Continuation environment (.root bound type source index) outer)
    (rule : RewriteRule) (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = none) :
    expansionValue (Execution.evaluate environment outer (.root bound type source index) tail) =
      refusedValue "PremiseBindingUnavailable" index := by
  simp only [expansionValue, Execution.evaluate]
  unfold Execution.evaluateRoot
  split
  · rename_i found
    simp [declared] at found
  · rename_i actualRule found
    have same : actualRule = rule := Option.some.inj (found.symm.trans declared)
    subst actualRule
    split
    · rfl
    · rename_i spec foundSpec
      simp [specified] at foundSpec

theorem binding_rejected_wire (environment : Environment) (outer : Execution.Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Execution.Continuation environment (.root bound type source index) outer)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec) (admitted : admittedFor rule spec = false) :
    expansionValue (Execution.evaluate environment outer (.root bound type source index) tail) =
      refusedValue "PremiseBindingRejected" index := by
  simp only [expansionValue, Execution.evaluate]
  unfold Execution.evaluateRoot
  split
  · rename_i found
    simp [declared] at found
  · rename_i actualRule found
    have same : actualRule = rule := Option.some.inj (found.symm.trans declared)
    subst actualRule
    split
    · rename_i foundSpec
      simp [specified] at foundSpec
    · rename_i actualSpec foundSpec
      have same : actualSpec = spec := Option.some.inj (foundSpec.symm.trans specified)
      subst actualSpec
      simp only [admitted, Bool.false_eq_true, ↓reduceDIte]
      rfl

theorem source_rejected_wire (environment : Environment) (outer : Execution.Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Execution.Continuation environment (.root bound type source index) outer)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec) (admitted : admittedFor rule spec = true)
    (checked : checkOpenPatternWellSorted environment.language environment.free bound type source = false) :
    expansionValue (Execution.evaluate environment outer (.root bound type source index) tail) =
      refusedValue "PremiseSourceRejected" index := by
  simp only [expansionValue, Execution.evaluate]
  unfold Execution.evaluateRoot
  split
  · rename_i found
    simp [declared] at found
  · rename_i actualRule found
    have same : actualRule = rule := Option.some.inj (found.symm.trans declared)
    subst actualRule
    split
    · rename_i foundSpec
      simp [specified] at foundSpec
    · rename_i actualSpec foundSpec
      have same : actualSpec = spec := Option.some.inj (foundSpec.symm.trans specified)
      subst actualSpec
      simp only [admitted, checked, Bool.false_eq_true, ↓reduceDIte]
      rfl

theorem root_started_wire (environment : Environment) (outer : Execution.Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Execution.Continuation environment (.root bound type source index) outer)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec) (admitted : admittedFor rule spec = true)
    (checked : checkOpenPatternWellSorted environment.language environment.free bound type source = true) :
    expansionValue (Execution.evaluate environment outer (.root bound type source index) tail) =
      a "Some" [a "PremiseExpansion" [a "LCons" [a "PremiseRootMatch"
        [boundValue bound, encoded (InferenceCettaWire.AuthoredRule.typeTerm type), patternValue source, number index,
          ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec),
          encoded (RuleInstantiationExecution.GeneralExecution.matcherStateTerm
            (GeneralScopedMatchMachine.start ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩)),
          number 0, continuationValue tail], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]] := by
  simp only [expansionValue, Execution.evaluate]
  unfold Execution.evaluateRoot
  split
  · rename_i found
    simp [declared] at found
  · rename_i actualRule found
    have same : actualRule = rule := Option.some.inj (found.symm.trans declared)
    subst actualRule
    split
    · rename_i foundSpec
      simp [specified] at foundSpec
    · rename_i actualSpec foundSpec
      have same : actualSpec = spec := Option.some.inj (foundSpec.symm.trans specified)
      subst actualSpec
      simp only [admitted, checked, ↓reduceDIte]
      rfl


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.RootFrame


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

namespace RootFrame

local macro "root_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by first | assumption | decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

theorem refused_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (head : String) (supported : head ∈ dataHeads) : PureData.Template program (refusedData head) := by
  unfold refusedData
  root_template (program) (agreement)
theorem accepted_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) :
    PureData.Template program rootData := by unfold rootData; root_template (program) (agreement)
theorem request_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) :
    PureData.Template program (rootPairs[1]!).2 := by
  change PureData.Template program (a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient",
    .symbol "RuleLeft", .symbol "LNil", number 0, .symbol "LNil", v "left", v "source"])
  root_template (program) (agreement)

theorem row_encoded_returns {α : Type} (program : Program) (lower : MatcherFrames.LowerOperations program)
    (encoder : α → Term) (caller : Subst) (state : State) (index : Nat) (values : List α) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number index, encoded (encodeList encoder values)]) :
    PureReturns program caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (encodeOption encoder values[index]?)) := by
  have returned := lower.row caller state index (values.map encoder) one two (by
    simpa only [MatcherFrames.termListValue, encodeList_map, Function.id_comp] using captured)
  cases found : values[index]? <;> simpa [List.getElem?_map, found, encodeOption] using returned

def request (rule : RewriteRule) (spec : RuleBindingSpec) (bound : List TypeExpr) (source : Pattern) :
    GeneralScopedMatchMachine.Request := ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩

theorem evaluate_root_within_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (premiseAgreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (lower : MatcherFrames.LowerOperations program) (admission : AdmissionOperations program)
    (state : State) (environment : Environment) (outer : Execution.Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Execution.Continuation environment (.root bound type source index) outer)
    (footprint : List String) (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns program [] state (a Helper.evaluate.head
      [environmentValue environment (environment.free.entriesOn footprint),
        goalValue (.root bound type source index), continuationValue tail]) state
      (expansionValue (Execution.evaluate environment outer (.root bound type source index) tail)) := by
  let free := environment.free.entriesOn footprint
  let caller := rootCaller environment outer bound type source index tail free
  have row := row_encoded_returns program lower InferenceCettaWire.AuthoredRule.rewriteTerm caller state index
    environment.language.rewrites (v "index") (v "rewrites") (by
      simp [caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
  apply evaluate_root_body_returns program agreement state environment outer bound type source index tail free
  rw [lookup_shape]
  cases declared : environment.language.rewrites[index]? with
  | none =>
      apply branch_returns program caller caller state _ (.symbol "None") lookupCases
        (refusedData "PremiseRuleUnavailable") _
      · simpa [declared, encodeOption, CettaWireAtom.encode] using row
      · simp [lookup_cases_syntax, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · rw [rule_unavailable_wire environment outer bound type source index tail declared]
        simpa [refusedData, refusedValue,
          caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
          applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program caller state _ (refused_template program agreement "PremiseRuleUnavailable" (by decide))
  | some rule =>
      let found : Subst := ("rule", ruleValue rule) :: caller
      let ruled : Subst := [("bindings", encoded (InferenceCettaWire.AuthoredRule.optionalBindingTerm rule.bindings)),
        ("right", patternValue rule.right), ("left", patternValue rule.left),
        ("premises", encoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises)),
        ("ruleTypes", encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm rule.typeContext)),
        ("ruleName", stringValue rule.name)] ++ found
      apply branch_returns program caller found state _ (a "Some" [ruleValue rule]) lookupCases foundBody _
      · simpa [declared, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany] using row
      · simp [lookup_cases_syntax, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · rw [found_shape]
        apply branch_returns program found ruled state _ (ruleValue rule) ruleCases ruleBody _
        · simpa [found, applySubst, Subst.lookup] using variable_returns program found state "rule"
        · simp [inference_list_wire, rule_cases_syntax, ruleValue, InferenceCettaWire.AuthoredRule.rewriteTerm,
            ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
        · rw [rule_shape]
          have specification := specification_in_extension_returns program premiseAgreement ruled state environment index
            (v "index") (v "specifications") (by
              simp [ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
                applySubst, Subst.lookup])
          cases specified : specification? environment index with
          | none =>
              apply branch_returns program ruled ruled state _ (.symbol "None") specificationCases
                (refusedData "PremiseBindingUnavailable") _
              · simpa [specified, encodeOption, CettaWireAtom.encode] using specification
              · simp [specification_cases_syntax, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · rw [specification_unavailable_wire environment outer bound type source index tail rule declared specified]
                simpa [refusedData, refusedValue,
                  ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
                  applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return program ruled state _
                    (refused_template program agreement "PremiseBindingUnavailable" (by decide))
          | some spec =>
              let selected : Subst := ("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)) :: ruled
              apply branch_returns program ruled selected state _
                (a "Some" [encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)]) specificationCases admittedBody _
              · simpa [specified, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany] using specification
              · simp [specification_cases_syntax, selected, ruled, found, caller, rootCaller,
                  goalCaller, environmentCaller, callee, Helper.names,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup]
              · rw [admitted_shape]
                apply bool_if_returns program selected state _ (admittedFor rule spec) _ _ _
                · exact binding_admitted_captured_returns program agreement admission selected state rule spec
                    (v "rule") (v "spec") (by
                      simp [selected, ruled, found, caller, rootCaller, goalCaller, environmentCaller,
                        callee, Helper.names, applySubst, Subst.lookup])
                · cases admitted : admittedFor rule spec with
                  | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      rw [binding_rejected_wire environment outer bound type source index tail rule spec declared specified admitted]
                      simpa [refusedData, refusedValue,
                        selected, ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
                        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                        PureData.template_return program selected state _
                          (refused_template program agreement "PremiseBindingRejected" (by decide))
                  | true =>
                      simp only [↓reduceIte]
                      apply bool_if_returns program selected state _
                        (checkOpenPatternWellSorted environment.language environment.free bound type source) _ _ _
                      · have sorted := lower.sorted selected state environment.language free bound type source
                          (v "declarations") (v "free") (v "bound") (v "type") (v "source") (by
                            simp [MatcherFrames.declarationsValue, DeclarationTyping.declarationsTerm,
                              MatcherFrames.freeValue, MatcherFrames.boundValue, MatcherFrames.typeValue, MatcherFrames.patternValue,
                              selected, ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
                              applySubst, Subst.lookup])
                        rw [Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot environment.language environment.free bound type source footprint covered] at sorted
                        exact sorted
                      · cases checked : checkOpenPatternWellSorted environment.language environment.free bound type source with
                        | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            rw [source_rejected_wire environment outer bound type source index tail rule spec declared specified admitted checked]
                            simpa [refusedData, refusedValue,
                              selected, ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
                              applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                              PureData.template_return program selected state _
                                (refused_template program agreement "PremiseSourceRejected" (by decide))
                        | true =>
                            simp only [↓reduceIte]
                            let ambient := ("ambient", number bound.length) :: selected
                            let requested := ("query", MatcherFrames.requestValue (request rule spec bound source)) :: ambient
                            let matched := ("matcher", MatcherFrames.matcherValue
                              (GeneralScopedMatchMachine.start (request rule spec bound source))) :: requested
                            unfold acceptedBody
                            apply PureData.let_bindings_return (final := matched) (pairs := rootPairs)
                            · unfold rootPairs
                              apply PureData.BindingsReturn.cons (bound := ambient)
                              · simpa only [List.length_map] using lower.length selected state
                                  (bound.map InferenceCettaWire.AuthoredRule.typeTerm) (v "bound") (by
                                    simp [MatcherFrames.termListValue, encodeList_map,
                                      selected, ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
                                      applySubst, Subst.lookup])
                              · simp [ambient, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                                  selected, ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names, Subst.lookup]
                              · apply PureData.BindingsReturn.cons (bound := requested)
                                · simpa [rootPairs, request, MatcherFrames.requestValue,
                                    RuleInstantiationExecution.GeneralExecution.matcherRequestTerm, encodeList,
                                    ambient, selected, ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
                                    applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                                    PureData.template_return program ambient state _ (request_template program agreement)
                                · simp [requested, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                                    ambient, selected, ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names, Subst.lookup]
                                  rfl
                                · apply PureData.BindingsReturn.cons (bound := matched)
                                  · exact lower.start requested state (request rule spec bound source) (v "query") (by
                                      simp [requested, applySubst, Subst.lookup])
                                  · simp [matched, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                                      requested, ambient, selected, ruled, found, caller, rootCaller, goalCaller, environmentCaller, callee, Helper.names, Subst.lookup]
                                  · exact PureData.BindingsReturn.nil matched state
                            · rw [root_started_wire environment outer bound type source index tail rule spec declared specified admitted checked]
                              simpa [rootData,
                                request, MatcherFrames.matcherValue, MatcherFrames.requestValue,
                                matched, requested, ambient, selected, ruled, found, caller, rootCaller,
                                goalCaller, environmentCaller, callee, Helper.names,
                                applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                                PureData.template_return program matched state _ (accepted_template program agreement)


end RootFrame

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program)
open Effects (State)
open Eval

def freshnessCaller (environment : Environment) (outer : Execution.Goal) (context : Context)
    (condition : FreshnessCondition) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("subjectSchema", patternValue condition.term), ("name", stringValue condition.varName)] ++
    premiseContextCaller environment outer context (.freshness condition) initial tail free

def congruenceCaller (environment : Environment) (outer : Execution.Goal) (context : Context)
    (source target : Pattern) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.congruence source target) initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("targetSchema", patternValue target), ("sourceSchema", patternValue source)] ++
    premiseContextCaller environment outer context (.congruence source target) initial tail free

def scopedStepCaller (environment : Environment) (outer : Execution.Goal) (context : Context)
    (step : ScopedStepPremise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.scopedStep step) initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("targetSchema", patternValue step.target), ("sourceSchema", patternValue step.source),
    ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm step.resultType)), ("binders", boundValue step.binders)] ++
    premiseContextCaller environment outer context (.scopedStep step) initial tail free

theorem freshness_body_returns (state : State) (environment : Environment) (outer : Execution.Goal) (context : Context)
    (condition : FreshnessCondition) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (free : List (String × TypeExpr)) (answer : Atom)
    (returned : PureReturns RuleExecutionProgram.scopedMachineProgram (freshnessCaller environment outer context condition initial tail free)
      state (premiseBody 1) state answer) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.premise context (.freshness condition) initial), continuationValue tail])
      state answer := by
  apply evaluate_premise_body_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement
    state environment outer context (.freshness condition) initial tail free answer
  rw [premise_context_shape]
  apply branch_returns RuleExecutionProgram.scopedMachineProgram (premiseContextCaller environment outer context (.freshness condition) initial tail free)
    (freshnessCaller environment outer context condition initial tail free) state _
    (encoded (InferenceCettaWire.AuthoredRule.premiseTerm (.freshness condition))) premiseCases (premiseBody 1) answer
  · simpa [premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
      applySubst, Subst.lookup] using
      variable_returns RuleExecutionProgram.scopedMachineProgram (premiseContextCaller environment outer context (.freshness condition) initial tail free)
        state "premise"
  · simp [premise_cases, InferenceCettaWire.AuthoredRule.premiseTerm, freshnessCaller,
      premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · exact returned

theorem congruence_body_returns (state : State) (environment : Environment) (outer : Execution.Goal) (context : Context)
    (source target : Pattern) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.congruence source target) initial) outer)
    (free : List (String × TypeExpr)) (answer : Atom)
    (returned : PureReturns RuleExecutionProgram.scopedMachineProgram (congruenceCaller environment outer context source target initial tail free)
      state (premiseBody 3) state answer) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.premise context (.congruence source target) initial), continuationValue tail])
      state answer := by
  apply evaluate_premise_body_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement
    state environment outer context (.congruence source target) initial tail free answer
  rw [premise_context_shape]
  apply branch_returns RuleExecutionProgram.scopedMachineProgram (premiseContextCaller environment outer context (.congruence source target) initial tail free)
    (congruenceCaller environment outer context source target initial tail free) state _
    (encoded (InferenceCettaWire.AuthoredRule.premiseTerm (.congruence source target))) premiseCases (premiseBody 3) answer
  · simpa [premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
      applySubst, Subst.lookup] using
      variable_returns RuleExecutionProgram.scopedMachineProgram (premiseContextCaller environment outer context (.congruence source target) initial tail free)
        state "premise"
  · simp [premise_cases, InferenceCettaWire.AuthoredRule.premiseTerm, congruenceCaller,
      premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · exact returned

theorem scoped_step_body_returns (state : State) (environment : Environment) (outer : Execution.Goal) (context : Context)
    (step : ScopedStepPremise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.scopedStep step) initial) outer)
    (free : List (String × TypeExpr)) (answer : Atom)
    (returned : PureReturns RuleExecutionProgram.scopedMachineProgram (scopedStepCaller environment outer context step initial tail free)
      state (premiseBody 4) state answer) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.premise context (.scopedStep step) initial), continuationValue tail])
      state answer := by
  apply evaluate_premise_body_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement
    state environment outer context (.scopedStep step) initial tail free answer
  rw [premise_context_shape]
  apply branch_returns RuleExecutionProgram.scopedMachineProgram (premiseContextCaller environment outer context (.scopedStep step) initial tail free)
    (scopedStepCaller environment outer context step initial tail free) state _
    (encoded (InferenceCettaWire.AuthoredRule.premiseTerm (.scopedStep step))) premiseCases (premiseBody 4) answer
  · simpa [premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
      applySubst, Subst.lookup] using
      variable_returns RuleExecutionProgram.scopedMachineProgram (premiseContextCaller environment outer context (.scopedStep step) initial tail free)
        state "premise"
  · simp [premise_cases, InferenceCettaWire.AuthoredRule.premiseTerm, InferenceCettaWire.encodeList, scopedStepCaller,
      premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · exact returned

def transitionDataHeads : List String := dataHeads ++ ["PremiseEvaluate"]
theorem transition_data_template (head : String) (arguments : List Atom) (member : head ∈ transitionDataHeads)
    (children : ∀ argument ∈ arguments, PureData.Template RuleExecutionProgram.scopedMachineProgram argument) :
    PureData.Template RuleExecutionProgram.scopedMachineProgram (a head arguments) := by
  simp only [transitionDataHeads, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact data_template RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement head arguments member children
  · exact PureData.Template.constructor "PremiseEvaluate" arguments (by decide +kernel) (by decide) children


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval

def emptyData : Atom := a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]
def stepProjectionData : Atom := a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
  a "LCons" [a "PremiseStepProjection" [v "premiseIndex", v "quantifiers"], .symbol "LNil"]]]
def stepSortData : Atom := a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
  a "LCons" [a "PremiseStepSort" [v "premiseIndex", v "quantifiers"], .symbol "LNil"]]]
def childData (effectiveBound binders : Atom) : Atom :=
  a "Some" [a "PremiseExpansion" [a "LCons" [a "PremiseEvaluate" [
    a "StepsGoal" [effectiveBound, v "type", v "actualSource", v "ruleIndex"],
    a "PremiseStepped" [a "PremiseStepCall" [v "context", v "premise", v "initial", binders,
      v "type", v "actualSource", v "targetSchema"], v "continuation"]], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]
def ordinaryInstantiation (depth source : Atom) : Atom := a "gslt:rule:scope-instantiate-at" [
  .symbol "None", v "rule", v "spec", v "ambient", a "RulePremise" [v "premiseIndex", v "quantifiers", number 0],
  .symbol "LNil", depth, v "initial", source]
def childProjectionCases (effectiveBound binders : Atom) : SpaceSemantics.Cases :=
  [(.symbol "None", stepProjectionData), (a "Some" [v "actualSource"], childData effectiveBound binders),
    (v "badProjection", .symbol "None")]
def childProjectionBody (depth effectiveBound binders : Atom) : Atom :=
  caseData (ordinaryInstantiation depth (v "sourceSchema")) (childProjectionCases effectiveBound binders)
def congruenceTypeBody : Atom := a "let" [v "ambient", a "gslt:automata:length" [v "bound"],
  childProjectionBody (number 0) (v "bound") (.symbol "LNil")]
def congruenceTypeCases : SpaceSemantics.Cases :=
  [(.symbol "None", stepSortData), (a "Some" [v "type"], congruenceTypeBody), (v "badType", .symbol "None")]

theorem congruence_shape : premiseBody 3 =
    caseData (a "gslt:premise:source-type" [v "declarations", v "rule", v "sourceSchema"])
      congruenceTypeCases := by decide +kernel

def scopedStepPairs : List Atom :=
  [.expression [v "ambient", a "gslt:automata:length" [v "bound"]],
    .expression [v "depth", a "gslt:automata:length" [v "binders"]],
    .expression [v "effectiveBound", a "gslt:automata:append" [v "binders", v "bound"]]]
def scopedStepNested : Atom :=
  a "let" [v "ambient", a "gslt:automata:length" [v "bound"],
    a "let" [v "depth", a "gslt:automata:length" [v "binders"],
      a "let" [v "effectiveBound", a "gslt:automata:append" [v "binders", v "bound"],
        childProjectionBody (v "depth") (v "effectiveBound") (v "binders")]]]
theorem scoped_step_shape : premiseBody 4 =
    a "let*" [.expression scopedStepPairs, childProjectionBody (v "depth") (v "effectiveBound") (v "binders")] := by
  decide +kernel
theorem scoped_step_nested : Eval.nestedLets scopedStepPairs
    (childProjectionBody (v "depth") (v "effectiveBound") (v "binders")) = some scopedStepNested := rfl

def freshnessProjectionData : Atom := a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
  a "LCons" [a "PremiseFreshnessProjection" [v "premiseIndex", v "quantifiers"], .symbol "LNil"]]]
def freshnessData : Atom := a "Some" [a "PremiseExpansion" [a "LCons" [a "PremiseDeliver" [
  a "PremiseResult" [v "goal", a "PremiseAnswer" [v "initial",
    a "PremiseFreshnessEvent" [v "premiseIndex", v "quantifiers", v "atom", v "subject"]]], v "continuation"],
  .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]
def freshnessCheckedBody : Atom := a "if" [a "gslt:premise:fresh" [v "atom", v "subject"], freshnessData, emptyData]
def freshnessSubjectCases : SpaceSemantics.Cases :=
  [(.symbol "None", freshnessProjectionData), (a "Some" [v "subject"], freshnessCheckedBody),
    (v "badSubject", .symbol "None")]
def freshnessSubjectBody : Atom := caseData (ordinaryInstantiation (number 0) (v "subjectSchema")) freshnessSubjectCases
def freshnessNameCases : SpaceSemantics.Cases :=
  [(.symbol "None", freshnessProjectionData), (a "Some" [v "atom"], freshnessSubjectBody), (v "badName", .symbol "None")]
def freshnessNameBody : Atom := caseData (v "nameOption") freshnessNameCases
def freshnessResolvedCases : SpaceSemantics.Cases :=
  [(a "Some" [a "FVar" [v "atom"]], a "Some" [v "atom"]), (v "nonName", .symbol "None")]
def freshnessStoredBody : Atom := caseData (a "gslt:rule:scope-instantiate-value" [
  v "stored", v "ambient", number 0, .symbol "LNil"]) freshnessResolvedCases
def freshnessLookupCases : SpaceSemantics.Cases :=
  [(.symbol "None", a "Some" [v "name"]), (a "Some" [v "stored"], freshnessStoredBody),
    (v "badLookup", .symbol "None")]
def freshnessLookupBody : Atom := caseData (a "gslt:automata:binding" [v "name", v "initial"]) freshnessLookupCases
theorem freshness_shape : premiseBody 1 = a "let" [v "ambient", a "gslt:automata:length" [v "bound"],
    a "let" [v "nameOption", freshnessLookupBody, freshnessNameBody]] := by decide +kernel

local macro "transition_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply transition_data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

theorem empty_template : PureData.Template RuleExecutionProgram.scopedMachineProgram emptyData := by unfold emptyData; transition_template
theorem step_projection_template : PureData.Template RuleExecutionProgram.scopedMachineProgram stepProjectionData := by
  unfold stepProjectionData; transition_template
theorem step_sort_template : PureData.Template RuleExecutionProgram.scopedMachineProgram stepSortData := by unfold stepSortData; transition_template
theorem child_template (effectiveBound binders : Atom)
    (one : PureData.Template RuleExecutionProgram.scopedMachineProgram effectiveBound) (two : PureData.Template RuleExecutionProgram.scopedMachineProgram binders) :
    PureData.Template RuleExecutionProgram.scopedMachineProgram (childData effectiveBound binders) := by
  unfold childData
  repeat' first
  | exact one
  | exact two
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply transition_data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)

theorem freshness_projection_template : PureData.Template RuleExecutionProgram.scopedMachineProgram freshnessProjectionData := by
  unfold freshnessProjectionData; transition_template
theorem freshness_template : PureData.Template RuleExecutionProgram.scopedMachineProgram freshnessData := by unfold freshnessData; transition_template


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise

theorem evaluate_congruence_sort_none_eq (environment : Environment) (outer : Execution.Goal)
    (context : Context) (source target : Pattern) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.congruence source target) initial) outer)
    (typed : GeneralPremise.sourceType? environment.language context.rule source = none) :
    Execution.evaluate environment outer (.premise context (.congruence source target) initial) tail =
      { unresolved := [.stepSort context.premiseIndex context.quantifierDepth] } := by
  rw [Execution.evaluate.eq_1, Execution.evaluatePremise.eq_4]
  split
  · rfl
  · rename_i type found
    simp [typed] at found

theorem evaluate_congruence_projection_none_eq (environment : Environment) (outer : Execution.Goal)
    (context : Context) (source target : Pattern) (initial : Assignment) (type : TypeExpr)
    (tail : Execution.Continuation environment (.premise context (.congruence source target) initial) outer)
    (typed : GeneralPremise.sourceType? environment.language context.rule source = some type)
    (interpreted : ScopedRuleMatching.instantiateAt? context.rule context.spec context.bound.length
      (context.site 0) [] 0 initial source = none) :
    Execution.evaluate environment outer (.premise context (.congruence source target) initial) tail =
      { unresolved := [.stepProjection context.premiseIndex context.quantifierDepth] } := by
  rw [Execution.evaluate.eq_1, Execution.evaluatePremise.eq_4]
  split
  · rename_i unavailable
    simp [typed] at unavailable
  · rename_i actualType found
    have same := Option.some.inj (found.symm.trans typed)
    subst actualType
    split
    · rfl
    · rename_i actualSource found
      simp [interpreted] at found

theorem evaluate_congruence_some_eq (environment : Environment) (outer : Execution.Goal)
    (context : Context) (source target actualSource : Pattern) (initial : Assignment) (type : TypeExpr)
    (tail : Execution.Continuation environment (.premise context (.congruence source target) initial) outer)
    (typed : GeneralPremise.sourceType? environment.language context.rule source = some type)
    (interpreted : ScopedRuleMatching.instantiateAt? context.rule context.spec context.bound.length
      (context.site 0) [] 0 initial source = some actualSource) :
    Execution.evaluate environment outer (.premise context (.congruence source target) initial) tail =
      { tasks := [.evaluate (.steps context.bound type actualSource context.ruleIndex)
          (.stepped {
            context := context, premise := .congruence source target, initial := initial, binders := [],
            type := type, source := actualSource, targetSchema := target,
            conclude := fun _ _ _ _ _ _ _ _ child matching finalTyped => .step typed interpreted child matching finalTyped } tail)] } := by
  rw [Execution.evaluate.eq_1, Execution.evaluatePremise.eq_4]
  split
  · rename_i unavailable
    simp [typed] at unavailable
  · rename_i actualType found
    have same := Option.some.inj (found.symm.trans typed)
    subst actualType
    split
    · rename_i unavailable
      simp [interpreted] at unavailable
    · rename_i actual found
      have same := Option.some.inj (found.symm.trans interpreted)
      subst actual
      rfl

theorem evaluate_scoped_step_none_eq (environment : Environment) (outer : Execution.Goal)
    (context : Context) (step : ScopedStepPremise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.scopedStep step) initial) outer)
    (interpreted : ScopedRuleMatching.instantiateAt? context.rule context.spec context.bound.length
      (context.site 0) [] step.binders.length initial step.source = none) :
    Execution.evaluate environment outer (.premise context (.scopedStep step) initial) tail =
      { unresolved := [.stepProjection context.premiseIndex context.quantifierDepth] } := by
  rw [Execution.evaluate.eq_1, Execution.evaluatePremise.eq_5]
  split
  · rfl
  · rename_i actualSource found
    simp [interpreted] at found

theorem evaluate_scoped_step_some_eq (environment : Environment) (outer : Execution.Goal)
    (context : Context) (step : ScopedStepPremise) (actualSource : Pattern) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.scopedStep step) initial) outer)
    (interpreted : ScopedRuleMatching.instantiateAt? context.rule context.spec context.bound.length
      (context.site 0) [] step.binders.length initial step.source = some actualSource) :
    Execution.evaluate environment outer (.premise context (.scopedStep step) initial) tail =
      { tasks := [.evaluate (.steps (step.binders ++ context.bound) step.resultType actualSource context.ruleIndex)
          (.stepped {
            context := context, premise := .scopedStep step, initial := initial, binders := step.binders,
            type := step.resultType, source := actualSource, targetSchema := step.target,
            conclude := fun _ _ _ _ _ _ _ _ child matching finalTyped => .scopedStep interpreted child matching finalTyped } tail)] } := by
  rw [Execution.evaluate.eq_1, Execution.evaluatePremise.eq_5]
  split
  · rename_i unavailable
    simp [interpreted] at unavailable
  · rename_i actual found
    have same := Option.some.inj (found.symm.trans interpreted)
    subst actual
    rfl

theorem evaluate_freshness_none_eq (environment : Environment) (outer : Execution.Goal)
    (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (read : GeneralPremise.freshnessSubject? context.rule context.spec context.bound context.premiseIndex
      context.quantifierDepth initial condition = none) :
    Execution.evaluate environment outer (.premise context (.freshness condition) initial) tail =
      { unresolved := [.freshnessProjection context.premiseIndex context.quantifierDepth] } := by
  rw [Execution.evaluate.eq_1, Execution.evaluatePremise.eq_2]
  split
  · rfl
  · rename_i atom subject found
    simp [read] at found

theorem evaluate_freshness_false_eq (environment : Environment) (outer : Execution.Goal)
    (context : Context) (condition : FreshnessCondition) (initial : Assignment) (atom : String) (subject : Pattern)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (read : GeneralPremise.freshnessSubject? context.rule context.spec context.bound context.premiseIndex
      context.quantifierDepth initial condition = some (atom, subject))
    (checked : Substitution.isFresh atom subject = false) :
    Execution.evaluate environment outer (.premise context (.freshness condition) initial) tail = {} := by
  rw [Execution.evaluate.eq_1, Execution.evaluatePremise.eq_2]
  split
  · rename_i unavailable
    simp [read] at unavailable
  · rename_i actualAtom actualSubject found
    have same := Option.some.inj (found.symm.trans read)
    have one := congrArg Prod.fst same
    have two := congrArg Prod.snd same
    dsimp only at one two
    subst actualAtom actualSubject
    simp [checked]

theorem evaluate_freshness_true_eq (environment : Environment) (outer : Execution.Goal)
    (context : Context) (condition : FreshnessCondition) (initial : Assignment) (atom : String) (subject : Pattern)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (read : GeneralPremise.freshnessSubject? context.rule context.spec context.bound context.premiseIndex
      context.quantifierDepth initial condition = some (atom, subject))
    (checked : Substitution.isFresh atom subject = true) :
    Execution.evaluate environment outer (.premise context (.freshness condition) initial) tail =
      { tasks := [.deliver (.premise initial (.freshness context.premiseIndex context.quantifierDepth atom subject)
          (.freshness read ((syntactic_freshness_iff atom subject).mp checked))) tail] } := by
  rw [Execution.evaluate.eq_1, Execution.evaluatePremise.eq_2]
  split
  · rename_i unavailable
    simp [read] at unavailable
  · rename_i actualAtom actualSubject found
    have same := Option.some.inj (found.symm.trans read)
    have one := congrArg Prod.fst same
    have two := congrArg Prod.snd same
    dsimp only at one two
    subst actualAtom actualSubject
    simp [checked]


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions


set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower

open Eval

def ruleHeadNames : List String :=
  ["+",
   "-",
   "<",
   "==",
   ">=",
   "Binding",
   "ContextualValue",
   "FVar",
   "LCons",
   "LNil",
   "None",
   "OccurrenceAssignment",
   "PApp",
   "PCollection",
   "PLam",
   "PMultiLam",
   "PSubst",
   "RecoveryAssignment",
   "Some",
   "Var",
   "case",
   "gslt:automata:append",
   "gslt:automata:binding",
   "gslt:automata:length",
   "gslt:automata:member",
   "gslt:premise:free-vars",
   "gslt:premise:free-vars-list",
   "gslt:premise:fresh",
   "gslt:rule:lift-bvars",
   "gslt:rule:lift-bvars-list",
   "gslt:rule:row-at",
   "gslt:rule:scope-assignment",
   "gslt:rule:scope-index",
   "gslt:rule:scope-instantiate-value",
   "gslt:rule:scope-substitute",
   "gslt:rule:scope-substitute-list",
   "gslt:rule:scope-well-scoped",
   "gslt:rule:scope-well-scoped-list",
   "if",
   "let",
   "let*"]

def ruleHeads (head : String) : Bool := ruleHeadNames.contains head

theorem rule_closed : ProgramClosed ruleHeads RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RuleExecutionProgram.program.equations.all (fun equation =>
        !ruleHeads equation.head || codeWithin ruleHeads equation.body) = true := by rfl
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

theorem rule_retained_equations :
    RuleExecutionProgram.program.equations.filter (fun equation => ruleHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => ruleHeads equation.head) := by rfl

theorem rule_retained_declarations :
    RuleExecutionProgram.program.declarations.filter (retainedCallDeclaration ruleHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration ruleHeads) := by rfl

theorem rule_agreement : ProgramAgreementOn ruleHeads RuleExecutionProgram.program RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _ rule_retained_equations rule_retained_declarations


def sourceTypeHeadNames : List String :=
  ["==",
   "FVar",
   "GrammarTypingV1", "GrammarTypingWrappedV1",
   "LCons",
   "LNil",
   "PApp",
   "ScopedRewriteRuleV1",
   "Some",
   "TBase",
   "TypeBinding",
   "case",
   "gslt:premise:constructor-declarations",
   "gslt:premise:source-type",
   "gslt:premise:type-context-lookup",
   "if",
   "let"]

def sourceTypeHeads (head : String) : Bool := sourceTypeHeadNames.contains head

theorem sourceType_closed : ProgramClosed sourceTypeHeads premiseRuntimeProgram := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : premiseRuntimeProgram.equations.all (fun equation =>
        !sourceTypeHeads equation.head || codeWithin sourceTypeHeads equation.body) = true := by rfl
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

theorem sourceType_retained_equations :
    premiseRuntimeProgram.equations.filter (fun equation => sourceTypeHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => sourceTypeHeads equation.head) := by rfl

theorem sourceType_retained_declarations :
    premiseRuntimeProgram.declarations.filter (retainedCallDeclaration sourceTypeHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration sourceTypeHeads) := by rfl

theorem sourceType_agreement : ProgramAgreementOn sourceTypeHeads premiseRuntimeProgram RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _ sourceType_retained_equations sourceType_retained_declarations


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval
open InferenceCettaWire.AuthoredRule (contextualValueTerm)

abbrev patternOptionValue (result : Option Pattern) : Atom :=
  encoded (MatchAutomataBindingExecution.patternOptionTerm result)
abbrev valueOptionValue (result : Option ContextualValue) : Atom :=
  encoded (RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm result)
abbrev typeOptionValue (result : Option TypeExpr) : Atom :=
  encoded (encodeOption InferenceCettaWire.AuthoredRule.typeTerm result)
abbrev valueValue (value : ContextualValue) : Atom := encoded (contextualValueTerm value)
abbrev specValue (spec : RuleBindingSpec) : Atom := encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)
abbrev siteValue (site : RulePatternSite) : Atom := encoded (InferenceCettaWire.AuthoredRule.siteTerm site)
abbrev pathValue (path : List Nat) : Atom := encoded (InferenceCettaWire.encodeList Term.natural path)

private theorem raw_admitted (program : SpaceSemantics.Program) (head : String) (arguments : List Atom)
    (checked : (List.range arguments.length).all (fun index => argumentIsRaw program head index) = true) :
    ∀ offset argument, arguments[offset]? = some argument →
      argumentIsRaw program head offset = true ∨ passiveArgument argument = true := by
  intro offset argument selected
  obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp selected
  exact Or.inl (List.all_eq_true.mp checked offset (List.mem_range.mpr bounded))

theorem binding_returns (caller : Subst) (state : State) (name : String) (assignment : Assignment)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [stringValue name, assignmentValue assignment]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:automata:binding" [one, two]) state
      (valueOptionValue (ScopedRuleMatching.lookup assignment name)) := by
  let aliases : Subst := [("name", stringValue name), ("assignment", assignmentValue assignment)]
  have base : PureReturns RuleExecutionProgram.program aliases state
      (a "gslt:automata:binding" [v "name", v "assignment"]) state
      (valueOptionValue (ScopedRuleMatching.lookup assignment name)) := by
    apply RuleExecutionProgram.automata_captured_returns (by decide +kernel)
    simpa only [RuleInstantiationExecution.ScopedCapture.scoped_lookup_wire,
      valueOptionValue, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm] using
      MatchAutomataBindingExecution.payload_binding_captured_returns aliases state name
        (assignment.map fun entry => (entry.1, contextualValueTerm entry.2)) [v "name", v "assignment"]
        (by simp [aliases, assignmentValue,
          RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm, applySubst, Subst.lookup])
  have transported : PureReturns RuleExecutionProgram.scopedMachineProgram aliases state
      (a "gslt:automata:binding" [v "name", v "assignment"]) state
      (valueOptionValue (ScopedRuleMatching.lookup assignment name)) :=
    path_of_closed_agreement rule_closed rule_agreement
      ⟨by change codeWithin ruleHeads (a "gslt:automata:binding" [v "name", v "assignment"]) = true; decide, rfl⟩ base
  apply captured_call_returns RuleExecutionProgram.scopedMachineProgram aliases caller state state "gslt:automata:binding"
    [v "name", v "assignment"] [one, two] _ (by decide +kernel) (by decide)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · simpa [aliases, applySubst, Subst.lookup] using captured.symm
  · exact transported

theorem instantiate_value_returns (caller : Subst) (state : State) (value : ContextualValue)
    (ambient depth : Nat) (arguments : List Pattern) (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [valueValue value, number ambient, number depth, patternsValue arguments]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state
      (a "gslt:rule:scope-instantiate-value" [one, two, three, four]) state
      (patternOptionValue (RuleBinding.instantiateValue? value ambient depth arguments)) := by
  let aliases : Subst := [("value", valueValue value), ("ambient", number ambient),
    ("depth", number depth), ("arguments", patternsValue arguments)]
  apply captured_call_in_extension rule_closed rule_agreement caller aliases state state
    "gslt:rule:scope-instantiate-value" [one, two, three, four] ["value", "ambient", "depth", "arguments"] _
    (by decide) (by decide) (by decide +kernel) (by decide)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · simpa [aliases, applySubst, Subst.lookup] using captured
  · exact RuleInstantiationExecution.ScopedCapture.instantiate_value_captured_returns caller state
      value ambient depth arguments one two three four captured

theorem fresh_returns (caller : Subst) (state : State) (name : String) (pattern : Pattern) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [stringValue name, patternValue pattern]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:fresh" [one, two]) state
      (Effects.boolean (Substitution.isFresh name pattern)) := by
  let aliases : Subst := [("name", stringValue name), ("pattern", patternValue pattern)]
  apply captured_call_in_extension rule_closed rule_agreement caller aliases state state
    "gslt:premise:fresh" [one, two] ["name", "pattern"] _
    (by decide) (by decide) (by decide +kernel) (by decide)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · simpa [aliases, applySubst, Subst.lookup] using captured
  · exact PremiseOperationsExecution.fresh_captured_returns caller state name pattern one two captured

theorem source_type_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rule : RewriteRule) (source : Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm language.terms), ruleValue rule, patternValue source]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:source-type" [one, two, three]) state
      (typeOptionValue (GeneralPremise.sourceType? language rule source)) := by
  let aliases : Subst := [("declarations", encoded (DeclarationTyping.declarationsTerm language.terms)),
    ("rule", ruleValue rule), ("source", patternValue source)]
  have base := source_type_captured_returns aliases state language rule source
    (v "declarations") (v "rule") (v "source") (by simp [aliases, DeclarationTyping.declarationsTerm, applySubst, Subst.lookup])
  have elevated : PureReturns premiseRuntimeProgram aliases state
      (a "gslt:premise:source-type" [v "declarations", v "rule", v "source"]) state
      (typeOptionValue (GeneralPremise.sourceType? language rule source)) :=
    premise_previous_returns (by decide +kernel) base
  have transported : PureReturns RuleExecutionProgram.scopedMachineProgram aliases state
      (a "gslt:premise:source-type" [v "declarations", v "rule", v "source"]) state
      (typeOptionValue (GeneralPremise.sourceType? language rule source)) :=
    path_of_closed_agreement sourceType_closed sourceType_agreement
      ⟨by change codeWithin sourceTypeHeads (a "gslt:premise:source-type" [v "declarations", v "rule", v "source"]) = true; decide, rfl⟩ elevated
  apply captured_call_returns RuleExecutionProgram.scopedMachineProgram aliases caller state state "gslt:premise:source-type"
    [v "declarations", v "rule", v "source"] [one, two, three] _ (by decide +kernel) (by decide)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · simpa [aliases, applySubst, Subst.lookup] using captured.symm
  · exact transported

theorem instantiate_returns (caller : Subst) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      ScopedInstantiationExecution.instantiationValues (.symbol "None") rule spec ambient site path depth assignment pattern) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-instantiate-at" arguments) state
      (patternOptionValue (ScopedRuleMatching.instantiateAt? rule spec ambient site path depth assignment pattern)) := by
  let aliases : Subst := [("operation", .symbol "None"), ("rule", ruleValue rule), ("spec", specValue spec),
    ("ambient", number ambient), ("site", siteValue site), ("path", pathValue path), ("depth", number depth),
    ("assignment", assignmentValue assignment), ("pattern", patternValue pattern)]
  have length : arguments.length = 9 := by
    have sized := congrArg List.length captured
    simpa only [List.length_map, ScopedInstantiationExecution.instantiationValues,
      List.length_cons, List.length_nil] using sized
  apply captured_call_in_extension ScopedInstantiationExecution.runtime_closed ScopedInstantiationExecution.scoped_machine_agreement
    caller aliases state state "gslt:rule:scope-instantiate-at" arguments
    ["operation", "rule", "spec", "ambient", "site", "path", "depth", "assignment", "pattern"] _
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
  · exact raw_admitted _ _ _ (by rw [length]; decide +kernel)
  · change arguments.map (applySubst caller) =
      [.symbol "None", ruleValue rule, specValue spec, number ambient, siteValue site, pathValue path,
        number depth, assignmentValue assignment, patternValue pattern] at captured
    simpa [aliases, applySubst, Subst.lookup] using captured
  · exact ScopedInstantiationExecution.instantiate_ordinary_captured_returns caller state rule spec ambient site path
      depth assignment pattern arguments captured

theorem length_encoded_returns {α : Type} (encoder : α → Term) (caller : Subst) (state : State)
    (values : List α) (input : Atom)
    (captured : applySubst caller input = encoded (encodeList encoder values)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:automata:length" [input]) state (number values.length) := by
  simpa only [List.length_map] using MatcherFrames.Mechanical.length_returns caller state
    (values.map encoder) input (by simpa only [MatcherFrames.termListValue, encodeList_map, Function.id_comp] using captured)

theorem append_encoded_returns {α : Type} (encoder : α → Term) (caller : Subst) (state : State)
    (left right : List α) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [encoded (encodeList encoder left), encoded (encodeList encoder right)]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:automata:append" [one, two]) state
      (encoded (encodeList encoder (left ++ right))) := by
  simpa only [MatcherFrames.termListValue, encodeList_map, Function.id_comp, ← List.map_append] using MatcherFrames.Mechanical.append_returns
    caller state (left.map encoder) (right.map encoder) one two
    (by simpa only [MatcherFrames.termListValue, encodeList_map, Function.id_comp] using captured)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval

abbrev nameOptionValue (result : Option String) : Atom := encoded (PremiseOperationsExecution.nameOptionTerm result)

def freshnessAmbientCaller (environment : Environment) (outer : Execution.Goal) (context : Context)
    (condition : FreshnessCondition) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  ("ambient", number context.bound.length) :: freshnessCaller environment outer context condition initial tail free

theorem freshness_stored_returns (state : State) (environment : Environment) (outer : Execution.Goal)
    (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (free : List (String × TypeExpr)) (value : ContextualValue) :
    PureReturns RuleExecutionProgram.scopedMachineProgram
      (("stored", Lower.valueValue value) :: freshnessAmbientCaller environment outer context condition initial tail free)
      state freshnessStoredBody state
      (nameOptionValue (match RuleBinding.instantiateValue? value context.bound.length 0 [] with
        | some (.fvar atom) => some atom | _ => none)) := by
  let caller := ("stored", Lower.valueValue value) :: freshnessAmbientCaller environment outer context condition initial tail free
  unfold freshnessStoredBody
  have projection := Lower.instantiate_value_returns caller state value context.bound.length 0 []
    (v "stored") (v "ambient") (number 0) (.symbol "LNil") (by
      simp [caller, freshnessAmbientCaller, freshnessCaller, premiseContextCaller, premiseGoalCaller, goalCaller,
        environmentCaller, callee, Helper.names, patternsValue,
        InferenceCettaWire.encodePatterns, applySubst, Subst.lookup, CettaWireAtom.encode])
  cases interpreted : RuleBinding.instantiateValue? value context.bound.length 0 [] with
  | none =>
      let selected := ("nonName", .symbol "None") :: caller
      apply branch_returns RuleExecutionProgram.scopedMachineProgram caller selected state _ (.symbol "None")
        freshnessResolvedCases (.symbol "None") _
      · simpa [interpreted, Lower.patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
          CettaWireAtom.encode] using projection
      · simp [freshnessResolvedCases, selected, caller, freshnessAmbientCaller, freshnessCaller,
          premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · simpa [nameOptionValue, PremiseOperationsExecution.nameOptionTerm, CettaWireAtom.encode] using
          symbol_returns RuleExecutionProgram.scopedMachineProgram selected state "None"
  | some pattern =>
      by_cases named : ∃ atom, pattern = .fvar atom
      · obtain ⟨atom, rfl⟩ := named
        let selected := ("atom", stringValue atom) :: caller
        apply branch_returns RuleExecutionProgram.scopedMachineProgram caller selected state _ (Lower.patternOptionValue (some (.fvar atom)))
          freshnessResolvedCases (a "Some" [v "atom"]) _
        · simpa only [interpreted] using projection
        · simp [freshnessResolvedCases, Lower.patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
            InferenceCettaWire.encodePattern, selected, caller, freshnessAmbientCaller, freshnessCaller,
            premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
        · simpa [nameOptionValue, PremiseOperationsExecution.nameOptionTerm, selected, a, v, encoded,
            applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return RuleExecutionProgram.scopedMachineProgram selected state (a "Some" [v "atom"])
              (transition_data_template "Some" [v "atom"] (by decide) (by simp; exact .captured "atom"))
      · have unnamed : (match (generalizing := false) some pattern with
            | some (.fvar atom) => some atom | _ => none : Option String) = none := by
          cases pattern with
          | fvar atom => exact False.elim (named ⟨atom, rfl⟩)
          | _ => rfl
        rw [unnamed]
        let selected := ("nonName", Lower.patternOptionValue (some pattern)) :: caller
        apply branch_returns RuleExecutionProgram.scopedMachineProgram caller selected state _ (Lower.patternOptionValue (some pattern))
          freshnessResolvedCases (.symbol "None") _
        · simpa only [interpreted] using projection
        · cases pattern with
          | fvar atom => exact False.elim (named ⟨atom, rfl⟩)
          | _ =>
              simp [freshnessResolvedCases, Lower.patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
                InferenceCettaWire.encodePattern, selected, caller, freshnessAmbientCaller, freshnessCaller,
                premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
        · simpa [nameOptionValue, PremiseOperationsExecution.nameOptionTerm, CettaWireAtom.encode] using
            symbol_returns RuleExecutionProgram.scopedMachineProgram selected state "None"

theorem freshness_lookup_returns (state : State) (environment : Environment) (outer : Execution.Goal)
    (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (free : List (String × TypeExpr)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram (freshnessAmbientCaller environment outer context condition initial tail free)
      state freshnessLookupBody state
      (nameOptionValue (GeneralPremise.freshnessName? context.bound.length initial condition.varName)) := by
  let caller := freshnessAmbientCaller environment outer context condition initial tail free
  unfold freshnessLookupBody
  have foundReturned := Lower.binding_returns caller state condition.varName initial (v "name") (v "initial")
    (by simp [caller, freshnessAmbientCaller, freshnessCaller, premiseContextCaller, premiseGoalCaller,
      goalCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
  cases found : ScopedRuleMatching.lookup initial condition.varName with
  | none =>
      apply branch_returns RuleExecutionProgram.scopedMachineProgram caller caller state _ (.symbol "None")
        freshnessLookupCases (a "Some" [v "name"]) _
      · simpa [found, Lower.valueOptionValue, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using foundReturned
      · simp [freshnessLookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [GeneralPremise.freshnessName?, found, nameOptionValue, PremiseOperationsExecution.nameOptionTerm,
          caller, freshnessAmbientCaller, freshnessCaller, premiseContextCaller, premiseGoalCaller, goalCaller,
          environmentCaller, callee, Helper.names, a, v, encoded, applySubst, applySubst.applySubstList,
          Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return RuleExecutionProgram.scopedMachineProgram caller state (a "Some" [v "name"])
            (transition_data_template "Some" [v "name"] (by decide) (by simp; exact .captured "name"))
  | some value =>
      let selected := ("stored", Lower.valueValue value) :: caller
      apply branch_returns RuleExecutionProgram.scopedMachineProgram caller selected state _ (Lower.valueOptionValue (some value))
        freshnessLookupCases freshnessStoredBody _
      · simpa only [found] using foundReturned
      · simp [freshnessLookupCases, Lower.valueOptionValue, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, selected, caller, freshnessAmbientCaller, freshnessCaller,
          premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · have returned := freshness_stored_returns state environment outer context condition initial tail free value
        cases interpreted : RuleBinding.instantiateValue? value context.bound.length 0 [] with
        | none =>
            simpa only [GeneralPremise.freshnessName?, found, selected, caller, interpreted] using returned
        | some pattern =>
            cases pattern <;>
              simpa only [GeneralPremise.freshnessName?, found, selected, caller, interpreted] using returned


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval

theorem evaluate_freshness_returns (state : State) (environment : Environment) (outer : Execution.Goal)
    (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (free : List (String × TypeExpr)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.premise context (.freshness condition) initial), continuationValue tail])
      state (expansionValue (Execution.evaluate environment outer (.premise context (.freshness condition) initial) tail)) := by
  let caller := freshnessCaller environment outer context condition initial tail free
  let ambientCaller := freshnessAmbientCaller environment outer context condition initial tail free
  let nameCaller := ("nameOption", nameOptionValue
    (GeneralPremise.freshnessName? context.bound.length initial condition.varName)) :: ambientCaller
  apply freshness_body_returns state environment outer context condition initial tail free
  rw [freshness_shape]
  apply named_let_returns RuleExecutionProgram.scopedMachineProgram caller state "ambient" _ (number context.bound.length) _ _
  · simp [caller, freshnessCaller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller,
      callee, Helper.names, Subst.lookup]
  · exact Lower.length_encoded_returns InferenceCettaWire.AuthoredRule.typeTerm caller state context.bound
      (v "bound") (by simp [caller, freshnessCaller, premiseContextCaller, premiseGoalCaller, goalCaller,
        environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
  · apply named_let_returns RuleExecutionProgram.scopedMachineProgram ambientCaller state "nameOption" _
      (nameOptionValue (GeneralPremise.freshnessName? context.bound.length initial condition.varName)) freshnessNameBody _
    · simp [ambientCaller, freshnessAmbientCaller, freshnessCaller, premiseContextCaller, premiseGoalCaller,
        goalCaller, environmentCaller, callee, Helper.names, Subst.lookup]
    · exact freshness_lookup_returns state environment outer context condition initial tail free
    · unfold freshnessNameBody
      cases named : GeneralPremise.freshnessName? context.bound.length initial condition.varName with
      | none =>
          have callerEq : ("nameOption", nameOptionValue none) :: ambientCaller = nameCaller := by
            simp [nameCaller, named]
          rw [callerEq]
          apply branch_returns RuleExecutionProgram.scopedMachineProgram nameCaller nameCaller state _ (.symbol "None")
            freshnessNameCases freshnessProjectionData _
          · simpa [nameCaller, named, nameOptionValue, PremiseOperationsExecution.nameOptionTerm,
              applySubst, Subst.lookup, CettaWireAtom.encode] using variable_returns RuleExecutionProgram.scopedMachineProgram nameCaller state "nameOption"
          · simp [freshnessNameCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
          · have read : GeneralPremise.freshnessSubject? context.rule context.spec context.bound context.premiseIndex
                context.quantifierDepth initial condition = none := by
              simp [GeneralPremise.freshnessSubject?, named]
            unfold expansionValue
            rw [evaluate_freshness_none_eq environment outer context condition initial tail read]
            simpa [freshnessProjectionData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, obligationTerm, nameCaller, ambientCaller, freshnessAmbientCaller,
              caller, freshnessCaller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
              encodeOption, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
              CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return RuleExecutionProgram.scopedMachineProgram nameCaller state freshnessProjectionData freshness_projection_template
      | some atom =>
          have callerEq : ("nameOption", nameOptionValue (some atom)) :: ambientCaller = nameCaller := by
            simp [nameCaller, named]
          rw [callerEq]
          let atomCaller := ("atom", stringValue atom) :: nameCaller
          apply branch_returns RuleExecutionProgram.scopedMachineProgram nameCaller atomCaller state _ (nameOptionValue (some atom))
            freshnessNameCases freshnessSubjectBody _
          · simpa [nameCaller, named, applySubst, Subst.lookup] using
              variable_returns RuleExecutionProgram.scopedMachineProgram nameCaller state "nameOption"
          · simp [freshnessNameCases, nameOptionValue, PremiseOperationsExecution.nameOptionTerm, atomCaller,
              nameCaller, ambientCaller, freshnessAmbientCaller, freshnessCaller, premiseContextCaller,
              premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
          · unfold freshnessSubjectBody ordinaryInstantiation
            have projection := Lower.instantiate_returns atomCaller state context.rule context.spec context.bound.length
              (context.site 0) [] 0 initial condition.term
              [.symbol "None", v "rule", v "spec", v "ambient",
                a "RulePremise" [v "premiseIndex", v "quantifiers", number 0], .symbol "LNil", number 0,
                v "initial", v "subjectSchema"] (by
                  change _ = [.symbol "None", ruleValue context.rule, Lower.specValue context.spec, number context.bound.length,
                    Lower.siteValue (context.site 0), .symbol "LNil", number 0, assignmentValue initial, patternValue condition.term]
                  simp [atomCaller, nameCaller, ambientCaller, freshnessAmbientCaller, freshnessCaller,
                    premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
                    Context.site, Lower.siteValue, InferenceCettaWire.AuthoredRule.siteTerm,
                    a, v, encoded, number, applySubst, applySubst.applySubstList, Subst.lookup,
                    CettaWireAtom.encode, CettaWireAtom.encodeMany])
            cases interpreted : ScopedRuleMatching.instantiateAt? context.rule context.spec context.bound.length
                (context.site 0) [] 0 initial condition.term with
            | none =>
                apply branch_returns RuleExecutionProgram.scopedMachineProgram atomCaller atomCaller state _ (.symbol "None")
                  freshnessSubjectCases freshnessProjectionData _
                · simpa [interpreted, Lower.patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
                    CettaWireAtom.encode] using projection
                · simp [freshnessSubjectCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                · have read : GeneralPremise.freshnessSubject? context.rule context.spec context.bound context.premiseIndex
                      context.quantifierDepth initial condition = none := by
                    have projected := interpreted
                    simp only [Context.site] at projected
                    simp [GeneralPremise.freshnessSubject?, named, projected]
                  unfold expansionValue
                  rw [evaluate_freshness_none_eq environment outer context condition initial tail read]
                  simpa [freshnessProjectionData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, obligationTerm, atomCaller, nameCaller, ambientCaller,
                    freshnessAmbientCaller, caller, freshnessCaller, premiseContextCaller, premiseGoalCaller, goalCaller,
                    environmentCaller, callee, Helper.names, encodeOption, encodeList, applySubst,
                    applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                    PureData.template_return RuleExecutionProgram.scopedMachineProgram atomCaller state freshnessProjectionData freshness_projection_template
            | some subject =>
                let final := ("subject", patternValue subject) :: atomCaller
                have read : GeneralPremise.freshnessSubject? context.rule context.spec context.bound context.premiseIndex
                    context.quantifierDepth initial condition = some (atom, subject) := by
                  have projected := interpreted
                  simp only [Context.site] at projected
                  simp [GeneralPremise.freshnessSubject?, named, projected]
                apply branch_returns RuleExecutionProgram.scopedMachineProgram atomCaller final state _ (Lower.patternOptionValue (some subject))
                  freshnessSubjectCases freshnessCheckedBody _
                · simpa only [interpreted] using projection
                · simp [freshnessSubjectCases, Lower.patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
                    final, atomCaller, nameCaller, ambientCaller, freshnessAmbientCaller, freshnessCaller,
                    premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
                    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                    matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
                · unfold freshnessCheckedBody
                  apply bool_if_returns RuleExecutionProgram.scopedMachineProgram final state _ (Substitution.isFresh atom subject) freshnessData emptyData _
                  · exact Lower.fresh_returns final state atom subject (v "atom") (v "subject")
                      (by simp [final, atomCaller, nameCaller, applySubst, Subst.lookup])
                  · cases checked : Substitution.isFresh atom subject with
                    | false =>
                        simp only [Bool.false_eq_true, ite_false]
                        unfold expansionValue
                        rw [evaluate_freshness_false_eq environment outer context condition initial atom subject tail read checked]
                        simpa [emptyData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, encodeOption, encodeList, a, v, encoded,
                          applySubst, applySubst.applySubstList, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                          PureData.template_return RuleExecutionProgram.scopedMachineProgram final state emptyData empty_template
                    | true =>
                        simp only [ite_true]
                        unfold expansionValue
                        rw [evaluate_freshness_true_eq environment outer context condition initial atom subject tail read checked]
                        simpa [freshnessData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, taskTerm, resultTerm, goalTerm, eventTerm,
                          final, atomCaller, nameCaller, ambientCaller, freshnessAmbientCaller, caller, freshnessCaller,
                          premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
                          goalValue, continuationValue, patternValue, QueryExecution.patternValue,
                          assignmentValue, QueryExecution.assignmentValue, encoded, QueryExecution.encoded, encodeOption, encodeList,
                          applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                          PureData.template_return RuleExecutionProgram.scopedMachineProgram final state freshnessData freshness_template


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program)
open Effects (State)
open Eval

theorem evaluate_congruence_returns (state : State) (environment : Environment) (outer : Execution.Goal)
    (context : Context) (source target : Pattern) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.congruence source target) initial) outer)
    (free : List (String × TypeExpr)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.premise context (.congruence source target) initial), continuationValue tail])
      state (expansionValue (Execution.evaluate environment outer (.premise context (.congruence source target) initial) tail)) := by
  let caller := congruenceCaller environment outer context source target initial tail free
  apply congruence_body_returns state environment outer context source target initial tail free
  rw [congruence_shape]
  have typedReturned := Lower.source_type_returns caller state environment.language context.rule source
    (v "declarations") (v "rule") (v "sourceSchema") (by
      simp [caller, congruenceCaller, premiseContextCaller, premiseGoalCaller, goalCaller,
        environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
  cases typed : GeneralPremise.sourceType? environment.language context.rule source with
  | none =>
      apply branch_returns RuleExecutionProgram.scopedMachineProgram caller caller state _ (.symbol "None") congruenceTypeCases stepSortData _
      · simpa [typed, Lower.typeOptionValue, encodeOption, CettaWireAtom.encode] using typedReturned
      · simp [congruenceTypeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · unfold expansionValue
        rw [evaluate_congruence_sort_none_eq environment outer context source target initial tail typed]
        simpa [stepSortData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, obligationTerm, caller, congruenceCaller,
          premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
          encodeOption, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return RuleExecutionProgram.scopedMachineProgram caller state stepSortData step_sort_template
  | some type =>
      let selected := ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm type)) :: caller
      let ambientCaller := ("ambient", number context.bound.length) :: selected
      apply branch_returns RuleExecutionProgram.scopedMachineProgram caller selected state _ (Lower.typeOptionValue (some type))
        congruenceTypeCases congruenceTypeBody _
      · simpa only [typed] using typedReturned
      · simp [congruenceTypeCases, Lower.typeOptionValue, encodeOption, selected,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup,
          caller, congruenceCaller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names]
      · unfold congruenceTypeBody
        apply named_let_returns RuleExecutionProgram.scopedMachineProgram selected state "ambient" _ (number context.bound.length)
          (childProjectionBody (number 0) (v "bound") (.symbol "LNil")) _
        · simp [selected, caller, congruenceCaller, premiseContextCaller, premiseGoalCaller, goalCaller,
            environmentCaller, callee, Helper.names, Subst.lookup]
        · exact Lower.length_encoded_returns InferenceCettaWire.AuthoredRule.typeTerm selected state
            context.bound (v "bound") (by simp [selected, caller, congruenceCaller, premiseContextCaller,
              premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
        · unfold childProjectionBody ordinaryInstantiation
          have projection := Lower.instantiate_returns ambientCaller state context.rule context.spec context.bound.length
            (context.site 0) [] 0 initial source
            [.symbol "None", v "rule", v "spec", v "ambient",
              a "RulePremise" [v "premiseIndex", v "quantifiers", number 0], .symbol "LNil", number 0,
              v "initial", v "sourceSchema"] (by
                change _ = [.symbol "None", ruleValue context.rule, Lower.specValue context.spec, number context.bound.length,
                  Lower.siteValue (context.site 0), .symbol "LNil", number 0, assignmentValue initial, patternValue source]
                simp [ambientCaller, selected, caller, congruenceCaller, premiseContextCaller, premiseGoalCaller,
                  goalCaller, environmentCaller, callee, Helper.names, Context.site, Lower.siteValue,
                  InferenceCettaWire.AuthoredRule.siteTerm, a, v, encoded, number, applySubst,
                  applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany])
          cases interpreted : ScopedRuleMatching.instantiateAt? context.rule context.spec context.bound.length
              (context.site 0) [] 0 initial source with
          | none =>
              apply branch_returns RuleExecutionProgram.scopedMachineProgram ambientCaller ambientCaller state _ (.symbol "None")
                (childProjectionCases (v "bound") (.symbol "LNil")) stepProjectionData _
              · simpa [interpreted, Lower.patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
                  CettaWireAtom.encode] using projection
              · simp [childProjectionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · unfold expansionValue
                rw [evaluate_congruence_projection_none_eq environment outer context source target initial type tail typed interpreted]
                simpa [stepProjectionData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, obligationTerm, ambientCaller, selected, caller,
                  congruenceCaller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
                  encodeOption, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return RuleExecutionProgram.scopedMachineProgram ambientCaller state stepProjectionData step_projection_template
          | some actualSource =>
              let final := ("actualSource", patternValue actualSource) :: ambientCaller
              apply branch_returns RuleExecutionProgram.scopedMachineProgram ambientCaller final state _ (Lower.patternOptionValue (some actualSource))
                (childProjectionCases (v "bound") (.symbol "LNil")) (childData (v "bound") (.symbol "LNil")) _
              · simpa only [interpreted] using projection
              · simp [childProjectionCases, Lower.patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
                  final, ambientCaller, selected, caller, congruenceCaller, premiseContextCaller, premiseGoalCaller,
                  goalCaller, environmentCaller, callee, Helper.names,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
              · unfold expansionValue
                rw [evaluate_congruence_some_eq environment outer context source target actualSource initial type tail typed interpreted]
                simpa [childData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, taskTerm, goalTerm, continuationTerm, stepCallTerm,
                  final, ambientCaller, selected, caller, congruenceCaller, premiseContextCaller, premiseGoalCaller,
                  goalCaller, environmentCaller, callee, Helper.names, contextValue, QueryExecution.contextValue,
                  assignmentValue, QueryExecution.assignmentValue, boundValue, QueryExecution.boundValue,
                  InferenceCettaWire.encodeList, encodeOption, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return RuleExecutionProgram.scopedMachineProgram final state (childData (v "bound") (.symbol "LNil"))
                    (child_template _ _ (.captured "bound") (.symbol "LNil"))

theorem evaluate_scoped_step_returns (state : State) (environment : Environment) (outer : Execution.Goal)
    (context : Context) (step : ScopedStepPremise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.scopedStep step) initial) outer)
    (free : List (String × TypeExpr)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.premise context (.scopedStep step) initial), continuationValue tail])
      state (expansionValue (Execution.evaluate environment outer (.premise context (.scopedStep step) initial) tail)) := by
  let caller := scopedStepCaller environment outer context step initial tail free
  let ambientCaller := ("ambient", number context.bound.length) :: caller
  let depthCaller := ("depth", number step.binders.length) :: ambientCaller
  let boundCaller := ("effectiveBound", boundValue (step.binders ++ context.bound)) :: depthCaller
  apply scoped_step_body_returns state environment outer context step initial tail free
  rw [scoped_step_shape]
  apply let_star_returns RuleExecutionProgram.scopedMachineProgram caller state state scopedStepPairs _ scopedStepNested _ scoped_step_nested
  unfold scopedStepNested
  apply named_let_returns RuleExecutionProgram.scopedMachineProgram caller state "ambient" _ (number context.bound.length) _ _
  · simp [caller, scopedStepCaller, premiseContextCaller, premiseGoalCaller, goalCaller,
      environmentCaller, callee, Helper.names, Subst.lookup]
  · exact Lower.length_encoded_returns InferenceCettaWire.AuthoredRule.typeTerm caller state context.bound
      (v "bound") (by simp [caller, scopedStepCaller, premiseContextCaller, premiseGoalCaller, goalCaller,
        environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
  · apply named_let_returns RuleExecutionProgram.scopedMachineProgram ambientCaller state "depth" _ (number step.binders.length) _ _
    · simp [ambientCaller, caller, scopedStepCaller, premiseContextCaller, premiseGoalCaller, goalCaller,
        environmentCaller, callee, Helper.names, Subst.lookup]
    · exact Lower.length_encoded_returns InferenceCettaWire.AuthoredRule.typeTerm ambientCaller state step.binders
        (v "binders") (by simp [ambientCaller, caller, scopedStepCaller, premiseContextCaller, premiseGoalCaller,
          goalCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
    · apply named_let_returns RuleExecutionProgram.scopedMachineProgram depthCaller state "effectiveBound" _
        (boundValue (step.binders ++ context.bound)) _ _
      · simp [depthCaller, ambientCaller, caller, scopedStepCaller, premiseContextCaller, premiseGoalCaller,
          goalCaller, environmentCaller, callee, Helper.names, Subst.lookup]
      · exact Lower.append_encoded_returns InferenceCettaWire.AuthoredRule.typeTerm depthCaller state step.binders
          context.bound (v "binders") (v "bound") (by simp [depthCaller, ambientCaller, caller,
            scopedStepCaller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
            applySubst, Subst.lookup])
      · unfold childProjectionBody ordinaryInstantiation
        have projection := Lower.instantiate_returns boundCaller state context.rule context.spec context.bound.length
          (context.site 0) [] step.binders.length initial step.source
          [.symbol "None", v "rule", v "spec", v "ambient",
            a "RulePremise" [v "premiseIndex", v "quantifiers", number 0], .symbol "LNil", v "depth",
            v "initial", v "sourceSchema"] (by
              change _ = [.symbol "None", ruleValue context.rule, Lower.specValue context.spec, number context.bound.length,
                Lower.siteValue (context.site 0), .symbol "LNil", number step.binders.length,
                assignmentValue initial, patternValue step.source]
              simp [boundCaller, depthCaller, ambientCaller, caller, scopedStepCaller, premiseContextCaller,
                premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names, Context.site, Lower.siteValue,
                InferenceCettaWire.AuthoredRule.siteTerm, a, v, encoded, number, applySubst,
                applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany])
        cases interpreted : ScopedRuleMatching.instantiateAt? context.rule context.spec context.bound.length
            (context.site 0) [] step.binders.length initial step.source with
        | none =>
            apply branch_returns RuleExecutionProgram.scopedMachineProgram boundCaller boundCaller state _ (.symbol "None")
              (childProjectionCases (v "effectiveBound") (v "binders")) stepProjectionData _
            · simpa [interpreted, Lower.patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
                CettaWireAtom.encode] using projection
            · simp [childProjectionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · unfold expansionValue
              rw [evaluate_scoped_step_none_eq environment outer context step initial tail interpreted]
              simpa [stepProjectionData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, obligationTerm, boundCaller, depthCaller, ambientCaller, caller,
                scopedStepCaller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
                encodeOption, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
                CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                PureData.template_return RuleExecutionProgram.scopedMachineProgram boundCaller state stepProjectionData step_projection_template
        | some actualSource =>
            let final := ("actualSource", patternValue actualSource) :: boundCaller
            apply branch_returns RuleExecutionProgram.scopedMachineProgram boundCaller final state _ (Lower.patternOptionValue (some actualSource))
              (childProjectionCases (v "effectiveBound") (v "binders")) (childData (v "effectiveBound") (v "binders")) _
            · simpa only [interpreted] using projection
            · simp [childProjectionCases, Lower.patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
                final, boundCaller, depthCaller, ambientCaller, caller, scopedStepCaller, premiseContextCaller,
                premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
            · unfold expansionValue
              rw [evaluate_scoped_step_some_eq environment outer context step actualSource initial tail interpreted]
              simpa [childData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, taskTerm, goalTerm, continuationTerm, stepCallTerm,
                final, boundCaller, depthCaller, ambientCaller, caller, scopedStepCaller, premiseContextCaller,
                premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
                contextValue, QueryExecution.contextValue, assignmentValue, QueryExecution.assignmentValue,
                boundValue, QueryExecution.boundValue, InferenceCettaWire.encodeList, encodeOption, encodeList,
                applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                PureData.template_return RuleExecutionProgram.scopedMachineProgram final state (childData (v "effectiveBound") (v "binders"))
                  (child_template _ _ (.captured "effectiveBound") (.captured "binders"))


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval

theorem evaluate_freshness_captured_returns (caller : Subst) (state : State) (environment : Environment)
    (outer : Execution.Goal) (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (free : List (String × TypeExpr)) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment free, goalValue (.premise context (.freshness condition) initial), continuationValue tail]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a Helper.evaluate.head [one, two, three]) state
      (expansionValue (Execution.evaluate environment outer (.premise context (.freshness condition) initial) tail)) :=
  helper_capture RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement .evaluate caller state [one, two, three]
    [environmentValue environment free, goalValue (.premise context (.freshness condition) initial), continuationValue tail] _
    rfl captured (evaluate_freshness_returns state environment outer context condition initial tail free)

theorem evaluate_freshness_captured_completed_iff (caller : Subst) (state : State) (environment : Environment)
    (outer : Execution.Goal) (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.freshness condition) initial) outer)
    (free : List (String × TypeExpr)) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment free, goalValue (.premise context (.freshness condition) initial), continuationValue tail])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run RuleExecutionProgram.scopedMachineProgram fuel {state, control := .evaluate caller (a Helper.evaluate.head [one, two, three])} =
      .complete after answers input output) ↔
      after = state ∧ answers = [expansionValue (Execution.evaluate environment outer (.premise context (.freshness condition) initial) tail)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff RuleExecutionProgram.scopedMachineProgram caller state state _ _
    (evaluate_freshness_captured_returns caller state environment outer context condition initial tail free one two three captured)
    after answers input output


theorem evaluate_congruence_captured_returns (caller : Subst) (state : State) (environment : Environment)
    (outer : Execution.Goal) (context : Context) (source target : Pattern) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.congruence source target) initial) outer)
    (free : List (String × TypeExpr)) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment free, goalValue (.premise context (.congruence source target) initial), continuationValue tail]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a Helper.evaluate.head [one, two, three]) state
      (expansionValue (Execution.evaluate environment outer (.premise context (.congruence source target) initial) tail)) :=
  helper_capture RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement .evaluate caller state [one, two, three]
    [environmentValue environment free, goalValue (.premise context (.congruence source target) initial), continuationValue tail] _
    rfl captured (evaluate_congruence_returns state environment outer context source target initial tail free)

theorem evaluate_congruence_captured_completed_iff (caller : Subst) (state : State) (environment : Environment)
    (outer : Execution.Goal) (context : Context) (source target : Pattern) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.congruence source target) initial) outer)
    (free : List (String × TypeExpr)) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment free, goalValue (.premise context (.congruence source target) initial), continuationValue tail])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run RuleExecutionProgram.scopedMachineProgram fuel {state, control := .evaluate caller (a Helper.evaluate.head [one, two, three])} =
      .complete after answers input output) ↔
      after = state ∧ answers = [expansionValue (Execution.evaluate environment outer (.premise context (.congruence source target) initial) tail)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff RuleExecutionProgram.scopedMachineProgram caller state state _ _
    (evaluate_congruence_captured_returns caller state environment outer context source target initial tail free one two three captured)
    after answers input output


theorem evaluate_scoped_step_captured_returns (caller : Subst) (state : State) (environment : Environment)
    (outer : Execution.Goal) (context : Context) (step : ScopedStepPremise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.scopedStep step) initial) outer)
    (free : List (String × TypeExpr)) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment free, goalValue (.premise context (.scopedStep step) initial), continuationValue tail]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a Helper.evaluate.head [one, two, three]) state
      (expansionValue (Execution.evaluate environment outer (.premise context (.scopedStep step) initial) tail)) :=
  helper_capture RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement .evaluate caller state [one, two, three]
    [environmentValue environment free, goalValue (.premise context (.scopedStep step) initial), continuationValue tail] _
    rfl captured (evaluate_scoped_step_returns state environment outer context step initial tail free)

theorem evaluate_scoped_step_captured_completed_iff (caller : Subst) (state : State) (environment : Environment)
    (outer : Execution.Goal) (context : Context) (step : ScopedStepPremise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.scopedStep step) initial) outer)
    (free : List (String × TypeExpr)) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment free, goalValue (.premise context (.scopedStep step) initial), continuationValue tail])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run RuleExecutionProgram.scopedMachineProgram fuel {state, control := .evaluate caller (a Helper.evaluate.head [one, two, three])} =
      .complete after answers input output) ↔
      after = state ∧ answers = [expansionValue (Execution.evaluate environment outer (.premise context (.scopedStep step) initial) tail)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff RuleExecutionProgram.scopedMachineProgram caller state state _ _
    (evaluate_scoped_step_captured_returns caller state environment outer context step initial tail free one two three captured)
    after answers input output


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

def queryStartData : Atom := a "Some" [a "PremiseExpansion"
  [a "LCons" [a "PremiseQuery" [v "request", a "PremiseState"
    [a "LCons" [.symbol "PremiseQueryStart", .symbol "LNil"], .symbol "LNil", .symbol "LNil", number 0],
    number 0, v "continuation"], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]
def queryRequestData : Atom := a "PremiseQueryRequest" [v "context", v "relation", v "arguments", v "initial"]
theorem query_start_shape : premiseBody 0 = a "let" [v "request", queryRequestData, queryStartData] := by decide +kernel
theorem forall_shape : premiseBody 2 = a "gslt:premise:machine-evaluate"
    [v "declarations", v "free", v "goal", v "continuation"] := by decide +kernel

local macro "start_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)
theorem query_request_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) :
    PureData.Template program queryRequestData := by unfold queryRequestData; start_template (program) (agreement)
theorem query_start_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) :
    PureData.Template program queryStartData := by unfold queryStartData; start_template (program) (agreement)

theorem evaluate_query_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (context : Context)
    (relation : String) (arguments : List Pattern) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.relationQuery relation arguments) initial) outer)
    (free : List (String × TypeExpr)) :
    PureReturns program [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.premise context (.relationQuery relation arguments) initial),
        continuationValue tail]) state
      (expansionValue (Execution.evaluate environment outer (.premise context (.relationQuery relation arguments) initial) tail)) := by
  let caller := premiseContextCaller environment outer context (.relationQuery relation arguments) initial tail free
  let selected : Subst := [("arguments", patternsValue arguments), ("relation", stringValue relation)] ++ caller
  let request : Query.Request := ⟨context, relation, arguments, initial⟩
  let requested := ("request", encoded (queryRequestTerm request)) :: selected
  apply evaluate_premise_body_returns program agreement state environment outer context _ initial tail free
  rw [premise_context_shape]
  apply branch_returns program caller selected state _
    (encoded (InferenceCettaWire.AuthoredRule.premiseTerm (.relationQuery relation arguments)))
    premiseCases (premiseBody 0) _
  · simpa [caller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller,
      callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "premise"
  · simp [premise_cases, InferenceCettaWire.AuthoredRule.premiseTerm,
      selected, caller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, patternsValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [query_start_shape]
    apply named_let_returns program selected state "request" queryRequestData (encoded (queryRequestTerm request)) queryStartData _
    · simp [selected, caller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names, Subst.lookup]
    · simpa [queryRequestData, request, queryRequestTerm, selected, caller,
        premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
        patternsValue, QueryExecution.patternsValue, applySubst, applySubst.applySubstList,
        Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return program selected state _ (query_request_template program agreement)
    · simpa [queryStartData, expansionValue, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, Execution.evaluate, Execution.evaluatePremise,
        request, Query.start, queryStateTerm, PremiseSchedulerExecution.schedulerStateTerm, queryTaskTerm, taskTerm, encodeOption, encodeList,
        requested, selected, caller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return program requested state _ (query_start_template program agreement)

theorem evaluate_forall_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (premiseAgreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (context : Context)
    (collection parameter : String) (body : Premise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context (.forAll collection parameter body) initial) outer)
    (free : List (String × TypeExpr)) :
    PureReturns program [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.premise context (.forAll collection parameter body) initial),
        continuationValue tail]) state
      (expansionValue (Execution.evaluate environment outer (.premise context (.forAll collection parameter body) initial) tail)) := by
  let caller := premiseContextCaller environment outer context (.forAll collection parameter body) initial tail free
  let selected : Subst := [("body", encoded (InferenceCettaWire.AuthoredRule.premiseTerm body)),
    ("parameter", stringValue parameter), ("collection", stringValue collection)] ++ caller
  apply evaluate_premise_body_returns program agreement state environment outer context _ initial tail free
  rw [premise_context_shape]
  apply branch_returns program caller selected state _
    (encoded (InferenceCettaWire.AuthoredRule.premiseTerm (.forAll collection parameter body)))
    premiseCases (premiseBody 2) _
  · simpa [caller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller,
      callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "premise"
  · simp [premise_cases, InferenceCettaWire.AuthoredRule.premiseTerm,
      selected, caller, premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [forall_shape]
    exact Administration.forall_in_extension_returns program premiseAgreement selected state environment outer free
      context collection parameter body initial tail (v "declarations") (v "free") (v "goal") (v "continuation") (by
        simp [selected, caller, premiseContextCaller, premiseGoalCaller, goalCaller,
          environmentCaller, callee, Helper.names, applySubst, Subst.lookup])


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval

namespace Evaluation

theorem evaluate_within_returns (state : State) (environment : Environment) (outer goal : Execution.Goal)
    (tail : Execution.Continuation environment goal outer) (footprint : List String)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.goalFreeWithin footprint goal) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.evaluate.head
      [environmentValue environment (environment.free.entriesOn footprint), goalValue goal, continuationValue tail]) state
      (expansionValue (Execution.evaluate environment outer goal tail)) := by
  cases goal with
  | premise context premise initial =>
      cases premise with
      | relationQuery relation arguments =>
          exact PremiseTransitions.evaluate_query_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement state environment
            outer context relation arguments initial tail (environment.free.entriesOn footprint)
      | freshness condition =>
          exact PremiseTransitions.evaluate_freshness_returns state environment outer context condition initial tail
            (environment.free.entriesOn footprint)
      | forAll collection parameter body =>
          exact PremiseTransitions.evaluate_forall_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement
            AssembledLower.premise_agreement state environment outer context collection parameter body initial tail
            (environment.free.entriesOn footprint)
      | congruence source target =>
          exact PremiseTransitions.evaluate_congruence_returns state environment outer context source target initial tail
            (environment.free.entriesOn footprint)
      | scopedStep step =>
          exact PremiseTransitions.evaluate_scoped_step_returns state environment outer context step initial tail
            (environment.free.entriesOn footprint)
  | premises context premises initial =>
      exact Administration.evaluate_premises_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement
        AssembledLower.premise_agreement state environment outer context premises initial tail
        (environment.free.entriesOn footprint)
  | quantified context parameter body index elements initial =>
      exact Administration.evaluate_quantified_within_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement
        AssembledLower.premise_agreement state environment outer context parameter body index elements initial tail footprint covered.2
  | root bound type source index =>
      exact RootFrame.evaluate_root_within_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement
        AssembledLower.premise_agreement MatcherFrames.Checkers.operations AdmissionLower.Assembly.operations
        state environment outer bound type source index tail footprint covered
  | steps bound type source limit =>
      exact Administration.evaluate_steps_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement
        AssembledLower.premise_agreement state environment outer bound type source limit tail
        (environment.free.entriesOn footprint)

theorem evaluate_captured_within_returns (caller : Subst) (state : State) (environment : Environment)
    (outer goal : Execution.Goal) (tail : Execution.Continuation environment goal outer) (footprint : List String)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.goalFreeWithin footprint goal) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), goalValue goal, continuationValue tail]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a Helper.evaluate.head [one, two, three]) state
      (expansionValue (Execution.evaluate environment outer goal tail)) :=
  helper_capture RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement .evaluate caller state [one, two, three]
    [environmentValue environment (environment.free.entriesOn footprint), goalValue goal, continuationValue tail] _
    rfl captured (evaluate_within_returns state environment outer goal tail footprint covered)

theorem evaluate_captured_completed_iff (caller : Subst) (state : State) (environment : Environment)
    (outer goal : Execution.Goal) (tail : Execution.Continuation environment goal outer) (footprint : List String)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.goalFreeWithin footprint goal) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), goalValue goal, continuationValue tail])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run RuleExecutionProgram.scopedMachineProgram fuel {state, control := .evaluate caller (a Helper.evaluate.head [one, two, three])} =
      .complete after answers input output) ↔
      after = state ∧ answers = [expansionValue (Execution.evaluate environment outer goal tail)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff RuleExecutionProgram.scopedMachineProgram caller state state _ _
    (evaluate_captured_within_returns caller state environment outer goal tail footprint covered one two three captured)
    after answers input output


end Evaluation

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

namespace Delivery

def cases : SpaceSemantics.Cases := sourceCases (equation .deliver).body
def administrativeBody : Atom := a "gslt:premise:machine-deliver" [v "result", v "continuation"]
def rootBody : Atom := a MatcherFrames.Helper.body.head [v "environment", v "result", v "continuation"]
def steppedBody : Atom := a MatcherFrames.Helper.stepped.head [v "environment", v "result", v "continuation"]

theorem delivery_shape : (equation .deliver).body = caseData (v "continuation") cases := by decide +kernel
theorem delivery_cases : cases =
    [(a "PremiseRootBody" [v "bound", v "type", v "source", v "index", v "rule", v "spec", v "trace", v "captured", v "tail"], rootBody),
      (a "PremiseStepped" [v "call", v "tail"], steppedBody), (v "administrative", administrativeBody)] := by decide +kernel

def caller (environment : Environment) {goal outer : Execution.Goal}
    (result : Execution.Result environment goal) (tail : Execution.Continuation environment goal outer)
    (free : List (String × TypeExpr)) : Subst :=
  callee .deliver [environmentValue environment free, resultValue result, continuationValue tail]

theorem administrative_selected (environment : Environment) (goal outer : Execution.Goal)
    (result : Execution.Result environment goal) (tail : Execution.Continuation environment goal outer)
    (free : List (String × TypeExpr)) (supported : administrativeContinuation tail = true) :
    SpaceSemantics.selectCase (caller environment result tail free) (continuationValue tail) cases =
      some (("administrative", continuationValue tail) :: caller environment result tail free, administrativeBody) := by
  cases tail <;> simp only [administrativeContinuation, Bool.false_eq_true] at supported
  all_goals simp [delivery_cases, caller, continuationValue, continuationTerm, callee, Helper.names,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]

theorem delivered_administrative_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (premiseAgreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram program)
    (state : State) (environment : Environment) (goal outer : Execution.Goal)
    (result : Execution.Result environment goal) (tail : Execution.Continuation environment goal outer)
    (free : List (String × TypeExpr)) (supported : administrativeContinuation tail = true) :
    PureReturns program [] state (a Helper.deliver.head
      [environmentValue environment free, resultValue result, continuationValue tail]) state
      (expansionValue (Execution.delivered environment outer result tail)) := by
  let selected := ("administrative", continuationValue tail) :: caller environment result tail free
  apply helper_call program agreement .deliver [] state _ _ _ rfl (QueryExecution.captured_closed _)
  rw [delivery_shape]
  apply branch_returns program (caller environment result tail free) selected state _ (continuationValue tail)
    cases administrativeBody _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns program (caller environment result tail free) state "continuation"
  · exact administrative_selected environment goal outer result tail free supported
  · unfold administrativeBody
    exact Administration.delivered_in_extension_returns program premiseAgreement selected state environment goal outer result tail
      supported (v "result") (v "continuation") (by simp [selected, caller, callee, Helper.names, applySubst, Subst.lookup])

theorem delivered_within_returns (state : State) (environment : Environment) (goal outer : Execution.Goal)
    (result : Execution.Result environment goal) (tail : Execution.Continuation environment goal outer)
    (footprint : List String)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.taskFreeWithin footprint (.deliver result tail)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.deliver.head
      [environmentValue environment (environment.free.entriesOn footprint), resultValue result, continuationValue tail]) state
      (expansionValue (Execution.delivered environment outer result tail)) := by
  let free := environment.free.entriesOn footprint
  cases tail with
  | rootBody bound type source index rule spec declared specified admitted sorted trace captured matched typed tail =>
      let original := Execution.Continuation.rootBody bound type source index rule spec declared specified admitted sorted trace captured matched typed tail
      let selected : Subst := [("tail", continuationValue tail), ("captured", assignmentValue captured),
        ("trace", encoded (traceTerm trace)), ("spec", MatcherFrames.specValue spec), ("rule", ruleValue rule),
        ("index", number index), ("source", patternValue source), ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm type)),
        ("bound", boundValue bound)] ++ caller environment result original free
      apply helper_call RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement .deliver [] state _ _ _ rfl (QueryExecution.captured_closed _)
      rw [delivery_shape]
      apply branch_returns RuleExecutionProgram.scopedMachineProgram (caller environment result original free) selected state _
        (continuationValue original) cases rootBody _
      · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
          variable_returns RuleExecutionProgram.scopedMachineProgram (caller environment result original free) state "continuation"
      · simp [delivery_cases, original, continuationValue, continuationTerm, selected, caller, callee, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · exact MatcherFrames.Consumer.frame_captured_within_returns MatcherFrames.Checkers.operations .body
          selected state environment footprint outer (.deliver result original)
          [v "environment", v "result", v "continuation"]
          [environmentValue environment free, resultValue result, continuationValue original] rfl covered rfl (by
            simp [selected, caller, callee, Helper.names, applySubst, Subst.lookup])
  | stepped call tail =>
      let original := Execution.Continuation.stepped call tail
      let selected : Subst := [("tail", continuationValue tail), ("call", encoded (stepCallTerm call))] ++
        caller environment result original free
      apply helper_call RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement .deliver [] state _ _ _ rfl (QueryExecution.captured_closed _)
      rw [delivery_shape]
      apply branch_returns RuleExecutionProgram.scopedMachineProgram (caller environment result original free) selected state _
        (continuationValue original) cases steppedBody _
      · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
          variable_returns RuleExecutionProgram.scopedMachineProgram (caller environment result original free) state "continuation"
      · simp [delivery_cases, original, continuationValue, continuationTerm, selected, caller, callee, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · exact MatcherFrames.Consumer.frame_captured_within_returns MatcherFrames.Checkers.operations .stepped
          selected state environment footprint outer (.deliver result original)
          [v "environment", v "result", v "continuation"]
          [environmentValue environment free, resultValue result, continuationValue original] rfl covered rfl (by
            simp [selected, caller, callee, Helper.names, applySubst, Subst.lookup])
  | done goal =>
      exact delivered_administrative_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement AssembledLower.premise_agreement
        state environment _ _ result _ free rfl
  | nextPremise context premise premises initial tail =>
      exact delivered_administrative_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement AssembledLower.premise_agreement
        state environment _ _ result _ free rfl
  | prepend context premise premises initial middle event valid tail =>
      exact delivered_administrative_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement AssembledLower.premise_agreement
        state environment _ _ result _ free rfl
  | quantifier context collection parameter body initial kind elements read tail =>
      exact delivered_administrative_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement AssembledLower.premise_agreement
        state environment _ _ result _ free rfl
  | element context parameter body index element elements initial typed tail =>
      exact delivered_administrative_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement AssembledLower.premise_agreement
        state environment _ _ result _ free rfl
  | prependElement context parameter body index element elements initial middle event typed valid tail =>
      exact delivered_administrative_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement AssembledLower.premise_agreement
        state environment _ _ result _ free rfl
  | searchedRoot bound type source index limit earlier tail =>
      exact delivered_administrative_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement AssembledLower.premise_agreement
        state environment _ _ result _ free rfl

theorem delivered_captured_within_returns (caller : Subst) (state : State) (environment : Environment)
    (goal outer : Execution.Goal) (result : Execution.Result environment goal)
    (tail : Execution.Continuation environment goal outer) (footprint : List String)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.taskFreeWithin footprint (.deliver result tail)) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), resultValue result, continuationValue tail]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a Helper.deliver.head [one, two, three]) state
      (expansionValue (Execution.delivered environment outer result tail)) :=
  helper_capture RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement .deliver caller state [one, two, three]
    [environmentValue environment (environment.free.entriesOn footprint), resultValue result, continuationValue tail] _
    rfl captured (delivered_within_returns state environment goal outer result tail footprint covered)



end Delivery

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval

namespace Tasks

theorem expand_evaluate_returns (state : State) (environment : Environment) (outer goal : Execution.Goal)
    (tail : Execution.Continuation environment goal outer) (footprint : List String)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.goalFreeWithin footprint goal) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.expand.head
      [environmentValue environment (environment.free.entriesOn footprint), taskValue (.evaluate goal tail)]) state
      (expansionValue (Execution.expand environment outer (.evaluate goal tail))) := by
  apply expand_branch_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement state environment outer _
    (environment.free.entriesOn footprint) (evaluateCaller environment outer goal tail _) (taskBody 0) _
    (evaluate_selected environment outer goal tail _)
  rw [evaluate_shape]
  exact Evaluation.evaluate_captured_within_returns (evaluateCaller environment outer goal tail _) state environment outer goal tail
    footprint covered (v "environment") (v "goal") (v "continuation") (by
      simp [evaluateCaller, taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])

theorem expand_deliver_returns (state : State) (environment : Environment) (outer goal : Execution.Goal)
    (result : Execution.Result environment goal) (tail : Execution.Continuation environment goal outer)
    (footprint : List String) (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.taskFreeWithin footprint (.deliver result tail)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.expand.head
      [environmentValue environment (environment.free.entriesOn footprint), taskValue (.deliver result tail)]) state
      (expansionValue (Execution.expand environment outer (.deliver result tail))) := by
  apply expand_branch_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement state environment outer _
    (environment.free.entriesOn footprint) (deliverCaller environment outer goal result tail _) (taskBody 1) _
    (deliver_selected environment outer goal result tail _)
  rw [deliver_shape]
  exact Delivery.delivered_captured_within_returns (deliverCaller environment outer goal result tail _) state environment goal outer
    result tail footprint covered (v "environment") (v "result") (v "continuation") (by
      simp [deliverCaller, taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])

theorem expand_root_returns (state : State) (environment : Environment) (outer : Execution.Goal)
    (frame : Execution.RootMatchFrame environment outer) (footprint : List String)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.taskFreeWithin footprint (.rootMatch frame)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.expand.head
      [environmentValue environment (environment.free.entriesOn footprint), taskValue (.rootMatch frame)]) state
      (expansionValue (Execution.expand environment outer (.rootMatch frame))) := by
  apply expand_branch_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement state environment outer _
    (environment.free.entriesOn footprint) (rootCaller environment outer frame _) (taskBody 3) _
    (root_selected environment outer frame _)
  rw [root_shape]
  exact MatcherFrames.Consumer.frame_captured_within_returns MatcherFrames.Checkers.operations .root
    (rootCaller environment outer frame _) state environment footprint outer (.rootMatch frame)
    [v "environment", v "task"]
    [environmentValue environment (environment.free.entriesOn footprint), taskValue (.rootMatch frame)]
    rfl covered rfl (by simp [rootCaller, taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])

theorem expand_target_returns (state : State) (environment : Environment) (outer : Execution.Goal)
    (frame : Execution.TargetMatchFrame environment outer) (footprint : List String)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.taskFreeWithin footprint (.targetMatch frame)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.expand.head
      [environmentValue environment (environment.free.entriesOn footprint), taskValue (.targetMatch frame)]) state
      (expansionValue (Execution.expand environment outer (.targetMatch frame))) := by
  apply expand_branch_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement state environment outer _
    (environment.free.entriesOn footprint) (targetCaller environment outer frame _) (taskBody 4) _
    (target_selected environment outer frame _)
  rw [target_shape]
  exact MatcherFrames.Consumer.frame_captured_within_returns MatcherFrames.Checkers.operations .target
    (targetCaller environment outer frame _) state environment footprint outer (.targetMatch frame)
    [v "environment", v "task"]
    [environmentValue environment (environment.free.entriesOn footprint), taskValue (.targetMatch frame)]
    rfl covered rfl (by simp [targetCaller, taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])

theorem expand_scan_returns (state : State) (environment : Environment) (outer : Execution.Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit cursor : Nat)
    (tail : Execution.Continuation environment (.steps bound type source limit) outer) (free : List (String × TypeExpr)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.expand.head
      [environmentValue environment free, taskValue (.scanChildren bound type source limit cursor tail)]) state
      (expansionValue (Execution.expand environment outer (.scanChildren bound type source limit cursor tail))) := by
  apply expand_branch_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement state environment outer _ free
    (scanCaller environment outer bound type source limit cursor tail free) (taskBody 5) _
    (scan_selected environment outer bound type source limit cursor tail free)
  rw [scan_shape]
  exact Administration.scan_children_captured_in_extension_returns RuleExecutionProgram.scopedMachineProgram AssembledLower.premise_agreement
    (scanCaller environment outer bound type source limit cursor tail free) state environment outer free bound type source limit cursor tail
    (v "declarations") (v "free") (v "task") (by
      simp [scanCaller, taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])

theorem expand_within_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (outer : Execution.Goal)
    (task : Execution.Task environment outer) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.taskFreeWithin footprint task) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a Helper.expand.head
      [environmentValue environment (environment.free.entriesOn footprint), taskValue task]) state
      (expansionValue (Execution.expand environment outer task)) := by
  cases task with
  | evaluate goal tail => exact expand_evaluate_returns state environment outer goal tail footprint covered.1
  | deliver result tail => exact expand_deliver_returns state environment outer _ result tail footprint covered
  | query request machine cursor tail =>
      exact QueryFrame.expand_query_within_returns RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement ControlAssembly.query_agreement
        ControlAssembly.scheduler_agreement QueryLower.operations state environment outer request machine cursor tail (by simp [finiteProvider]) footprint provider covered.2.1
  | rootMatch frame => exact expand_root_returns state environment outer frame footprint covered
  | targetMatch frame => exact expand_target_returns state environment outer frame footprint covered
  | scanChildren bound type source limit cursor tail =>
      exact expand_scan_returns state environment outer bound type source limit cursor tail (environment.free.entriesOn footprint)

theorem expand_captured_within_returns (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (outer : Execution.Goal)
    (task : Execution.Task environment outer) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.taskFreeWithin footprint task) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), taskValue task]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a Helper.expand.head [one, two]) state
      (expansionValue (Execution.expand environment outer task)) :=
  helper_capture RuleExecutionProgram.scopedMachineProgram AdmissionLower.Assembly.agreement .expand caller state [one, two]
    [environmentValue environment (environment.free.entriesOn footprint), taskValue task] _ rfl captured
    (expand_within_returns state environment finiteProvider outer task footprint provider covered)

theorem expand_captured_completed_iff (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (outer : Execution.Goal)
    (task : Execution.Task environment outer) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.taskFreeWithin footprint task) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), taskValue task])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run RuleExecutionProgram.scopedMachineProgram fuel {state, control := .evaluate caller (a Helper.expand.head [one, two])} =
      .complete after answers input output) ↔
      after = state ∧ answers = [expansionValue (Execution.expand environment outer task)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff RuleExecutionProgram.scopedMachineProgram caller state state _ _
    (expand_captured_within_returns caller state environment finiteProvider outer task footprint provider covered one two captured)
    after answers input output


end Tasks

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.CompletedAssembly
open Eval
theorem run_retained_equations :
    PremiseMachineRunExecution.referenceRuntime.equations.filter
      (fun equation => PremiseMachineRunExecution.executionHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter
      (fun equation => PremiseMachineRunExecution.executionHeads equation.head) := by rfl

theorem run_retained_declarations :
    PremiseMachineRunExecution.referenceRuntime.declarations.filter
      (retainedCallDeclaration PremiseMachineRunExecution.executionHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter
      (retainedCallDeclaration PremiseMachineRunExecution.executionHeads) := by rfl

theorem run_agreement : ProgramAgreementOn PremiseMachineRunExecution.executionHeads
    PremiseMachineRunExecution.referenceRuntime RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _
    run_retained_equations run_retained_declarations

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.CompletedAssembly


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval

namespace Machine

theorem state_scheduler_codec (environment : Environment) (goal : Execution.Goal)
    (machine : Execution.State environment goal) :
    stateTerm machine = PremiseSchedulerExecution.schedulerStateTerm taskTerm resultTerm obligationTerm machine := rfl

theorem expansion_scheduler_codec (environment : Environment) (goal : Execution.Goal)
    (expanded : Scheduler.Expansion (Execution.Task environment goal) (Execution.Result environment goal) Execution.Obligation) :
    expansionTerm expanded = PremiseSchedulerExecution.schedulerExpansionTerm taskTerm resultTerm obligationTerm expanded := rfl

theorem start_returns (state : State) (environment : Environment) (goal : Execution.Goal) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a "gslt:premise:machine-start" [goalValue goal]) state
      (encoded (encodeOption stateTerm (some (Execution.start environment goal)))) :=
  PremiseMachineRunExecution.start_returns RuleExecutionProgram.scopedMachineProgram CompletedAssembly.run_agreement state environment goal

theorem tick_within_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (goal : Execution.Goal)
    (machine : Execution.State environment goal) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.stateFreeWithin footprint environment goal machine) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a "gslt:premise:machine-tick"
      [environmentValue environment (environment.free.entriesOn footprint), encoded (stateTerm machine)]) state
      (encoded (encodeOption stateTerm (some (Execution.tick environment goal machine)))) := by
  apply PremiseMachineRunExecution.tick_returns RuleExecutionProgram.scopedMachineProgram CompletedAssembly.run_agreement state
    (environmentTerm environment (environment.free.entriesOn footprint)) taskTerm resultTerm obligationTerm
    (Execution.expand environment goal) machine
  intro current member caller captured
  exact Tasks.expand_captured_within_returns caller state environment finiteProvider goal current footprint provider (covered.1 current member)
    (v "environment") (v "task") captured

theorem run_state_within_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (goal : Execution.Goal)
    (fuel : Nat) (machine : Execution.State environment goal) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.stateFreeWithin footprint environment goal machine) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a "gslt:premise:machine-run"
      [environmentValue environment (environment.free.entriesOn footprint), number fuel, encoded (stateTerm machine)]) state
      (encoded (encodeOption stateTerm (some (Execution.run environment goal fuel machine)))) := by
  have rows := Mettapedia.OSLF.MeTTaIL.GeneralPremise.provider_coverage_mono _ footprint environment.provider provider
    (Mettapedia.OSLF.MeTTaIL.GeneralPremise.provider_covered_by_own_names environment.provider)
  apply PremiseMachineRunExecution.run_returns RuleExecutionProgram.scopedMachineProgram CompletedAssembly.run_agreement state
    (environmentTerm environment (environment.free.entriesOn footprint)) taskTerm resultTerm obligationTerm
    (Execution.expand environment goal) fuel machine
  intro elapsedTicks bounded current member caller captured
  exact Tasks.expand_captured_within_returns caller state environment finiteProvider goal current footprint provider
    ((Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.run_free_within footprint environment goal rows
      (Query.DynamicOutputsFreeWithin.of_unregistered footprint environment finiteProvider) elapsedTicks machine covered).1 current member)
    (v "environment") (v "task") captured

theorem run_from_start_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (goal : Execution.Goal)
    (fuel : Nat) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (initial : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.goalFreeWithin footprint goal) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a "gslt:premise:machine-run"
      [environmentValue environment (environment.free.entriesOn footprint), number fuel,
        encoded (stateTerm (Execution.start environment goal))]) state
      (encoded (encodeOption stateTerm (some (Execution.run environment goal fuel (Execution.start environment goal))))) :=
  run_state_within_returns state environment finiteProvider goal fuel _ footprint provider
    (Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.start_free_within footprint environment goal initial)

theorem run_state_captured_within_returns (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (goal : Execution.Goal)
    (fuel : Nat) (machine : Execution.State environment goal) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.stateFreeWithin footprint environment goal machine) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), number fuel, encoded (stateTerm machine)]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:machine-run" arguments) state
      (encoded (encodeOption stateTerm (some (Execution.run environment goal fuel machine)))) := by
  have rows := Mettapedia.OSLF.MeTTaIL.GeneralPremise.provider_coverage_mono _ footprint environment.provider provider
    (Mettapedia.OSLF.MeTTaIL.GeneralPremise.provider_covered_by_own_names environment.provider)
  apply PremiseMachineRunExecution.run_captured_returns RuleExecutionProgram.scopedMachineProgram CompletedAssembly.run_agreement caller state
    (environmentTerm environment (environment.free.entriesOn footprint)) taskTerm resultTerm obligationTerm
    (Execution.expand environment goal) fuel machine arguments captured
  intro elapsedTicks bounded current member callee capturedTask
  exact Tasks.expand_captured_within_returns callee state environment finiteProvider goal current footprint provider
    ((Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.run_free_within footprint environment goal rows
      (Query.DynamicOutputsFreeWithin.of_unregistered footprint environment finiteProvider) elapsedTicks machine covered).1 current member)
    (v "environment") (v "task") capturedTask

theorem run_from_start_captured_returns (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (goal : Execution.Goal)
    (fuel : Nat) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (initial : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.goalFreeWithin footprint goal) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), number fuel,
        encoded (stateTerm (Execution.start environment goal))]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:machine-run" arguments) state
      (encoded (encodeOption stateTerm (some (Execution.run environment goal fuel (Execution.start environment goal))))) :=
  run_state_captured_within_returns caller state environment finiteProvider goal fuel _ footprint provider
    (Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.start_free_within footprint environment goal initial) arguments captured

theorem run_state_captured_completed_iff (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (goal : Execution.Goal)
    (fuel : Nat) (machine : Execution.State environment goal) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.stateFreeWithin footprint environment goal machine) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), number fuel, encoded (stateTerm machine)])
    (after : State) (answers input output : List Atom) :
    (∃ evaluatorFuel, run RuleExecutionProgram.scopedMachineProgram evaluatorFuel {state, control := .evaluate caller (a "gslt:premise:machine-run" arguments)} =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption stateTerm (some (Execution.run environment goal fuel machine)))] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff RuleExecutionProgram.scopedMachineProgram caller state state _ _
    (run_state_captured_within_returns caller state environment finiteProvider goal fuel machine footprint provider covered arguments captured)
    after answers input output

theorem run_from_start_captured_completed_iff (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (goal : Execution.Goal)
    (fuel : Nat) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (initial : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.goalFreeWithin footprint goal) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), number fuel,
        encoded (stateTerm (Execution.start environment goal))])
    (after : State) (answers input output : List Atom) :
    (∃ evaluatorFuel, run RuleExecutionProgram.scopedMachineProgram evaluatorFuel {state, control := .evaluate caller (a "gslt:premise:machine-run" arguments)} =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption stateTerm
        (some (Execution.run environment goal fuel (Execution.start environment goal))))] ∧ input = [] ∧ output = [] :=
  run_state_captured_completed_iff caller state environment finiteProvider goal fuel _ footprint provider
    (Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.start_free_within footprint environment goal initial) arguments captured after answers input output


end Machine

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Machine

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval

theorem root_run_captured_returns (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index fuel : Nat) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn (source.freeFvarNames ++ providerFreeNames environment.provider)),
        number fuel, encoded (stateTerm (Execution.start environment (.root bound type source index)))]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:machine-run" arguments) state
      (encoded (encodeOption stateTerm (some (Execution.run environment (.root bound type source index) fuel
        (Execution.start environment (.root bound type source index)))))) :=
  run_from_start_captured_returns caller state environment finiteProvider (.root bound type source index) fuel _
    (fun _ member => List.mem_append_right _ member)
    (fun _ member => List.mem_append_left _ member) arguments captured

theorem steps_run_captured_returns (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit fuel : Nat) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn (source.freeFvarNames ++ providerFreeNames environment.provider)),
        number fuel, encoded (stateTerm (Execution.start environment (.steps bound type source limit)))]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:machine-run" arguments) state
      (encoded (encodeOption stateTerm (some (Execution.run environment (.steps bound type source limit) fuel
        (Execution.start environment (.steps bound type source limit)))))) :=
  run_from_start_captured_returns caller state environment finiteProvider (.steps bound type source limit) fuel _
    (fun _ member => List.mem_append_right _ member)
    (fun _ member => List.mem_append_left _ member) arguments captured

theorem premises_run_captured_returns (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (context : Context) (premises : List Premise) (initial : Assignment) (fuel : Nat)
    (admitted : admittedFor context.rule context.spec = true) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn
        (ConditionalEquationExecution.assignmentFreeNames initial ++ providerFreeNames environment.provider)),
        number fuel, encoded (stateTerm (Execution.start environment (.premises context premises initial)))]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:machine-run" arguments) state
      (encoded (encodeOption stateTerm (some (Execution.run environment (.premises context premises initial) fuel
        (Execution.start environment (.premises context premises initial)))))) := by
  apply run_from_start_captured_returns caller state environment finiteProvider (.premises context premises initial) fuel _
    (fun _ member => List.mem_append_right _ member) _ arguments captured
  exact ⟨admitted, Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_coverage_mono _ _ initial
    (fun _ member => List.mem_append_left _ member) (Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_covered_by_own_names initial)⟩

theorem premise_run_captured_returns (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (context : Context) (premise : Premise) (initial : Assignment) (fuel : Nat)
    (admitted : admittedFor context.rule context.spec = true) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn
        (ConditionalEquationExecution.assignmentFreeNames initial ++ providerFreeNames environment.provider)),
        number fuel, encoded (stateTerm (Execution.start environment (.premise context premise initial)))]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:machine-run" arguments) state
      (encoded (encodeOption stateTerm (some (Execution.run environment (.premise context premise initial) fuel
        (Execution.start environment (.premise context premise initial)))))) := by
  apply run_from_start_captured_returns caller state environment finiteProvider (.premise context premise initial) fuel _
    (fun _ member => List.mem_append_right _ member) _ arguments captured
  exact ⟨admitted, Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_coverage_mono _ _ initial
    (fun _ member => List.mem_append_left _ member) (Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_covered_by_own_names initial)⟩

theorem quantified_run_captured_returns (caller : Subst) (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (context : Context) (parameter : String) (body : Premise) (index : Nat) (elements : List Pattern)
    (initial : Assignment) (fuel : Nat) (admitted : admittedFor context.rule context.spec = true) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn
        (ConditionalEquationExecution.assignmentFreeNames initial ++ elements.flatMap Pattern.freeFvarNames ++ providerFreeNames environment.provider)),
        number fuel, encoded (stateTerm (Execution.start environment (.quantified context parameter body index elements initial)))]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:machine-run" arguments) state
      (encoded (encodeOption stateTerm (some (Execution.run environment (.quantified context parameter body index elements initial) fuel
        (Execution.start environment (.quantified context parameter body index elements initial)))))) := by
  apply run_from_start_captured_returns caller state environment finiteProvider (.quantified context parameter body index elements initial) fuel _
    (fun _ member => List.mem_append_right _ member) _ arguments captured
  refine ⟨admitted, ?_, ?_⟩
  · exact Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_coverage_mono _ _ initial
      (fun _ member => List.mem_append_left _ (List.mem_append_left _ member))
      (Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_covered_by_own_names initial)
  · intro element member name occurs
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨element, member, occurs⟩))


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Machine


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Machine

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval

theorem complete_captured_returns (caller : Subst) (state : State) (environment : Environment) (goal : Execution.Goal)
    (machine : Execution.State environment goal) (argument : Atom)
    (captured : applySubst caller argument = encoded (stateTerm machine)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:machine-complete" [argument]) state
      (Effects.boolean (Execution.complete environment goal machine)) := by
  let aliases : Subst := [("scheduler", encoded (stateTerm machine))]
  have source := PremiseSchedulerExecution.complete_captured_returns aliases state taskTerm resultTerm obligationTerm machine
    [v "scheduler"] (by simp [aliases, applySubst, Subst.lookup, state_scheduler_codec])
  have transported := PremiseSchedulerExecution.returns_in_extension RuleExecutionProgram.scopedMachineProgram ControlAssembly.scheduler_agreement
    (show codeWithin PremiseSchedulerExecution.executionHeads (a "gslt:premise:machine-complete" [v "scheduler"]) = true by decide +kernel)
    source
  apply captured_call_returns RuleExecutionProgram.scopedMachineProgram aliases caller state state "gslt:premise:machine-complete"
    [v "scheduler"] [argument] _ _ (by decide) _ _ _ transported
  · rw [← ControlAssembly.scheduler_agreement.dispatch "gslt:premise:machine-complete" (by decide)]
    decide +kernel
  · intro offset value selected
    have same : offset = 0 := by
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    subst offset
    simp at selected
    subst value
    exact Or.inr rfl
  · intro offset value selected
    have same : offset = 0 := by
      have bounded := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    subst offset
    apply Or.inl
    rw [← ControlAssembly.scheduler_agreement.demand "gslt:premise:machine-complete" 0 (by decide)]
    decide +kernel
  · simp [aliases, applySubst, Subst.lookup, captured]

theorem complete_returns (state : State) (environment : Environment) (goal : Execution.Goal)
    (machine : Execution.State environment goal) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (a "gslt:premise:machine-complete" [encoded (stateTerm machine)]) state
      (Effects.boolean (Execution.complete environment goal machine)) :=
  complete_captured_returns [] state environment goal machine _ (Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil _)

theorem complete_captured_completed_iff (caller : Subst) (state : State) (environment : Environment) (goal : Execution.Goal)
    (machine : Execution.State environment goal) (argument : Atom)
    (captured : applySubst caller argument = encoded (stateTerm machine)) (after : State) (answers input output : List Atom) :
    (∃ evaluatorFuel, run RuleExecutionProgram.scopedMachineProgram evaluatorFuel {state, control := .evaluate caller (a "gslt:premise:machine-complete" [argument])} =
      .complete after answers input output) ↔
      after = state ∧ answers = [Effects.boolean (Execution.complete environment goal machine)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff RuleExecutionProgram.scopedMachineProgram caller state state _ _
    (complete_captured_returns caller state environment goal machine argument captured) after answers input output


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Machine
