import Mettapedia.OSLF.MeTTaIL.EngineCoded.RuleApplication
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Base premises computed on codes

A rule's premises are fixed by its language, so they are constants here. For a
relation environment whose tuples are computable on codes, every premise that
the base evaluator answers is computable on codes as a function of the bindings
it extends (`basePremise_computable`): a freshness condition, a relation query,
and the premises it leaves to the contextual step (congruence, scoped steps)
or does not answer (quantifiers). Choosing among a fixed list of computable
functions by position is computable (`table_computable`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EngineCoded

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.PatternCode.CodeComputable'
open CodeComputable
open private resolveFreshVarName from Mettapedia.OSLF.MeTTaIL.Engine

/-- **Choosing among a fixed list of computable functions by position is computable on codes.** -/
theorem table_computable {α β : Type} [Coded α] [Coded β] (fallback : β) :
    ∀ functions : List (α → β), (∀ f ∈ functions, CodeComputable f) →
      CodeComputable fun input : ℕ × α => (functions.getD input.1 (fun _ => fallback)) input.2
  | [], _ => (const fallback).of_eq fun _ => rfl
  | f :: rest, computable => by
      have later := table_computable fallback rest fun g member => computable g (List.mem_cons_of_mem _ member)
      refine (CodeComputable.ite (nat_eq fst (const 0)) ((computable f List.mem_cons_self).comp snd)
        (later.comp (pair (nat_sub fst (const 1)) snd))).of_eq fun input => ?_
      rcases input with ⟨index, argument⟩
      cases index <;> simp

/-- Choosing by position among a fixed list of computable functions, with a computable fallback beyond
the list, is computable on codes. -/
theorem tableOr_computable {α β : Type} [Coded α] [Coded β] {fallback : α → β}
    (hFallback : CodeComputable fallback) :
    ∀ functions : List (α → β), (∀ f ∈ functions, CodeComputable f) →
      CodeComputable fun input : ℕ × α => (functions.getD input.1 fallback) input.2
  | [], _ => (hFallback.comp snd).of_eq fun _ => rfl
  | f :: rest, computable => by
      have later := tableOr_computable hFallback rest fun g member => computable g (List.mem_cons_of_mem _ member)
      refine (CodeComputable.ite (nat_eq fst (const 0)) ((computable f List.mem_cons_self).comp snd)
        (later.comp (pair (nat_sub fst (const 1)) snd))).of_eq fun input => ?_
      rcases input with ⟨index, argument⟩
      cases index <;> simp

/-! ## Relation queries -/

theorem matchRelationArgument_of_not_fvar {argument : Pattern} (notName : ∀ name, argument ≠ .fvar name)
    (bindings : Bindings) (value : Pattern) :
    matchRelationArgument bindings argument value = matchPattern argument value := by
  cases argument with
  | fvar name => exact absurd rfl (notName name)
  | _ => rfl

theorem matchRelationArgument_computable (argument : Pattern) :
    CodeComputable fun input : Bindings × Pattern => matchRelationArgument input.1 argument input.2 := by
  by_cases isName : ∃ name, argument = .fvar name
  · obtain ⟨name, rfl⟩ := isName
    have lookedUp : CodeComputable fun input : Bindings × Pattern => input.1.lookup name :=
      lookup_computable.comp (pair fst (const name))
    have absent : CodeComputable fun input : Bindings × Pattern => [[(name, input.2)]] :=
      list_cons (list_cons (pair (const name) snd) (const [])) (const [])
    have present : CodeComputable₂ fun (input : Bindings × Pattern) (existing : Pattern) =>
        (if existing = input.2 then [[]] else [] : List Bindings) :=
      (CodeComputable.ite (patternEq.comp (pair snd (snd.comp fst))) (const [[]]) (const [])).of_eq fun y => by
        by_cases same : y.2 = y.1.2 <;> simp [same]
    refine (option_casesOn lookedUp absent present).of_eq fun input => ?_
    simp only [matchRelationArgument]
    cases input.1.lookup name <;> rfl
  · have notName : ∀ name, argument ≠ .fvar name := fun name same => isName ⟨name, same⟩
    exact (matchPattern_computable.comp (pair (const argument) snd)).of_eq fun input =>
      (matchRelationArgument_of_not_fvar notName input.1 input.2).symm

theorem matchRelationArgs_computable : ∀ arguments : List Pattern,
    CodeComputable fun input : Bindings × List Pattern => matchRelationArgs input.1 arguments input.2
  | [] => by
      refine (CodeComputable.ite (nat_eq (list_length snd) (const 0)) (const [[]]) (const [])).of_eq
        fun input => ?_
      rcases input with ⟨seed, values⟩
      cases values <;> simp [matchRelationArgs]
  | argument :: arguments => by
      have later := matchRelationArgs_computable arguments
      have firstValue : CodeComputable fun input : Bindings × List Pattern => input.2.getD 0 (Pattern.bvar 0) :=
        list_getD (Pattern.bvar 0) snd (const 0)
      have heads : CodeComputable fun input : Bindings × List Pattern =>
          matchRelationArgument input.1 argument (input.2.getD 0 (Pattern.bvar 0)) :=
        (matchRelationArgument_computable argument).comp (pair fst firstValue)
      have mergeHead : CodeComputable₂ fun (z : ((Bindings × List Pattern) × Bindings) × Bindings)
          (tail : Bindings) => mergeBindings z.1.2 tail :=
        mergeBindings_computable.comp (pair (snd.comp (fst.comp fst)) snd)
      have extendWith : CodeComputable₂ fun (y : (Bindings × List Pattern) × Bindings) (extended : Bindings) =>
          (matchRelationArgs extended arguments y.1.2.tail).filterMap (mergeBindings y.2) :=
        list_filterMap (later.comp (pair snd (list_tail (snd.comp (fst.comp fst))))) mergeHead
      have branch : CodeComputable₂ fun (input : Bindings × List Pattern) (head : Bindings) =>
          Option.casesOn (motive := fun _ => List Bindings) (mergeBindings input.1 head) []
            fun extended => (matchRelationArgs extended arguments input.2.tail).filterMap (mergeBindings head) :=
        option_casesOn (mergeBindings_computable.comp (pair (fst.comp fst) snd)) (const []) extendWith
      refine (CodeComputable.ite (nat_eq (list_length snd) (const 0)) (const [])
        (list_flatMap heads branch)).of_eq fun input => ?_
      rcases input with ⟨seed, values⟩
      cases values with
      | nil => simp [matchRelationArgs]
      | cons value values =>
          simp only [List.length_cons, Nat.add_one_ne_zero, decide_false, Bool.false_eq_true, if_false,
            List.getD_cons_zero, List.tail_cons]
          rw [matchRelationArgs]
          congr 1
          funext head
          cases mergeBindings seed head <;> rfl

theorem builtinRelationTuples_computable (language : LanguageDef) (relation : String) :
    CodeComputable fun arguments : List Pattern => builtinRelationTuples language relation arguments := by
  by_cases equality : relation = "eq"
  · subst equality
    have first := list_getD (Pattern.bvar 0) (id : CodeComputable fun arguments : List Pattern => arguments) (const 0)
    have second := list_getD (Pattern.bvar 0) (id : CodeComputable fun arguments : List Pattern => arguments) (const 1)
    refine (CodeComputable.ite (nat_eq (list_length id) (const 2))
      (list_cons (list_cons first (list_cons first (const [])))
        (list_cons (list_cons second (list_cons second (const []))) (const []))) (const [])).of_eq
      fun arguments => ?_
    match arguments with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | _ :: _ :: _ :: _ => simp [builtinRelationTuples]
  · refine (const ([] : List (List Pattern))).of_eq fun arguments => ?_
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;>
      simp [builtinRelationTuples, equality]

/-- **A relation query with fixed name and arguments is computable on codes** in the bindings it extends. -/
theorem relationQueryStep_computable (relEnv : RelationEnv) (relations : CodeComputable₂ relEnv.tuples)
    (language : LanguageDef) (relation : String) (arguments : List Pattern) :
    CodeComputable fun bindings : Bindings => relationQueryStep relEnv language bindings relation arguments := by
  have instantiated : CodeComputable fun bindings : Bindings => arguments.map (applyBindings bindings) :=
    list_map (const arguments) applyBindings_computable
  have tuples : CodeComputable fun bindings : Bindings =>
      builtinRelationTuples language relation (arguments.map (applyBindings bindings)) ++
        relEnv.tuples relation (arguments.map (applyBindings bindings)) :=
    list_append ((builtinRelationTuples_computable language relation).comp instantiated)
      (relations.comp (pair (const relation) instantiated))
  exact (list_flatMap tuples (list_filterMap ((matchRelationArgs_computable arguments).comp (pair fst snd))
    (mergeBindings_computable.comp (pair (fst.comp fst) snd)))).of_eq fun _ => rfl

/-! ## Freshness -/

theorem resolveFreshVarName_computable (name : String) :
    CodeComputable fun bindings : Bindings => resolveFreshVarName bindings name := by
  have lookedUp : CodeComputable fun bindings : Bindings => bindings.lookup name :=
    lookup_computable.comp (pair id (const name))
  have value : CodeComputable₂ fun (_ : Bindings) (value : Pattern) =>
      @Pattern.casesOn (fun _ => Option String) value (fun _ => none) (fun other => some other)
        (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ => none) (fun _ _ _ => none) :=
    (casesOn (pattern := fun input : Bindings × Pattern => input.2) (onBVar := fun _ _ => (none : Option String))
      (onFVar := fun _ other => some other) (onApply := fun _ _ _ => none) (onLambda := fun _ _ _ => none)
      (onMultiLambda := fun _ _ _ _ => none) (onSubst := fun _ _ _ => none) (onCollection := fun _ _ _ _ => none)
      snd (const none) (optionString_some snd) (const none) (const none) (const none) (const none)
      (const none)).of_eq fun _ => rfl
  refine (option_casesOn lookedUp (const (some name)) value).of_eq fun bindings => ?_
  unfold resolveFreshVarName
  cases bindings.lookup name with
  | none => rfl
  | some found => cases found <;> rfl

theorem freshness_computable (relEnv : RelationEnv) (language : LanguageDef) (condition : FreshnessCondition) :
    CodeComputable fun bindings : Bindings => premiseStepWithEnv relEnv language bindings (.freshness condition) := by
  have instantiated : CodeComputable fun bindings : Bindings => applyBindings bindings condition.term :=
    applyBindings_computable.comp (pair id (const condition.term))
  have fresh : CodeComputable₂ fun (bindings : Bindings) (name : String) =>
      (if checkFreshness { varName := name, term := applyBindings bindings condition.term } then [bindings]
        else [] : List Bindings) :=
    (CodeComputable.ite (CodeComputable.not (list_contains stringCode_injective'
      (freeVars_computable.comp (instantiated.comp fst)) snd)) (list_cons fst (const [])) (const [])).of_eq
      fun _ => rfl
  refine (optionString_casesOn (resolveFreshVarName_computable condition.varName) (const []) fresh).of_eq
    fun bindings => ?_
  simp only [premiseStepWithEnv]
  cases resolveFreshVarName bindings condition.varName <;> rfl

/-- **Every premise of the base evaluator is computable on codes** in the bindings it extends, when the
relation environment is. -/
theorem basePremise_computable (relEnv : RelationEnv) (relations : CodeComputable₂ relEnv.tuples)
    (language : LanguageDef) (premise : Premise) :
    CodeComputable fun bindings : Bindings => engineBasePremises relEnv language bindings premise := by
  cases premise with
  | freshness condition => exact freshness_computable relEnv language condition
  | congruence source target => exact (const []).of_eq fun _ => rfl
  | scopedStep step => exact (const []).of_eq fun _ => rfl
  | relationQuery relation arguments =>
      exact relationQueryStep_computable relEnv relations language relation arguments
  | forAll collection parameter body => exact (const []).of_eq fun _ => rfl

end Mettapedia.OSLF.MeTTaIL.EngineCoded

#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.basePremise_computable
