import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Closed first-order reification into the declaration-derived signature

This codec searches the existing constructor declarations, retaining their
membership evidence. It introduces no constructor inventory or metavariable
dependency convention. A successful result carries the requested sort and
erases to its exact input. Completeness concerns closed, actually typed
patterns accepted by the existing first-order compiler, not validation alone.

Unsupported forms remain outside this codec; no rule-firing or rejection
semantics is changed. Ambiguous declarations can yield different intrinsic
typing witnesses with the same erasure. No canonical ambiguity policy or
matching adequacy follows from choosing a successful witness here.
-/

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.Reification

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

set_option autoImplicit false

/-- A checked argument row in the existing parameter-scope and term syntax. -/
structure ReifiedArguments (language : LanguageDef) (parameters : List TermParam) where
  arity : List (List TypeExpr × TypeExpr)
  scopes : ParameterScopes parameters arity
  arguments : Args (signatureOf language) arity []

/-- Test one actual declaration against the requested label, sort, and typed
argument row. The callback is the recursive argument elaboration. -/
def constructorCandidate? (language : LanguageDef) (label : String) (type : TypeExpr)
    (arguments : ∀ parameters, Option (ReifiedArguments language parameters))
    (rule : {rule : GrammarRule // rule ∈ language.terms}) :
    Option (Term (signatureOf language) [] type) :=
  if rule.val.label = label then
    if sameType : .base rule.val.category = type then
      if ordinaryCheck : usesBareCollection? rule.val = false then
        let ordinary : ¬ UsesBareCollection rule.val := fun bare => by
          have checked := (usesBareCollection?_eq_true_iff rule.val).mpr bare
          rw [ordinaryCheck] at checked
          cases checked
        (arguments rule.val.params).map fun receipt =>
          sameType ▸ Term.op
            (Operator.constructor rule.val rule.property ordinary receipt.scopes)
            receipt.arguments
      else none
    else none
  else none

mutual
  /-- Reify a closed first-order input at its requested sort by searching the
  authored declarations. No proof-to-data choice operation is used. -/
  def reify? (language : LanguageDef) (pattern : Pattern) (type : TypeExpr) :
      Option (Term (signatureOf language) [] type) :=
    match pattern with
    | .apply label arguments =>
        language.terms.attach.findSome?
          (constructorCandidate? language label type
            (fun parameters => reifyArguments? language arguments parameters))
    | _ => none
  termination_by sizeOf pattern
  decreasing_by simp_wf

  /-- Reify an ordered row using only the simple parameters admissible in the
  closed first-order fragment. Binder parameters are not reinterpreted. -/
  def reifyArguments? (language : LanguageDef) (patterns : List Pattern)
      (parameters : List TermParam) : Option (ReifiedArguments language parameters) :=
    match patterns, parameters with
    | [], [] => some ⟨[], .nil, .nil⟩
    | pattern :: patterns, .simple name type :: parameters => do
        let head ← reify? language pattern type
        let tail ← reifyArguments? language patterns parameters
        pure ⟨([], type) :: tail.arity,
          .cons (.simple name type) tail.scopes, .cons head tail.arguments⟩
    | _, _ => none
  termination_by sizeOf patterns
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

theorem erase_sort_cast {language : LanguageDef} {first second : TypeExpr}
    (same : first = second) (term : Term (signatureOf language) [] first) :
    erase (same ▸ term) = erase term := by
  subst second
  rfl

theorem constructorCandidate?_erases
    {language : LanguageDef} {label : String} {type : TypeExpr}
    {patterns : List Pattern}
    {arguments : ∀ parameters, Option (ReifiedArguments language parameters)}
    (roundtrip : ∀ parameters receipt, arguments parameters = some receipt →
      eraseConstructorArguments receipt.scopes receipt.arguments = patterns)
    {rule : {rule : GrammarRule // rule ∈ language.terms}}
    {term : Term (signatureOf language) [] type}
    (accepted : constructorCandidate? language label type arguments rule = some term) :
    erase term = .apply label patterns := by
  unfold constructorCandidate? at accepted
  split at accepted
  · rename_i sameLabel
    split at accepted
    · rename_i sameType
      split at accepted
      · rename_i ordinary
        cases elaborated : arguments rule.val.params with
        | none => simp [elaborated] at accepted
        | some receipt =>
            simp only [elaborated, Option.map_some, Option.some.injEq] at accepted
            subst term
            rw [erase_sort_cast]
            simp only [erase]
            rw [roundtrip _ _ elaborated, sameLabel]
      · simp at accepted
    · simp at accepted
  · simp at accepted

mutual
  /-- Successful reification retains the exact source pattern. -/
  theorem reify?_erases {language : LanguageDef} {pattern : Pattern}
      {type : TypeExpr} {term : Term (signatureOf language) [] type}
      (accepted : reify? language pattern type = some term) : erase term = pattern := by
    cases pattern with
    | apply label patterns =>
        simp only [reify?] at accepted
        obtain ⟨rule, _, candidate⟩ := List.exists_of_findSome?_eq_some accepted
        exact constructorCandidate?_erases
          (fun parameters receipt elaborated => reifyArguments?_erases elaborated) candidate
    | bvar index => simp [reify?] at accepted
    | fvar name => simp [reify?] at accepted
    | lambda binder body => simp [reify?] at accepted
    | multiLambda count binders body => simp [reify?] at accepted
    | subst body replacement => simp [reify?] at accepted
    | collection kind elements rest => simp [reify?] at accepted
  termination_by sizeOf pattern
  decreasing_by
    all_goals (simp_all only [Pattern.apply.sizeOf_spec]; omega)

  /-- Successful argument elaboration retains every ordered source entry. -/
  theorem reifyArguments?_erases {language : LanguageDef}
      {patterns : List Pattern} {parameters : List TermParam}
      {receipt : ReifiedArguments language parameters}
      (accepted : reifyArguments? language patterns parameters = some receipt) :
      eraseConstructorArguments receipt.scopes receipt.arguments = patterns := by
    cases patterns with
    | nil =>
        cases parameters with
        | nil =>
            simp only [reifyArguments?, Option.some.injEq] at accepted
            subst receipt
            rfl
        | cons parameter parameters => simp [reifyArguments?] at accepted
    | cons pattern patterns =>
        cases parameters with
        | nil => simp [reifyArguments?] at accepted
        | cons parameter parameters =>
            cases parameter with
            | abstractionNamed binder name type => simp [reifyArguments?] at accepted
            | multiAbstractionNamed binders name type => simp [reifyArguments?] at accepted
            | simple name type =>
                cases head : reify? language pattern type with
                | none => simp [reifyArguments?, head] at accepted
                | some term =>
                    cases tail : reifyArguments? language patterns parameters with
                    | none => simp [reifyArguments?, head, tail] at accepted
                    | some rest =>
                        simp [reifyArguments?, head, tail] at accepted
                        subst receipt
                        simp only [eraseConstructorArguments, ParameterScope.wrap]
                        rw [reify?_erases head, reifyArguments?_erases tail]
  termination_by sizeOf patterns
  decreasing_by all_goals (simp_all only [List.cons.sizeOf_spec]; omega)
end

/-- The requested sort is checked by the original judgment, not validation. -/
theorem reify?_typed {language : LanguageDef} {pattern : Pattern} {type : TypeExpr}
    {term : Term (signatureOf language) [] type}
    (accepted : reify? language pattern type = some term) :
    HasType language FreeTypeContext.empty [] pattern type := by
  rw [← reify?_erases accepted]
  exact erase_typed term

/-- First-order acceptance excludes the representation binders required by
abstraction parameters, including a multiple abstraction with zero binders. -/
theorem simple_parameter_of_firstOrder
    {parameter : TermParam} {pattern : Pattern}
    (representation : MatchesParameterRepresentation parameter pattern)
    (accepted : compilePattern? pattern ≠ none) :
    ∃ name type, parameter = .simple name type := by
  cases parameter with
  | simple name type => exact ⟨name, type, rfl⟩
  | abstractionNamed binder name type =>
      obtain ⟨body, rfl⟩ :=
        (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
      simp [compilePattern?] at accepted
  | multiAbstractionNamed binders name type =>
      obtain ⟨count, body, rfl⟩ :=
        (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ _).mp representation
      simp [compilePattern?] at accepted

theorem compilePatterns?_ne_none_of_apply
    {label : String} {patterns : List Pattern}
    (accepted : compilePattern? (.apply label patterns) ≠ none) :
    compilePatterns? patterns ≠ none := by
  intro rejected
  simp [compilePattern?, rejected] at accepted

theorem compilePattern?_ne_none_of_cons
    {pattern : Pattern} {patterns : List Pattern}
    (accepted : compilePatterns? (pattern :: patterns) ≠ none) :
    compilePattern? pattern ≠ none := by
  intro rejected
  simp [compilePatterns?, rejected] at accepted

theorem compilePatterns?_ne_none_of_cons
    {pattern : Pattern} {patterns : List Pattern}
    (accepted : compilePatterns? (pattern :: patterns) ≠ none) :
    compilePatterns? patterns ≠ none := by
  intro rejected
  cases head : compilePattern? pattern <;>
    simp [compilePatterns?, rejected, head] at accepted

mutual
  /-- Every closed, typed first-order pattern has an actual computed receipt.
  This needs neither a validation premise nor uniqueness of declarations. -/
  theorem reify?_complete {language : LanguageDef} {pattern : Pattern}
      {type : TypeExpr}
      (typed : HasType language FreeTypeContext.empty [] pattern type)
      (accepted : compilePattern? pattern ≠ none) :
      (reify? language pattern type).isSome = true := by
    cases typed with
    | bvar lookup => simp at lookup
    | fvar lookup => simp [FreeTypeContext.empty] at lookup
    | @constructor _ rule patterns member ordinary argumentsTyped =>
        have argumentsSome := reifyArguments?_complete argumentsTyped
          (compilePatterns?_ne_none_of_apply accepted)
        simp only [reify?]
        apply List.findSome?_isSome_iff.mpr
        refine ⟨⟨rule, member⟩, List.mem_attach _ _, ?_⟩
        have ordinaryCheck : usesBareCollection? rule = false := by
          cases checked : usesBareCollection? rule with
          | false => rfl
          | true =>
              exact False.elim
                (ordinary ((usesBareCollection?_eq_true_iff rule).mp checked))
        simp only [constructorCandidate?, dif_pos ordinaryCheck]
        cases result : reifyArguments? language patterns rule.params with
        | none => simp [result] at argumentsSome
        | some receipt => simp
    | lambda bodyTyped => simp [compilePattern?] at accepted
    | multiLambda bodyTyped => simp [compilePattern?] at accepted
    | subst bodyTyped replacementTyped => simp [compilePattern?] at accepted
    | collection elementsTyped => simp [compilePattern?] at accepted
    | collectionConstructor member shape elementsTyped => simp [compilePattern?] at accepted
  termination_by sizeOf pattern
  decreasing_by
    all_goals (simp_all only [Pattern.apply.sizeOf_spec]; omega)

  /-- Argument reconstruction uses the typing derivation's actual parameter
list; it does not infer binder permissions from a traversal. -/
  theorem reifyArguments?_complete {language : LanguageDef}
      {patterns : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language FreeTypeContext.empty [] patterns parameters)
      (accepted : compilePatterns? patterns ≠ none) :
      (reifyArguments? language patterns parameters).isSome = true := by
    cases typed with
    | nil => simp [reifyArguments?]
    | @cons _ pattern patterns parameter parameters expected representation
        expectedType patternTyped patternsTyped =>
        have headAccepted := compilePattern?_ne_none_of_cons accepted
        have tailAccepted := compilePatterns?_ne_none_of_cons accepted
        obtain ⟨name, type, rfl⟩ :=
          simple_parameter_of_firstOrder representation headAccepted
        simp only [parameterType?, Option.some.injEq] at expectedType
        subst expected
        have headSome := reify?_complete patternTyped headAccepted
        have tailSome := reifyArguments?_complete patternsTyped tailAccepted
        cases head : reify? language pattern type with
        | none => simp [head] at headSome
        | some term =>
            cases tail : reifyArguments? language patterns parameters with
            | none => simp [tail] at tailSome
            | some receipt => simp [reifyArguments?, head, tail]
  termination_by sizeOf patterns
  decreasing_by
    all_goals (simp_all only [List.cons.sizeOf_spec]; omega)
end

/-- A reverse constructor bridge for arbitrary existing declarations, with
the actual computed intrinsic term and its exact erasure as the receipt. -/
theorem exists_reification_of_typed_firstOrder
    {language : LanguageDef} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language FreeTypeContext.empty [] pattern type)
    (accepted : compilePattern? pattern ≠ none) :
    ∃ term : Term (signatureOf language) [] type,
      reify? language pattern type = some term ∧ erase term = pattern := by
  have found := reify?_complete typed accepted
  cases result : reify? language pattern type with
  | none => simp [result] at found
  | some term => exact ⟨term, rfl, reify?_erases result⟩

/-- On the existing first-order fragment, computed reifiability is exactly
the original closed typing judgment. -/
theorem reify?_isSome_iff_typed
    {language : LanguageDef} {pattern : Pattern} {type : TypeExpr}
    (accepted : compilePattern? pattern ≠ none) :
    (reify? language pattern type).isSome = true ↔
      HasType language FreeTypeContext.empty [] pattern type := by
  constructor
  · intro found
    cases result : reify? language pattern type with
    | none => simp [result] at found
    | some term => exact reify?_typed result
  · intro typed
    exact reify?_complete typed accepted

end Mettapedia.GSLT.LanguageDef.BindingSyntax.Reification
