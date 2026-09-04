import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedFrontier
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-!
# Typed-frontier signatures compiled from `LanguageDef`

This module supplies the missing generic bridge from an authored
`LanguageDef` to the sorted constructor signature consumed by top-down typed
refinement.  A compiled head contains the source grammar rule, a proof that
the rule occurs in that exact language definition, and the exact list of base
sorts obtained from its parameters.  Consequently neither result sorts nor
child sorts can be supplied by a second hand-maintained table.

Rules with binders or non-base parameter types are rejected by this first
compiler rather than silently flattened.  Languages needing those forms must
compile them through a richer signature projection with its own adequacy
proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.LanguageDefSignature

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedFrontier

/-- Extract the child sort of an ordinary, base-sorted constructor
parameter.  Binder-bearing and higher type expressions are outside this
projection and fail closed. -/
def parameterBaseSort? : TermParam → Option String
  | .simple _ (.base sort) => some sort
  | _ => none

/-- Compile all parameter sorts or reject the complete rule. -/
def parameterBaseSorts? : List TermParam → Option (List String)
  | [] => some []
  | parameter :: parameters => do
      let sort ← parameterBaseSort? parameter
      let sorts ← parameterBaseSorts? parameters
      pure (sort :: sorts)

/-- One constructor head authenticated against an exact source
`LanguageDef`. -/
structure Head (source : LanguageDef) where
  rule : GrammarRule
  sourceMember : rule ∈ source.terms
  childSorts : List String
  childSortsExact : parameterBaseSorts? rule.params = some childSorts

/-- Compile one source rule.  Membership and base-sort extraction are both
checked by the function that constructs the proof-bearing result. -/
def compileHead? (source : LanguageDef) (rule : GrammarRule) :
    Option (Head source) :=
  if sourceMember : rule ∈ source.terms then
    match childSortsExact : parameterBaseSorts? rule.params with
    | none => none
    | some childSorts =>
        some ⟨rule, sourceMember, childSorts, childSortsExact⟩
  else none

/-- The typed-frontier signature is a projection of the authenticated rule;
it contains no independently authored sort or arity function. -/
def signature (source : LanguageDef) : TypedFrontier.Signature where
  SortType := String
  Head := Head source
  resultSort := fun head => head.rule.category
  childSorts := fun head => head.childSorts

@[simp] theorem signature_resultSort (source : LanguageDef)
    (head : Head source) :
    (signature source).resultSort head = head.rule.category := rfl

@[simp] theorem signature_childSorts (source : LanguageDef)
    (head : Head source) :
    (signature source).childSorts head = head.childSorts := rfl

/-- Successful compilation exposes exactly the source rule and its extracted
parameter sorts. -/
theorem compileHead?_some_exact (source : LanguageDef)
    (rule : GrammarRule) (head : Head source)
    (compiled : compileHead? source rule = some head) :
    head.rule = rule ∧
      parameterBaseSorts? rule.params = some head.childSorts := by
  unfold compileHead? at compiled
  split at compiled
  next member =>
    split at compiled
    next exactSorts => simp at compiled
    next sorts exactSorts =>
      cases Option.some.inj compiled
      exact ⟨rfl, exactSorts⟩
  next notMember => simp at compiled

/-- A compiled head cannot be detached from the source language's rule
inventory. -/
theorem compiled_head_is_source_rule (source : LanguageDef)
    (rule : GrammarRule) (head : Head source)
    (_compiled : compileHead? source rule = some head) :
    head.rule ∈ source.terms := by
  exact head.sourceMember

/-- Every parameter of the authored MM2 reader grammar is an ordinary base
sort, so the generic compiler loses no child-sort information on this source. -/
theorem mm2_all_parameters_compile :
    Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT.mm2Syntax.terms.all
      (fun rule => (parameterBaseSorts? rule.params).isSome) = true := by
  decide +kernel

private def rejectedArrowRule : GrammarRule := {
  label := "fixture-arrow"
  category := "Term"
  params := [.simple "function" (.arrow (.base "Term") (.base "Term"))]
  syntaxPattern := []
}

private def rejectedArrowLanguage : LanguageDef := {
  name := "RejectedArrowFixture"
  types := ["Term"]
  terms := [rejectedArrowRule]
  equations := []
  rewrites := []
}

/-- Negative fixture: a higher-typed parameter is rejected rather than
silently reported as a base-sorted child. -/
theorem higher_parameter_fails_closed :
    compileHead? rejectedArrowLanguage rejectedArrowRule = none := by
  rfl

/-- Negative fixture: a well-shaped rule from another language cannot be
compiled under this source identity. -/
theorem foreign_rule_fails_closed :
    let foreign : GrammarRule := {
      label := "foreign"
      category := "Term"
      params := []
      syntaxPattern := [] }
    compileHead? rejectedArrowLanguage foreign = none := by
  decide +kernel

#print axioms compileHead?_some_exact
#print axioms compiled_head_is_source_rule
#print axioms mm2_all_parameters_compile
#print axioms higher_parameter_fails_closed
#print axioms foreign_rule_fails_closed

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.LanguageDefSignature
