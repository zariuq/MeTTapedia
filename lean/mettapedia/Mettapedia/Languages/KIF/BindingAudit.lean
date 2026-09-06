import Mettapedia.Languages.KIF.LogicalSyntaxAudit

/-!
# Quantifier-binding audit for SUO-KIF

SUO-KIF implicitly universally quantifies regular variables that remain free
in a top-level formula. Consequently, free variables are not rejected here.
This pass checks both regular and row binders: a quantifier may not repeat a
name within its own variable class, and every explicitly bound variable must
occur free in its body. The latter catches misspellings that implicit
top-level quantification would otherwise hide.
 -/

set_option autoImplicit false

namespace Mettapedia.Languages.KIF

inductive BindingIssueKind : Type
  | duplicateBinder (quantifier variableName : String)
  | unusedBinder (quantifier variableName : String)
  | internalFuelExhausted
  deriving DecidableEq, Repr

structure BindingIssue where
  kind : BindingIssueKind
  span : SourceSpan
  deriving DecidableEq, Repr

private def binderVariables : Term → List (String × SourceSpan)
  | .list _ variables =>
      variables.filterMap fun
        | .atom value =>
            if value.kind = .regularVariable ||
                value.kind = .sequenceVariable then
              some (value.text, value.span)
            else none
        | .list _ _ => none
  | .atom _ => []

private def quantifierParts? : Term → Option (LocatedSymbol × Term × Term)
  | .list _ [headTerm, binder, body] => do
      let head ← headTerm.asSymbol?
      if head.text = "forall" || head.text = "exists" then
        some (head, binder, body)
      else
        none
  | _ => none

mutual
  /-- Regular and row variables free in a term. At the top level these receive
  the standard SUO-KIF implicit universal closure. -/
  def freeVariables : Nat → Term → List String
    | 0, _ => []
    | fuel + 1, term =>
        match quantifierParts? term with
        | some (_, binder, body) =>
            let bound := (binderVariables binder).map (·.1)
            (freeVariables fuel body).filter fun variableName =>
              !bound.contains variableName
        | none =>
            match term with
            | .atom value =>
                if value.kind = .regularVariable ||
                    value.kind = .sequenceVariable then [value.text] else []
            | .list _ children => freeVariablesInTerms fuel children

  def freeVariablesInTerms : Nat → List Term → List String
    | _, [] => []
    | fuel, term :: rest =>
        freeVariables fuel term ++ freeVariablesInTerms fuel rest
end

private def duplicateBindingIssues
    (quantifier : LocatedSymbol) (variables : List (String × SourceSpan)) :
    List BindingIssue :=
  variables.foldl
    (fun issues binding =>
      if (variables.map (·.1)).count binding.1 > 1 &&
          !(issues.any fun issue =>
            match issue.kind with
            | .duplicateBinder _ prior => prior = binding.1
            | _ => false) then
        issues ++ [⟨.duplicateBinder quantifier.text binding.1, binding.2⟩]
      else
        issues)
    []

private def unusedBindingIssues
    (quantifier : LocatedSymbol) (variables : List (String × SourceSpan))
    (fuel : Nat) (body : Term) : List BindingIssue :=
  let freeInBody := freeVariables fuel body
  variables.filterMap fun binding =>
    if freeInBody.contains binding.1 then none
    else some ⟨.unusedBinder quantifier.text binding.1, binding.2⟩

mutual
  private def auditBindingsInTerm : Nat → Term → List BindingIssue
    | 0, term => [⟨.internalFuelExhausted, term.span⟩]
    | fuel + 1, term =>
        match quantifierParts? term with
        | some (quantifier, binder, body) =>
            let variables := binderVariables binder
            duplicateBindingIssues quantifier variables ++
              unusedBindingIssues quantifier variables fuel body ++
              auditBindingsInTerm fuel body
        | none =>
            match term with
            | .atom _ => []
            | .list _ children => auditBindingsInTerms fuel children

  private def auditBindingsInTerms : Nat → List Term → List BindingIssue
    | _, [] => []
    | fuel, term :: rest =>
        auditBindingsInTerm fuel term ++ auditBindingsInTerms fuel rest
end

/-- Check explicit quantifier binders throughout a parsed source. -/
def bindingIssues (fuel : Nat) (parsed : Parsed) : List BindingIssue :=
  auditBindingsInTerms fuel parsed.forms

private def bindingCanaryPos : SourcePos := ⟨0, 1, 1⟩
private def bindingCanarySpan : SourceSpan :=
  ⟨bindingCanaryPos, bindingCanaryPos⟩
private def bindingCanarySymbol (text : String) : Term :=
  .atom ⟨.symbol, text, bindingCanarySpan⟩
private def bindingCanaryVariable (text : String) : Term :=
  .atom ⟨.regularVariable, text, bindingCanarySpan⟩
private def bindingCanaryRowVariable (text : String) : Term :=
  .atom ⟨.sequenceVariable, text, bindingCanarySpan⟩
private def bindingCanaryList (children : List Term) : Term :=
  .list bindingCanarySpan children

private def bindingCanaryForall
    (variables : List String) (body : Term) : Term :=
  bindingCanaryList
    [bindingCanarySymbol "forall",
      bindingCanaryList (variables.map bindingCanaryVariable), body]

example :
    bindingIssues 8
      ⟨[bindingCanaryForall ["?x"]
        (bindingCanaryList
          [bindingCanarySymbol "P", bindingCanaryVariable "?x",
            bindingCanaryVariable "?free"])], []⟩ = [] := by
  simp [bindingCanaryForall, bindingCanaryList, bindingCanarySymbol,
    bindingCanaryVariable, bindingIssues, auditBindingsInTerms,
    auditBindingsInTerm, quantifierParts?, Term.asSymbol?, binderVariables,
    duplicateBindingIssues, unusedBindingIssues, freeVariables,
    freeVariablesInTerms]

example :
    (bindingIssues 8
      ⟨[bindingCanaryForall ["?x", "?x", "?unused"]
        (bindingCanaryList
          [bindingCanarySymbol "P", bindingCanaryVariable "?x"])], []⟩).map
        (·.kind) =
      [.duplicateBinder "forall" "?x", .unusedBinder "forall" "?unused"] := by
  simp [bindingCanaryForall, bindingCanaryList, bindingCanarySymbol,
    bindingCanaryVariable, bindingIssues, auditBindingsInTerms,
    auditBindingsInTerm, quantifierParts?, Term.asSymbol?, binderVariables,
    duplicateBindingIssues, unusedBindingIssues, freeVariables,
    freeVariablesInTerms]

example :
    freeVariables 8
      (bindingCanaryForall ["?x"]
        (bindingCanaryList
          [bindingCanarySymbol "P", bindingCanaryVariable "?x",
            bindingCanaryVariable "?free"])) = ["?free"] := by
  simp [bindingCanaryForall, bindingCanaryList, bindingCanarySymbol,
    bindingCanaryVariable, freeVariables, freeVariablesInTerms,
    quantifierParts?, Term.asSymbol?, binderVariables]

example :
    bindingIssues 8
      ⟨[bindingCanaryList
        [bindingCanarySymbol "forall",
          bindingCanaryList
            [bindingCanaryRowVariable "@ROW", bindingCanaryVariable "?item"],
          bindingCanaryList
            [bindingCanarySymbol "P", bindingCanaryRowVariable "@ROW",
              bindingCanaryVariable "?item"]]], []⟩ = [] := by
  simp [bindingIssues, auditBindingsInTerms, auditBindingsInTerm,
    quantifierParts?, Term.asSymbol?, binderVariables, duplicateBindingIssues,
    unusedBindingIssues, freeVariables, freeVariablesInTerms,
    bindingCanaryList, bindingCanarySymbol, bindingCanaryVariable,
    bindingCanaryRowVariable]

end Mettapedia.Languages.KIF
