import Mettapedia.Languages.KIF.DeclarationDecode

/-!
# Logical-form audit for SUO-KIF

This pass checks the fixed syntax of logical connectives and quantifiers while
leaving ontology-specific relations and functions untouched. It catches forms
that a balanced S-expression parser must accept but a KIF elaborator cannot:
wrong connective arities, malformed binder lists, and the common `exist` /
`exists` typo.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.KIF

inductive LogicalSyntaxIssueKind : Type
  | wrongArity (head : String) (expected actual : Nat)
  | malformedBinderList (quantifier : String)
  | misspelledExists
  | internalFuelExhausted
  deriving DecidableEq, Repr

structure LogicalSyntaxIssue where
  kind : LogicalSyntaxIssueKind
  span : SourceSpan
  deriving DecidableEq, Repr

private def binderVariable : Term → Bool
  | .atom value =>
      value.kind = .regularVariable || value.kind = .sequenceVariable
  | .list _ _ => false

private def binderListValid : Term → Bool
  | .list _ variables => !variables.isEmpty && variables.all binderVariable
  | .atom _ => false

private def localIssues (term : Term) : List LogicalSyntaxIssue :=
  match term with
  | .atom _ => []
  | .list _ [] => []
  | .list _ (headTerm :: arguments) =>
      match headTerm.asSymbol? with
      | none => []
      | some head =>
          let exactArity (expected : Nat) :=
            if arguments.length = expected then []
            else [⟨.wrongArity head.text expected arguments.length, head.span⟩]
          match head.text with
          | "not" => exactArity 1
          | "=>" | "<=>" => exactArity 2
          | "forall" | "exists" =>
              let arityIssues := exactArity 2
              let binderIssues :=
                match arguments with
                | binder :: _ =>
                    if binderListValid binder then []
                    else [⟨.malformedBinderList head.text, binder.span⟩]
                | [] => []
              arityIssues ++ binderIssues
          | "exist" => [⟨.misspelledExists, head.span⟩]
          | _ => []

mutual
  private def auditTerm : Nat → Term → List LogicalSyntaxIssue
    | 0, term => [⟨.internalFuelExhausted, term.span⟩]
    | fuel + 1, term =>
        match term with
        | .atom _ => []
        | .list _ children => localIssues term ++ auditTerms fuel children

  private def auditTerms : Nat → List Term → List LogicalSyntaxIssue
    | _, [] => []
    | fuel, term :: rest => auditTerm fuel term ++ auditTerms fuel rest
end

/-- Audit every parsed form. Supplying at least the lexical token count gives
strictly more fuel than any AST nesting path. -/
def logicalSyntaxIssues (fuel : Nat) (parsed : Parsed) : List LogicalSyntaxIssue :=
  auditTerms fuel parsed.forms

private def canaryPos : SourcePos := ⟨0, 1, 1⟩
private def canarySpan : SourceSpan := ⟨canaryPos, canaryPos⟩
private def canarySymbol (text : String) : Term :=
  .atom ⟨.symbol, text, canarySpan⟩
private def canaryVariable (text : String) : Term :=
  .atom ⟨.regularVariable, text, canarySpan⟩
private def canaryRowVariable (text : String) : Term :=
  .atom ⟨.sequenceVariable, text, canarySpan⟩
private def canaryList (children : List Term) : Term :=
  .list canarySpan children
private def canaryCall (head : String) (arguments : List Term) : Term :=
  canaryList (canarySymbol head :: arguments)

example :
    localIssues
      (canaryCall "forall"
        [canaryList [canaryVariable "?x", canaryVariable "?y"],
          canaryCall "=>" [canaryCall "P" [], canaryCall "Q" []]]) = [] := by
  rfl

example :
    localIssues
      (canaryCall "forall"
        [canaryList [canaryRowVariable "@ROW", canaryVariable "?item"],
          canaryCall "P" [canaryRowVariable "@ROW", canaryVariable "?item"]]) =
      [] := by
  rfl

example :
    (localIssues
      (canaryCall "=>"
        [canaryCall "P" [], canaryCall "Q" [], canaryCall "R" []])).map
        (·.kind) = [.wrongArity "=>" 2 3] := by
  rfl

example :
    (localIssues
      (canaryCall "exists"
        [canaryVariable "?x", canaryCall "P" [canaryVariable "?x"]])).map
        (·.kind) = [.malformedBinderList "exists"] := by
  rfl

example :
    (localIssues
      (canaryCall "exist"
        [canaryList [canaryVariable "?x"],
          canaryCall "P" [canaryVariable "?x"]])).map
        (·.kind) = [.misspelledExists] := by
  rfl

end Mettapedia.Languages.KIF
