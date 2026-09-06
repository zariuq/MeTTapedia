import Mettapedia.Languages.KIF.Parser

/-!
# Source-layout audit for KIF nesting

Parenthesis balance alone cannot detect a missing close that is later canceled
by an unrelated surplus close. SUMO-family source files conventionally begin
each top-level form in column one and indent nested forms. This audit reports a
column-one opening parenthesis encountered while another form remains open.
It is a source-convention diagnostic, not a theorem that every KIF text must
use this layout.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.KIF

structure NestingIssue where
  span : SourceSpan
  enclosingDepth : Nat
  deriving DecidableEq, Repr

private def auditTokens : List Token → Nat → List NestingIssue → List NestingIssue
  | [], _, reversed => reversed.reverse
  | token :: rest, depth, reversed =>
      match token.kind with
      | .openParen =>
          let nextIssues :=
            if token.span.start.column = 1 && depth > 0 then
              ⟨token.span, depth⟩ :: reversed
            else reversed
          auditTokens rest (depth + 1) nextIssues
      | .closeParen => auditTokens rest (depth - 1) reversed
      | .atom _ _ | .comment _ => auditTokens rest depth reversed

/-- Column-one forms that begin while an earlier form is still open. -/
def nestingIssues (lexed : Lexed) : List NestingIssue :=
  auditTokens lexed.tokens 0 []

example :
    (lex "(outer\n  (inner))\n(next)").map nestingIssues = .ok [] := by
  rfl

example :
    (lex "(outer\n(inner))").map
        (fun lexed => (nestingIssues lexed).map (fun issue =>
          (issue.span.start.line, issue.enclosingDepth))) =
      .ok [(2, 1)] := by
  rfl

end Mettapedia.Languages.KIF
