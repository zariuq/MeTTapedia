import MeTTailCore.MeTTaIL.Syntax
import MeTTailCore.MeTTaSyntax.CommandIR

namespace MeTTailCore.MeTTaSyntax

open MeTTailCore.MeTTaIL.Syntax

/-- Lower one parsed source premise into the current structured premise subset.

Positive example: `(== $x 0)` becomes a congruence premise.
Negative example: a bare binder like `$x` is not a valid premise form here. -/
def syntaxPremise? : Pattern → Option Premise
  | .apply "==" [lhs, rhs] => some (.congruence lhs rhs)
  | .apply "fresh" [.fvar varName, term] =>
      some (.freshness { varName := varName, term := term })
  | .apply rel args => some (.relationQuery rel args)
  | _ => none

/-- Lower one parsed syntax command into a structured rewrite rule when the
command is a supported source rule form. -/
def syntaxRule? (name : String) : SyntaxCommand → Option RewriteRule
  | .defineEq lhs rhs =>
      some {
        name := name
        typeContext := []
        premises := []
        left := lhs
        right := rhs
      }
  | .defineRule lhs rhs premiseTerms => do
      let premises ← premiseTerms.mapM syntaxPremise?
      some {
        name := name
        typeContext := []
        premises := premises
        left := lhs
        right := rhs
      }
  | _ => none

theorem syntaxPremise_congruence :
    syntaxPremise? (.apply "==" [.fvar "x", .apply "0" []]) =
      some (.congruence (.fvar "x") (.apply "0" [])) := by
  rfl

theorem syntaxPremise_freshness :
    syntaxPremise? (.apply "fresh" [.fvar "z", .apply "pair" [.fvar "x", .apply "0" []]]) =
      some (.freshness {
        varName := "z"
        term := .apply "pair" [.fvar "x", .apply "0" []]
      }) := by
  rfl

theorem syntaxRule_defineRule :
    syntaxRule? "rule1"
        (.defineRule
          (.apply "pick" [.fvar "x"])
          (.fvar "y")
          [ .apply "spaceMatch" [.apply "score" [.fvar "x", .fvar "z"], .fvar "z", .fvar "y"] ]) =
      some {
        name := "rule1"
        typeContext := []
        premises := [ .relationQuery "spaceMatch"
          [ .apply "score" [.fvar "x", .fvar "z"], .fvar "z", .fvar "y" ] ]
        left := .apply "pick" [.fvar "x"]
        right := .fvar "y"
      } := by
  rfl

theorem syntaxRule_rejects_bare_premise :
    syntaxRule? "rule2"
        (.defineRule (.apply "f" [.fvar "x"]) (.apply "1" []) [.fvar "x"]) = none := by
  rfl

end MeTTailCore.MeTTaSyntax
