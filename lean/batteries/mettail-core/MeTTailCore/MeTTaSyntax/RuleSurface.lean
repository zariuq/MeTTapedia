import MeTTailCore.MeTTaIL.Syntax
import MeTTailCore.MeTTaSyntax.CommandIR

namespace MeTTailCore.MeTTaSyntax

open MeTTailCore.MeTTaIL.Syntax

/-- Lower one parsed surface premise into the current structured premise subset.

Positive example: `(== $x 0)` becomes a congruence premise.
Negative example: a bare binder like `$x` is not a valid premise form here. -/
def surfacePremise? : Pattern → Option Premise
  | .apply "==" [lhs, rhs] => some (.congruence lhs rhs)
  | .apply "fresh" [.fvar varName, term] =>
      some (.freshness { varName := varName, term := term })
  | .apply rel args => some (.relationQuery rel args)
  | _ => none

/-- Lower one parsed syntax command into a structured rewrite rule when the
command is a supported surface rule form. -/
def surfaceRule? (name : String) : SyntaxCommand → Option RewriteRule
  | .defineEq lhs rhs =>
      some {
        name := name
        typeContext := []
        premises := []
        left := lhs
        right := rhs
      }
  | .defineRule lhs rhs premiseTerms => do
      let premises ← premiseTerms.mapM surfacePremise?
      some {
        name := name
        typeContext := []
        premises := premises
        left := lhs
        right := rhs
      }
  | _ => none

theorem surfacePremise_congruence :
    surfacePremise? (.apply "==" [.fvar "x", .apply "0" []]) =
      some (.congruence (.fvar "x") (.apply "0" [])) := by
  rfl

theorem surfacePremise_freshness :
    surfacePremise? (.apply "fresh" [.fvar "z", .apply "pair" [.fvar "x", .apply "0" []]]) =
      some (.freshness {
        varName := "z"
        term := .apply "pair" [.fvar "x", .apply "0" []]
      }) := by
  rfl

theorem surfaceRule_defineRule :
    surfaceRule? "rule1"
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

theorem surfaceRule_rejects_bare_premise :
    surfaceRule? "rule2"
        (.defineRule (.apply "f" [.fvar "x"]) (.apply "1" []) [.fvar "x"]) = none := by
  rfl

end MeTTailCore.MeTTaSyntax
