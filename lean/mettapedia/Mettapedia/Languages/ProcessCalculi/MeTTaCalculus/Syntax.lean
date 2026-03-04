import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RelationNames

/-!
# MeTTa-Calculus Syntax and LanguageDef

Core syntax/rewrites for the symmetric reflective MeTTa-calculus.

## Source attribution

This formalization follows the calculus specification in:

- `/home/zar/claude/hyperon/rho4u/metta-calculus/metta-calculus.core.tex`

especially the `COMM` and `REFL` rules in the "A symmetric reflective
higher order concurrent calculus with backchaining" section.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax

abbrev Proc := Pattern
abbrev Name := Pattern
abbrev Term := Pattern

/-! ## Canonical constructors -/

def pZero : Proc := .apply "MZero" []

def pPar (elems : List Proc) : Proc := .collection .hashBag elems none

def nQuote (p : Proc) : Name := .apply "MQuote" [p]

def pDrop (x : Name) : Proc := .apply "MDrop" [x]

def pFor (t : Term) (x : Name) (k : Proc) : Proc := .apply "MFor" [t, x, k]

def pReflect (x : Name) (p : Proc) : Proc := .apply "MRef" [x, p]

def tProc (p : Proc) : Term := .apply "MTermProc" [p]

def tBool (b : Bool) : Term :=
  if b then .apply "MBoolTrue" [] else .apply "MBoolFalse" []

def tInt (n : Int) : Term := .apply "MInt" [.apply s!"{n}" []]

def tString (s : String) : Term := .apply "MString" [.apply s []]

def tSym (s : String) : Term := .apply s []

def par (p q : Proc) : Proc := pPar [p, q]

infixl:60 " ∥ " => par

/-! ## Rewrite rules -/

private def commSymRule : RewriteRule := {
  name := "CommSym"
  typeContext := [("t", .base "Term"), ("u", .base "Term"), ("x", .base "Name"),
                  ("p", .base "Proc"), ("q", .base "Proc"),
                  ("pOut", .base "Proc"), ("qOut", .base "Proc")]
  premises := [
    .relationQuery relMettaComm
      [.fvar "t", .fvar "u", .fvar "p", .fvar "q", .fvar "pOut", .fvar "qOut"]
  ]
  left := .collection .hashBag [
    .apply "MFor" [.fvar "t", .fvar "x", .fvar "p"],
    .apply "MFor" [.fvar "u", .fvar "x", .fvar "q"]
  ] (some "rest")
  right := .collection .hashBag [.fvar "pOut", .fvar "qOut"] (some "rest")
}

private def reflRule : RewriteRule := {
  name := "Refl"
  typeContext := [("x", .base "Name"), ("p", .base "Proc"), ("pNext", .base "Proc")]
  premises := [.relationQuery relMettaStepNoReflect [.fvar "p", .fvar "pNext"]]
  left := .apply "MRef" [.fvar "x", .fvar "p"]
  right := .apply "MFor" [.apply "MTermProc" [.fvar "pNext"], .fvar "x", .apply "MZero" []]
}

/-! ## Language definitions -/

/-- Full MeTTa-calculus language (COMM + REFL). -/
def mettaCalc : LanguageDef := {
  name := "MeTTaCalc"
  types := ["Proc", "Name", "Term"]
  congruenceCollections := [.hashBag]
  terms := [
    { label := "MZero", category := "Proc", params := [],
      syntaxPattern := [.terminal "0"] },
    { label := "MFor", category := "Proc",
      params := [.simple "t" (.base "Term"), .simple "x" (.base "Name"),
                 .simple "k" (.base "Proc")],
      syntaxPattern := [.terminal "for", .terminal "(", .nonTerminal "t",
                        .terminal "<-", .nonTerminal "x", .terminal ")", .nonTerminal "k"] },
    { label := "MRef", category := "Proc",
      params := [.simple "x" (.base "Name"), .simple "p" (.base "Proc")],
      syntaxPattern := [.nonTerminal "x", .terminal "?", .nonTerminal "p"] },
    { label := "MDrop", category := "Proc",
      params := [.simple "x" (.base "Name")],
      syntaxPattern := [.terminal "*", .nonTerminal "x"] },
    { label := "MQuote", category := "Name",
      params := [.simple "p" (.base "Proc")],
      syntaxPattern := [.terminal "@", .terminal "(", .nonTerminal "p", .terminal ")"] },
    { label := "MTermProc", category := "Term",
      params := [.simple "p" (.base "Proc")],
      syntaxPattern := [.terminal "(", .nonTerminal "p", .terminal ")"] },
    { label := "MBoolTrue", category := "Term", params := [],
      syntaxPattern := [.terminal "true"] },
    { label := "MBoolFalse", category := "Term", params := [],
      syntaxPattern := [.terminal "false"] },
    { label := "MInt", category := "Term", params := [.simple "n" (.base "Term")],
      syntaxPattern := [.terminal "int", .terminal "(", .nonTerminal "n", .terminal ")"] },
    { label := "MString", category := "Term", params := [.simple "s" (.base "Term")],
      syntaxPattern := [.terminal "str", .terminal "(", .nonTerminal "s", .terminal ")"] }
  ]
  equations := [
    { name := "QuoteDrop",
      typeContext := [("n", .base "Name")],
      premises := [],
      left := .apply "MQuote" [.apply "MDrop" [.fvar "n"]],
      right := .fvar "n" }
  ]
  rewrites := [commSymRule, reflRule]
}

/-- COMM-only fragment (used to define one-step reflection premises without
self-reference through REFL). -/
def mettaCalcCommOnly : LanguageDef :=
  { mettaCalc with
      name := "MeTTaCalcCommOnly"
      rewrites := [commSymRule] }

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
