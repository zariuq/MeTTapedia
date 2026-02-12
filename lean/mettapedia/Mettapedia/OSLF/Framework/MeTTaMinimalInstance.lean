import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# MeTTa Minimal State Client (OSLF)

First concrete OSLF client that models a MeTTa-style machine state with three
core instructions:

1. `Eval`
2. `Unify`
3. `Return`

This is intentionally minimal and executable in the current `LanguageDef`
pipeline, so it can serve as the starting point for fuller MeTTa/OSLF lifting.
-/

namespace Mettapedia.OSLF.Framework.MeTTaMinimalInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- Minimal MeTTa-like state language with instruction-tagged states. -/
def mettaMinimal : LanguageDef := {
  name := "MeTTaMinimalState",
  types := ["State", "Instr", "Atom"],
  terms := [
    { label := "State", category := "State",
      params := [.simple "instr" (.base "Instr"),
                 .simple "x" (.base "Atom"),
                 .simple "y" (.base "Atom")],
      syntaxPattern := [.terminal "<", .nonTerminal "instr", .terminal "|",
                        .nonTerminal "x", .terminal "|", .nonTerminal "y", .terminal ">"] },
    { label := "Eval", category := "Instr",
      params := [.simple "a" (.base "Atom")],
      syntaxPattern := [.terminal "eval", .terminal "(", .nonTerminal "a", .terminal ")"] },
    { label := "Unify", category := "Instr",
      params := [.simple "lhs" (.base "Atom"), .simple "rhs" (.base "Atom")],
      syntaxPattern := [.terminal "unify", .terminal "(", .nonTerminal "lhs", .terminal ",",
                        .nonTerminal "rhs", .terminal ")"] },
    { label := "Return", category := "Instr",
      params := [.simple "a" (.base "Atom")],
      syntaxPattern := [.terminal "return", .terminal "(", .nonTerminal "a", .terminal ")"] },
    { label := "ATrue", category := "Atom", params := [],
      syntaxPattern := [.terminal "true"] },
    { label := "AFalse", category := "Atom", params := [],
      syntaxPattern := [.terminal "false"] }
  ],
  equations := [],
  rewrites := [
    -- eval(a) transitions to return(a)
    { name := "StepEval",
      typeContext := [("a", .base "Atom"), ("x", .base "Atom"), ("y", .base "Atom")],
      premises := [],
      left := .apply "State" [.apply "Eval" [.fvar "a"], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Return" [.fvar "a"], .fvar "x", .fvar "y"] },

    -- unify(lhs, rhs) hit branch, premise-checked via built-in eq relation
    { name := "StepUnifyHit",
      typeContext := [("lhs", .base "Atom"), ("rhs", .base "Atom"),
                      ("x", .base "Atom"), ("y", .base "Atom")],
      premises := [.relationQuery "eq" [.fvar "lhs", .fvar "rhs"]],
      left := .apply "State" [.apply "Unify" [.fvar "lhs", .fvar "rhs"], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Return" [.apply "ATrue" []], .fvar "x", .fvar "y"] },

    -- unify(lhs, rhs) miss branch, supplied via external relation env
    { name := "StepUnifyMiss",
      typeContext := [("lhs", .base "Atom"), ("rhs", .base "Atom"),
                      ("x", .base "Atom"), ("y", .base "Atom")],
      premises := [.relationQuery "neq" [.fvar "lhs", .fvar "rhs"]],
      left := .apply "State" [.apply "Unify" [.fvar "lhs", .fvar "rhs"], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Return" [.apply "AFalse" []], .fvar "x", .fvar "y"] },

    -- return(false) is a stable observable endpoint marker
    { name := "ReturnStable",
      typeContext := [("x", .base "Atom"), ("y", .base "Atom")],
      premises := [],
      left := .apply "State" [.apply "Return" [.apply "AFalse" []], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Return" [.apply "AFalse" []], .fvar "x", .fvar "y"] }
  ]
}

/-- OSLF synthesis for the minimal MeTTa client (`State` process sort). -/
def mettaMinimalOSLF := langOSLF mettaMinimal "State"

/-- Automatic modal Galois connection for the minimal MeTTa client. -/
theorem mettaMinimalGalois :
    GaloisConnection (langDiamond mettaMinimal) (langBox mettaMinimal) :=
  langGalois mettaMinimal

/-- Example state constructor for executable smoke checks. -/
private def mkState (instr x y : Pattern) : Pattern :=
  .apply "State" [instr, x, y]

/-- `eval` instruction builder. -/
private def iEval (a : Pattern) : Pattern := .apply "Eval" [a]

/-- `unify` instruction builder. -/
private def iUnify (a b : Pattern) : Pattern := .apply "Unify" [a, b]

/-- External relation environment for explicit `neq` branch coverage. -/
private def mettaMinimalRelEnv : RelationEnv where
  tuples := fun rel =>
    if rel = "neq" then
      [ [Pattern.apply "ATrue" [], Pattern.apply "AFalse" []]
      , [Pattern.apply "AFalse" [], Pattern.apply "ATrue" []]
      ]
    else
      []

-- Smoke check 1: eval state has a one-step reduct.
#eval! do
  let a : Pattern := Pattern.apply "ATrue" []
  let s := mkState (iEval a) (Pattern.apply "AFalse" []) a
  let reducts := rewriteWithContextWithPremises mettaMinimal s
  IO.println s!"MeTTaMinimal demo (eval): reduct count = {reducts.length}"

-- Smoke check 2: unify(a,a) state has at least one reduct (hit branch).
#eval! do
  let a : Pattern := Pattern.apply "ATrue" []
  let s := mkState (iUnify a a) (Pattern.apply "AFalse" []) a
  let reducts := rewriteWithContextWithPremises mettaMinimal s
  IO.println s!"MeTTaMinimal demo (unify hit): reduct count = {reducts.length}"

-- Smoke check 3: unify(true,false) miss branch via external `neq` relation env.
#eval! do
  let t : Pattern := Pattern.apply "ATrue" []
  let f : Pattern := Pattern.apply "AFalse" []
  let s := mkState (iUnify t f) f t
  let reducts := rewriteWithContextWithPremisesUsing mettaMinimalRelEnv mettaMinimal s
  IO.println s!"MeTTaMinimal demo (unify miss via env): reduct count = {reducts.length}"

-- Verify instance and theorem are available.
#check mettaMinimalOSLF
#check mettaMinimalGalois

end Mettapedia.OSLF.Framework.MeTTaMinimalInstance
