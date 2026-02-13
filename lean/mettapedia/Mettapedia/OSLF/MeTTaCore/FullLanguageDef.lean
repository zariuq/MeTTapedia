import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaCore.Premises

/-!
# MeTTa Full LanguageDef (First Spec-Facing Slice)

This module provides a first `LanguageDef` client aimed at fuller MeTTa-style
machine semantics:

- explicit `State` sort
- premise-driven equation lookup (`eqnLookup`) with explicit miss branch
- core instruction branches (`Eval`, `Unify`, `Chain`, `Return`)
- spec-facing premise hooks (`typeOf`, `cast`, `groundedCall`)
- executable relation environment parameterized by query arguments

This is intentionally small but spec-facing, and is suitable as the first
increment toward a fuller MeTTa-as-GSLT client.
-/

namespace Mettapedia.OSLF.MeTTaCore.FullLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- First full-oriented MeTTa machine language slice. -/
def mettaFull : LanguageDef := {
  name := "MeTTaFullState",
  types := ["State", "Instr", "Atom", "Space"],
  terms := [
    { label := "State", category := "State",
      params := [ .simple "instr" (.base "Instr")
                , .simple "space" (.base "Space")
                , .simple "out" (.base "Atom") ],
      syntaxPattern := [.terminal "<", .nonTerminal "instr", .terminal "|",
                        .nonTerminal "space", .terminal "|", .nonTerminal "out",
                        .terminal ">"] },
    { label := "Eval", category := "Instr",
      params := [.simple "src" (.base "Atom")],
      syntaxPattern := [.terminal "eval", .terminal "(", .nonTerminal "src", .terminal ")"] },
    { label := "Unify", category := "Instr",
      params := [.simple "lhs" (.base "Atom"), .simple "rhs" (.base "Atom")],
      syntaxPattern := [.terminal "unify", .terminal "(", .nonTerminal "lhs", .terminal ",",
                        .nonTerminal "rhs", .terminal ")"] },
    { label := "Chain", category := "Instr",
      params := [.simple "src" (.base "Atom"), .simple "tmpl" (.base "Atom")],
      syntaxPattern := [.terminal "chain", .terminal "(", .nonTerminal "src", .terminal ",",
                        .nonTerminal "tmpl", .terminal ")"] },
    { label := "TypeCheck", category := "Instr",
      params := [.simple "atom" (.base "Atom"), .simple "ty" (.base "Atom")],
      syntaxPattern := [.terminal "type-of", .terminal "(",
                        .nonTerminal "atom", .terminal ",", .nonTerminal "ty", .terminal ")"] },
    { label := "Cast", category := "Instr",
      params := [.simple "atom" (.base "Atom"), .simple "ty" (.base "Atom")],
      syntaxPattern := [.terminal "cast", .terminal "(",
                        .nonTerminal "atom", .terminal ",", .nonTerminal "ty", .terminal ")"] },
    { label := "Grounded1", category := "Instr",
      params := [.simple "op" (.base "Atom"), .simple "arg" (.base "Atom")],
      syntaxPattern := [.terminal "grounded1", .terminal "(",
                        .nonTerminal "op", .terminal ",", .nonTerminal "arg", .terminal ")"] },
    { label := "Grounded2", category := "Instr",
      params := [.simple "op" (.base "Atom"), .simple "lhs" (.base "Atom"),
                 .simple "rhs" (.base "Atom")],
      syntaxPattern := [.terminal "grounded2", .terminal "(",
                        .nonTerminal "op", .terminal ",",
                        .nonTerminal "lhs", .terminal ",",
                        .nonTerminal "rhs", .terminal ")"] },
    { label := "Return", category := "Instr",
      params := [.simple "dst" (.base "Atom")],
      syntaxPattern := [.terminal "return", .terminal "(", .nonTerminal "dst", .terminal ")"] },
    { label := "Done", category := "Instr", params := [],
      syntaxPattern := [.terminal "done"] },
    { label := "ATrue", category := "Atom", params := [],
      syntaxPattern := [.terminal "true"] },
    { label := "AFalse", category := "Atom", params := [],
      syntaxPattern := [.terminal "false"] },
    { label := "GBoolTrue", category := "Atom", params := [],
      syntaxPattern := [.terminal "gtrue"] },
    { label := "GBoolFalse", category := "Atom", params := [],
      syntaxPattern := [.terminal "gfalse"] },
    { label := "Bool", category := "Atom", params := [],
      syntaxPattern := [.terminal "Bool"] },
    { label := "Atom", category := "Atom", params := [],
      syntaxPattern := [.terminal "Atom"] },
    { label := "not", category := "Atom", params := [],
      syntaxPattern := [.terminal "not"] },
    { label := "and", category := "Atom", params := [],
      syntaxPattern := [.terminal "and"] },
    { label := "or", category := "Atom", params := [],
      syntaxPattern := [.terminal "or"] },
    { label := "xor", category := "Atom", params := [],
      syntaxPattern := [.terminal "xor"] },
    { label := "eqBool", category := "Atom", params := [],
      syntaxPattern := [.terminal "eqBool"] },
    { label := "Space0", category := "Space", params := [],
      syntaxPattern := [.terminal "space0"] }
  ],
  equations := [],
  rewrites := [
    -- spec-facing equation application: lookup in current atomspace/space
    { name := "StepApplyEquation",
      typeContext := [ ("src", .base "Atom"), ("dst", .base "Atom")
                     , ("out", .base "Atom"), ("space", .base "Space") ],
      premises := [.relationQuery "eqnLookup" [.fvar "space", .fvar "src", .fvar "dst"]],
      left := .apply "State" [.apply "Eval" [.fvar "src"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "dst"], .fvar "space", .fvar "dst"] },
    -- explicit fallback: no equation match keeps source
    { name := "StepApplyEquationFallback",
      typeContext := [("src", .base "Atom"), ("out", .base "Atom"), ("space", .base "Space")],
      premises := [.relationQuery "noEqnLookup" [.fvar "space", .fvar "src"]],
      left := .apply "State" [.apply "Eval" [.fvar "src"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "src"], .fvar "space", .fvar "src"] },
    -- unify hit branch
    { name := "StepUnifyHit",
      typeContext := [("lhs", .base "Atom"), ("rhs", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "eq" [.fvar "lhs", .fvar "rhs"]],
      left := .apply "State" [.apply "Unify" [.fvar "lhs", .fvar "rhs"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "ATrue" []], .fvar "space", .apply "ATrue" []] },
    -- unify miss branch
    { name := "StepUnifyMiss",
      typeContext := [("lhs", .base "Atom"), ("rhs", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "neq" [.fvar "lhs", .fvar "rhs"]],
      left := .apply "State" [.apply "Unify" [.fvar "lhs", .fvar "rhs"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "AFalse" []], .fvar "space", .apply "AFalse" []] },
    -- chain hit branch via equation lookup on source atom
    { name := "StepChainHit",
      typeContext := [("src", .base "Atom"), ("tmpl", .base "Atom"), ("dst", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "eqnLookup" [.fvar "space", .fvar "src", .fvar "dst"]],
      left := .apply "State" [.apply "Chain" [.fvar "src", .fvar "tmpl"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "dst"], .fvar "space", .fvar "dst"] },
    -- chain miss branch falls back to template
    { name := "StepChainFallback",
      typeContext := [("src", .base "Atom"), ("tmpl", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "noEqnLookup" [.fvar "space", .fvar "src"]],
      left := .apply "State" [.apply "Chain" [.fvar "src", .fvar "tmpl"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "tmpl"], .fvar "space", .fvar "tmpl"] },
    -- type-check hit/miss branches via premise environment
    { name := "StepTypeCheckHit",
      typeContext := [("atom", .base "Atom"), ("ty", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "typeOf" [.fvar "space", .fvar "atom", .fvar "ty"]],
      left := .apply "State" [.apply "TypeCheck" [.fvar "atom", .fvar "ty"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "ATrue" []], .fvar "space", .apply "ATrue" []] },
    { name := "StepTypeCheckMiss",
      typeContext := [("atom", .base "Atom"), ("ty", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "notTypeOf" [.fvar "space", .fvar "atom", .fvar "ty"]],
      left := .apply "State" [.apply "TypeCheck" [.fvar "atom", .fvar "ty"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "AFalse" []], .fvar "space", .apply "AFalse" []] },
    -- cast hit/miss branches
    { name := "StepCastHit",
      typeContext := [("atom", .base "Atom"), ("ty", .base "Atom"), ("casted", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "cast" [.fvar "space", .fvar "atom", .fvar "ty", .fvar "casted"]],
      left := .apply "State" [.apply "Cast" [.fvar "atom", .fvar "ty"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "casted"], .fvar "space", .fvar "casted"] },
    { name := "StepCastMiss",
      typeContext := [("atom", .base "Atom"), ("ty", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "notCast" [.fvar "space", .fvar "atom", .fvar "ty"]],
      left := .apply "State" [.apply "Cast" [.fvar "atom", .fvar "ty"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "AFalse" []], .fvar "space", .apply "AFalse" []] },
    -- grounded op branches
    { name := "StepGrounded1Hit",
      typeContext := [("op", .base "Atom"), ("arg", .base "Atom"), ("result", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "groundedCall" [.fvar "op", .fvar "arg", .fvar "result"]],
      left := .apply "State" [.apply "Grounded1" [.fvar "op", .fvar "arg"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "result"], .fvar "space", .fvar "result"] },
    { name := "StepGrounded1Miss",
      typeContext := [("op", .base "Atom"), ("arg", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "noGroundedCall" [.fvar "op", .fvar "arg"]],
      left := .apply "State" [.apply "Grounded1" [.fvar "op", .fvar "arg"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "AFalse" []], .fvar "space", .apply "AFalse" []] },
    { name := "StepGrounded2Hit",
      typeContext := [("op", .base "Atom"), ("lhs", .base "Atom"), ("rhs", .base "Atom"),
                      ("result", .base "Atom"), ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "groundedCall" [.fvar "op", .fvar "lhs", .fvar "rhs", .fvar "result"]],
      left := .apply "State" [.apply "Grounded2" [.fvar "op", .fvar "lhs", .fvar "rhs"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "result"], .fvar "space", .fvar "result"] },
    { name := "StepGrounded2Miss",
      typeContext := [("op", .base "Atom"), ("lhs", .base "Atom"), ("rhs", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "noGroundedCall" [.fvar "op", .fvar "lhs", .fvar "rhs"]],
      left := .apply "State" [.apply "Grounded2" [.fvar "op", .fvar "lhs", .fvar "rhs"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "AFalse" []], .fvar "space", .apply "AFalse" []] },
    -- observable commit of return value
    { name := "StepReturn",
      typeContext := [("dst", .base "Atom"), ("space", .base "Space"), ("out", .base "Atom")],
      premises := [],
      left := .apply "State" [.apply "Return" [.fvar "dst"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Done" [], .fvar "space", .fvar "dst"] }
  ]
}

/-- OSLF synthesis for the first full-oriented MeTTa language slice. -/
def mettaFullOSLF := langOSLF mettaFull "State"

/-- Automatic modal Galois connection from the generic pipeline. -/
theorem mettaFullGalois :
    GaloisConnection (langDiamond mettaFull) (langBox mettaFull) :=
  langGalois mettaFull

private def aTrue : Pattern := .apply "ATrue" []
private def aFalse : Pattern := .apply "AFalse" []
private def space0 : Pattern := .apply "Space0" []

private def mkState (instr : Pattern) (space : Pattern := space0) (out : Pattern := aFalse) : Pattern :=
  .apply "State" [instr, space, out]

private def iEval (a : Pattern) : Pattern := .apply "Eval" [a]
private def iUnify (lhs rhs : Pattern) : Pattern := .apply "Unify" [lhs, rhs]
private def iChain (src tmpl : Pattern) : Pattern := .apply "Chain" [src, tmpl]
private def iTypeCheck (atom ty : Pattern) : Pattern := .apply "TypeCheck" [atom, ty]
private def iCast (atom ty : Pattern) : Pattern := .apply "Cast" [atom, ty]
private def iGrounded1 (op arg : Pattern) : Pattern := .apply "Grounded1" [op, arg]
private def iGrounded2 (op lhs rhs : Pattern) : Pattern := .apply "Grounded2" [op, lhs, rhs]

/-- Full-slice relation environment (Atomspace-backed eqnLookup + branches). -/
def mettaFullRelEnv : RelationEnv := Mettapedia.OSLF.MeTTaCore.Premises.mettaFullRelEnv

-- Smoke check: one equation-application step from Eval(true).
#eval! do
  let s := mkState (iEval aTrue) space0 aFalse
  let reducts := rewriteWithContextWithPremisesUsing mettaFullRelEnv mettaFull s
  IO.println s!"MeTTaFull demo (eqnLookup true -> false): reduct count = {reducts.length}"

-- Smoke check: two-step run (apply equation + return commit) to Done(false).
#eval! do
  let s := mkState (iEval aTrue) space0 aFalse
  let nf := fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull s 8
  IO.println s!"MeTTaFull demo normal form: {nf}"

-- Smoke check: unify hit and miss branches.
#eval! do
  let hit := mkState (iUnify aTrue aTrue) space0 aFalse
  let miss := mkState (iUnify aTrue aFalse) space0 aFalse
  let hitNF := fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull hit 8
  let missNF := fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull miss 8
  IO.println s!"MeTTaFull unify hit normal form: {hitNF}"
  IO.println s!"MeTTaFull unify miss normal form: {missNF}"

-- Smoke check: chain hit and fallback branches.
#eval! do
  let hit := mkState (iChain aTrue aTrue) space0 aFalse
  let miss := mkState (iChain (.apply "AUnknown" []) aTrue) space0 aFalse
  let hitNF := fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull hit 8
  let missNF := fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull miss 8
  IO.println s!"MeTTaFull chain hit normal form: {hitNF}"
  IO.println s!"MeTTaFull chain fallback normal form: {missNF}"

-- Smoke check: typeOf and cast hooks.
#eval! do
  let tCheckHit := mkState (iTypeCheck aTrue (.apply "Bool" [])) space0 aFalse
  let tCheckMiss := mkState (iTypeCheck (.apply "AUnknown" []) (.apply "Bool" [])) space0 aFalse
  let castHit := mkState (iCast aTrue (.apply "Bool" [])) space0 aFalse
  let castMiss := mkState (iCast (.apply "AUnknown" []) (.apply "Bool" [])) space0 aFalse
  IO.println s!"MeTTaFull typeOf hit: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull tCheckHit 8}"
  IO.println s!"MeTTaFull typeOf miss: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull tCheckMiss 8}"
  IO.println s!"MeTTaFull cast hit: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull castHit 8}"
  IO.println s!"MeTTaFull cast miss: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull castMiss 8}"

-- Smoke check: grounded boolean operations.
#eval! do
  let gNot := mkState (iGrounded1 (.apply "not" []) aTrue) space0 aFalse
  let gAnd := mkState (iGrounded2 (.apply "and" []) aTrue aFalse) space0 aFalse
  let gMiss := mkState (iGrounded2 (.apply "unknownOp" []) aTrue aFalse) space0 aFalse
  IO.println s!"MeTTaFull grounded not: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull gNot 8}"
  IO.println s!"MeTTaFull grounded and: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull gAnd 8}"
  IO.println s!"MeTTaFull grounded miss: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull gMiss 8}"

#check mettaFullOSLF
#check mettaFullGalois

end Mettapedia.OSLF.MeTTaCore.FullLanguageDef
