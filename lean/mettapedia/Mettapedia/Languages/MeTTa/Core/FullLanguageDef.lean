import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.Languages.MeTTa.Core.Premises

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

namespace Mettapedia.Languages.MeTTa.Core.FullLanguageDef

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
    { label := "Match", category := "Instr",
      params := [.simple "lhs" (.base "Atom"), .simple "rhs" (.base "Atom")],
      syntaxPattern := [.terminal "match", .terminal "(", .nonTerminal "lhs", .terminal ",",
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
    -- Conditional branching (aligned with Rust MeTTaFullState)
    { label := "If", category := "Instr",
      params := [.simple "cond" (.base "Atom"), .simple "thenVal" (.base "Atom"),
                 .simple "elseVal" (.base "Atom")],
      syntaxPattern := [.terminal "if", .terminal "(", .nonTerminal "cond", .terminal ",",
                        .nonTerminal "thenVal", .terminal ",",
                        .nonTerminal "elseVal", .terminal ")"] },
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
    -- Integer/comparison/string op symbols (aligned with Rust MeTTaFullState)
    { label := "add", category := "Atom", params := [],
      syntaxPattern := [.terminal "add"] },
    { label := "sub", category := "Atom", params := [],
      syntaxPattern := [.terminal "sub"] },
    { label := "mul", category := "Atom", params := [],
      syntaxPattern := [.terminal "mul"] },
    { label := "div", category := "Atom", params := [],
      syntaxPattern := [.terminal "div"] },
    { label := "modOp", category := "Atom", params := [],
      syntaxPattern := [.terminal "modOp"] },
    { label := "lt", category := "Atom", params := [],
      syntaxPattern := [.terminal "lt"] },
    { label := "le", category := "Atom", params := [],
      syntaxPattern := [.terminal "le"] },
    { label := "gt", category := "Atom", params := [],
      syntaxPattern := [.terminal "gt"] },
    { label := "ge", category := "Atom", params := [],
      syntaxPattern := [.terminal "ge"] },
    { label := "eqInt", category := "Atom", params := [],
      syntaxPattern := [.terminal "eqInt"] },
    { label := "concat", category := "Atom", params := [],
      syntaxPattern := [.terminal "concat"] },
    { label := "length", category := "Atom", params := [],
      syntaxPattern := [.terminal "length"] },
    -- Cons-list encoding for Space contents (aligned with Rust MeTTaFullState)
    { label := "ANil", category := "Atom", params := [],
      syntaxPattern := [.terminal "nil"] },
    { label := "ACons", category := "Atom",
      params := [.simple "head" (.base "Atom"), .simple "tail" (.base "Atom")],
      syntaxPattern := [.terminal "cons", .terminal "(", .nonTerminal "head", .terminal ",",
                        .nonTerminal "tail", .terminal ")"] },
    { label := "AEqEntry", category := "Atom",
      params := [.simple "src" (.base "Atom"), .simple "dst" (.base "Atom")],
      syntaxPattern := [.terminal "eq-entry", .terminal "(", .nonTerminal "src", .terminal ",",
                        .nonTerminal "dst", .terminal ")"] },
    { label := "ATypeEntry", category := "Atom",
      params := [.simple "atom" (.base "Atom"), .simple "ty" (.base "Atom")],
      syntaxPattern := [.terminal "type-entry", .terminal "(", .nonTerminal "atom", .terminal ",",
                        .nonTerminal "ty", .terminal ")"] },
    { label := "GInt", category := "Atom",
      params := [.simple "token" (.base "Atom")],
      syntaxPattern := [.terminal "gint", .terminal "(", .nonTerminal "token", .terminal ")"] },
    { label := "GString", category := "Atom",
      params := [.simple "token" (.base "Atom")],
      syntaxPattern := [.terminal "gstring", .terminal "(", .nonTerminal "token", .terminal ")"] },
    { label := "GStringVec", category := "Atom",
      params := [.simple "chunks" (.base "Atom")],
      syntaxPattern := [.terminal "gstring-vec", .terminal "(", .nonTerminal "chunks", .terminal ")"] },
    { label := "GStringCodes", category := "Atom",
      params := [.simple "codes" (.base "Atom")],
      syntaxPattern := [.terminal "gstring-codes", .terminal "(", .nonTerminal "codes", .terminal ")"] },
    -- User-defined symbol atom.  Preserves the symbol/string distinction:
    -- UserAtom wraps a GStringCodes name so that (= foo 1) and (= "foo" 1) are different.
    { label := "UserAtom", category := "Atom",
      params := [.simple "name" (.base "Atom")],
      syntaxPattern := [.terminal "user-atom", .terminal "(", .nonTerminal "name", .terminal ")"] },
    -- Space uses cons-list encoded Atom fields (aligned with Rust MeTTaFullState)
    { label := "Space", category := "Space",
      params := [ .simple "eqs" (.base "Atom")
                , .simple "tys" (.base "Atom") ],
      syntaxPattern := [.terminal "space", .terminal "(",
                        .nonTerminal "eqs", .terminal ",",
                        .nonTerminal "tys", .terminal ")"] }
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
    -- match hit/miss branches (first-class instruction, reusing structural eq/neq premises)
    { name := "StepMatchHit",
      typeContext := [("lhs", .base "Atom"), ("rhs", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "eq" [.fvar "lhs", .fvar "rhs"]],
      left := .apply "State" [.apply "Match" [.fvar "lhs", .fvar "rhs"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "ATrue" []], .fvar "space", .apply "ATrue" []] },
    { name := "StepMatchMiss",
      typeContext := [("lhs", .base "Atom"), ("rhs", .base "Atom"),
                      ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "neq" [.fvar "lhs", .fvar "rhs"]],
      left := .apply "State" [.apply "Match" [.fvar "lhs", .fvar "rhs"], .fvar "space", .fvar "out"],
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
      right := .apply "State" [.apply "Done" [], .fvar "space", .fvar "dst"] },
    -- conditional branching (aligned with Rust MeTTaFullState R15-R17)
    { name := "StepIfTrue",
      typeContext := [("cond", .base "Atom"), ("thenVal", .base "Atom"),
                      ("elseVal", .base "Atom"), ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "eq" [.fvar "cond", .apply "GBoolTrue" []]],
      left := .apply "State" [.apply "If" [.fvar "cond", .fvar "thenVal", .fvar "elseVal"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "thenVal"], .fvar "space", .fvar "thenVal"] },
    { name := "StepIfFalse",
      typeContext := [("cond", .base "Atom"), ("thenVal", .base "Atom"),
                      ("elseVal", .base "Atom"), ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "eq" [.fvar "cond", .apply "GBoolFalse" []]],
      left := .apply "State" [.apply "If" [.fvar "cond", .fvar "thenVal", .fvar "elseVal"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "elseVal"], .fvar "space", .fvar "elseVal"] },
    { name := "StepIfNonBool",
      typeContext := [("cond", .base "Atom"), ("thenVal", .base "Atom"),
                      ("elseVal", .base "Atom"), ("space", .base "Space"), ("out", .base "Atom")],
      premises := [.relationQuery "nonBoolAtom" [.fvar "cond"]],
      left := .apply "State" [.apply "If" [.fvar "cond", .fvar "thenVal", .fvar "elseVal"], .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "AFalse" []], .fvar "space", .apply "AFalse" []] }
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
private def space0 : Pattern := Mettapedia.Languages.MeTTa.Core.Premises.space0Pattern
private def gInt (n : Int) : Pattern := .apply "GInt" [(.apply s!"{n}" [])]
private def gString (s : String) : Pattern := .apply "GString" [(.apply s [])]

private def mkState (instr : Pattern) (space : Pattern := space0) (out : Pattern := aFalse) : Pattern :=
  .apply "State" [instr, space, out]

private def iEval (a : Pattern) : Pattern := .apply "Eval" [a]
private def iUnify (lhs rhs : Pattern) : Pattern := .apply "Unify" [lhs, rhs]
private def iMatch (lhs rhs : Pattern) : Pattern := .apply "Match" [lhs, rhs]
private def iChain (src tmpl : Pattern) : Pattern := .apply "Chain" [src, tmpl]
private def iTypeCheck (atom ty : Pattern) : Pattern := .apply "TypeCheck" [atom, ty]
private def iCast (atom ty : Pattern) : Pattern := .apply "Cast" [atom, ty]
private def iGrounded1 (op arg : Pattern) : Pattern := .apply "Grounded1" [op, arg]
private def iGrounded2 (op lhs rhs : Pattern) : Pattern := .apply "Grounded2" [op, lhs, rhs]
private def iIf (cond thenVal elseVal : Pattern) : Pattern := .apply "If" [cond, thenVal, elseVal]
private def gBoolTrue : Pattern := .apply "GBoolTrue" []
private def gBoolFalse : Pattern := .apply "GBoolFalse" []
private def gStringCodes (codes : List String) : Pattern :=
  .apply "GStringCodes" [codes.foldr (fun tok acc => .apply "ACons" [.apply tok [], acc]) (.apply "ANil" [])]

/-- Full-slice relation environment (Atomspace-backed eqnLookup + branches). -/
def mettaFullRelEnv : RelationEnv := Mettapedia.Languages.MeTTa.Core.Premises.mettaFullRelEnv

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

-- Smoke check: match hit and miss branches.
#eval! do
  let hit := mkState (iMatch aTrue aTrue) space0 aFalse
  let miss := mkState (iMatch aTrue aFalse) space0 aFalse
  let hitNF := fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull hit 8
  let missNF := fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull miss 8
  IO.println s!"MeTTaFull match hit normal form: {hitNF}"
  IO.println s!"MeTTaFull match miss normal form: {missNF}"

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

-- Smoke check: grounded Int/String operations and cast conversion branches.
#eval! do
  let gPlus := mkState (iGrounded2 (.apply "+" []) (gInt 2) (gInt 3)) space0 aFalse
  let gConcat := mkState (iGrounded2 (.apply "concat" []) (gString "hello") (gString "world")) space0 aFalse
  let gConcatSpaced := mkState
    (iGrounded2 (.apply "concat" [])
      (gStringCodes ["104", "105", "32"])
      (gStringCodes ["116", "104", "101", "114", "101"]))
    space0 aFalse
  let cStrToInt := mkState (iCast (gString "42") (.apply "Int" [])) space0 aFalse
  let cBadStrToInt := mkState (iCast (gString "abc") (.apply "Int" [])) space0 aFalse
  let cBoolToStr := mkState (iCast aTrue (.apply "String" [])) space0 aFalse
  let cBadStrToBool := mkState (iCast (gString "maybe") (.apply "Bool" [])) space0 aFalse
  IO.println s!"MeTTaFull grounded int plus: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull gPlus 8}"
  IO.println s!"MeTTaFull grounded string concat: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull gConcat 8}"
  IO.println s!"MeTTaFull grounded coded-string concat: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull gConcatSpaced 8}"
  IO.println s!"MeTTaFull cast string->int: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull cStrToInt 8}"
  IO.println s!"MeTTaFull cast invalid string->int: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull cBadStrToInt 8}"
  IO.println s!"MeTTaFull cast bool-symbol->string: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull cBoolToStr 8}"
  IO.println s!"MeTTaFull cast invalid string->bool: {fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull cBadStrToBool 8}"

-- coded_string_concat_normalForm_shape moved to FullLanguageTests.lean
-- (kernel reduction of `decide +kernel` is dramatically faster on imported definitions)

#check mettaFullOSLF
#check mettaFullGalois

end Mettapedia.Languages.MeTTa.Core.FullLanguageDef
