import Algorithms.MeTTa.Simple.Session
import Algorithms.MeTTa.Simple.Relations

open Algorithms.MeTTa.Simple
open Algorithms.MeTTa.Simple.Session
open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Engine
open MeTTailCore.MeTTaIL.Profile

private def emptyLanguage : LanguageDef := {
  name := "SimpleSession"
  types := []
  terms := []
  equations := []
  rewrites := []
  congruenceCollections := []
}

private def emptyBundle : SpecBundle := {
  language := emptyLanguage
  relationEnv := RelationEnv.empty
  builtins := coreIntrinsicBuiltins
  policy := {
    maxFuel := 128
    normalizeToFixedPoint := false
  }
}

def main : IO Unit := do
  let s0 := Session.new emptyBundle
  let s1 ← loadFile s0 "/home/zar/claude/hyperon/PeTTa/examples/invertpeanoplus.metta"
  IO.println s!"errors={s1.diag.errors} parsed={s1.diag.parsedLines} applied={s1.diag.appliedStmts} eval={s1.diag.evalCalls}"
  for m in s1.diag.messages.reverse do
    if m.contains "test failed" || m.contains "test passed" then
      IO.println m
