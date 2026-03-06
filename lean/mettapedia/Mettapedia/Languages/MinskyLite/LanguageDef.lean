import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# MinskyLite Language Definition

A deliberately small deterministic two-register machine.

Design:
- two unary counters (`Nat`)
- structured control graph (`Control`) rather than an external program lookup
- explicit machine-state rewrites for every instruction shape
- deterministic halting via `status = done`

This keeps the Lean-side artifact package minimal while still producing a
clean executable rewrite system for mettail-rust consumption.
-/

namespace Mettapedia.Languages.MinskyLite.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

def minskyLite : LanguageDef := {
  name := "MinskyLite"
  types := ["Nat", "Control", "Status", "Machine"]
  terms := [
    -- Unary naturals for the two registers.
    { label := "Zero", category := "Nat", params := [],
      syntaxPattern := [.terminal "Z"] },
    { label := "Succ", category := "Nat",
      params := [.simple "n" (.base "Nat")],
      syntaxPattern := [.terminal "S", .nonTerminal "n"] },

    -- Structured control for a deterministic two-register machine.
    { label := "Halt", category := "Control", params := [],
      syntaxPattern := [.terminal "halt"] },
    { label := "IncA", category := "Control",
      params := [.simple "next" (.base "Control")],
      syntaxPattern := [.terminal "incA", .nonTerminal "next"] },
    { label := "IncB", category := "Control",
      params := [.simple "next" (.base "Control")],
      syntaxPattern := [.terminal "incB", .nonTerminal "next"] },
    { label := "DecA", category := "Control",
      params := [ .simple "zeroNext" (.base "Control")
                , .simple "succNext" (.base "Control")],
      syntaxPattern := [.terminal "decA", .terminal "(", .nonTerminal "zeroNext",
                        .separator ",", .nonTerminal "succNext", .terminal ")"] },
    { label := "DecB", category := "Control",
      params := [ .simple "zeroNext" (.base "Control")
                , .simple "succNext" (.base "Control")],
      syntaxPattern := [.terminal "decB", .terminal "(", .nonTerminal "zeroNext",
                        .separator ",", .nonTerminal "succNext", .terminal ")"] },

    -- Machine status.
    { label := "Running", category := "Status", params := [],
      syntaxPattern := [.terminal "running"] },
    { label := "Done", category := "Status", params := [],
      syntaxPattern := [.terminal "done"] },

    -- Full machine state: control, regA, regB, status.
    { label := "Machine", category := "Machine",
      params := [ .simple "ctrl" (.base "Control")
                , .simple "regA" (.base "Nat")
                , .simple "regB" (.base "Nat")
                , .simple "status" (.base "Status")],
      syntaxPattern := [.terminal "state", .nonTerminal "ctrl", .nonTerminal "regA",
                        .nonTerminal "regB", .nonTerminal "status"] }
  ]
  equations := []
  rewrites := [
    { name := "R_IncA"
      typeContext := [("next", .base "Control"), ("a", .base "Nat"), ("b", .base "Nat")]
      premises := []
      left := .apply "Machine"
                [ .apply "IncA" [.fvar "next"]
                , .fvar "a", .fvar "b", .apply "Running" [] ]
      right := .apply "Machine"
                [ .fvar "next"
                , .apply "Succ" [.fvar "a"], .fvar "b", .apply "Running" [] ] },

    { name := "R_IncB"
      typeContext := [("next", .base "Control"), ("a", .base "Nat"), ("b", .base "Nat")]
      premises := []
      left := .apply "Machine"
                [ .apply "IncB" [.fvar "next"]
                , .fvar "a", .fvar "b", .apply "Running" [] ]
      right := .apply "Machine"
                [ .fvar "next"
                , .fvar "a", .apply "Succ" [.fvar "b"], .apply "Running" [] ] },

    { name := "R_DecA_Zero"
      typeContext := [("zeroNext", .base "Control"), ("succNext", .base "Control"), ("b", .base "Nat")]
      premises := []
      left := .apply "Machine"
                [ .apply "DecA" [.fvar "zeroNext", .fvar "succNext"]
                , .apply "Zero" [], .fvar "b", .apply "Running" [] ]
      right := .apply "Machine"
                [ .fvar "zeroNext"
                , .apply "Zero" [], .fvar "b", .apply "Running" [] ] },

    { name := "R_DecA_Succ"
      typeContext := [ ("zeroNext", .base "Control")
                     , ("succNext", .base "Control")
                     , ("a", .base "Nat")
                     , ("b", .base "Nat") ]
      premises := []
      left := .apply "Machine"
                [ .apply "DecA" [.fvar "zeroNext", .fvar "succNext"]
                , .apply "Succ" [.fvar "a"], .fvar "b", .apply "Running" [] ]
      right := .apply "Machine"
                [ .fvar "succNext"
                , .fvar "a", .fvar "b", .apply "Running" [] ] },

    { name := "R_DecB_Zero"
      typeContext := [("zeroNext", .base "Control"), ("succNext", .base "Control"), ("a", .base "Nat")]
      premises := []
      left := .apply "Machine"
                [ .apply "DecB" [.fvar "zeroNext", .fvar "succNext"]
                , .fvar "a", .apply "Zero" [], .apply "Running" [] ]
      right := .apply "Machine"
                [ .fvar "zeroNext"
                , .fvar "a", .apply "Zero" [], .apply "Running" [] ] },

    { name := "R_DecB_Succ"
      typeContext := [ ("zeroNext", .base "Control")
                     , ("succNext", .base "Control")
                     , ("a", .base "Nat")
                     , ("b", .base "Nat") ]
      premises := []
      left := .apply "Machine"
                [ .apply "DecB" [.fvar "zeroNext", .fvar "succNext"]
                , .fvar "a", .apply "Succ" [.fvar "b"], .apply "Running" [] ]
      right := .apply "Machine"
                [ .fvar "succNext"
                , .fvar "a", .fvar "b", .apply "Running" [] ] },

    { name := "R_Halt"
      typeContext := [("a", .base "Nat"), ("b", .base "Nat")]
      premises := []
      left := .apply "Machine"
                [ .apply "Halt" []
                , .fvar "a", .fvar "b", .apply "Running" [] ]
      right := .apply "Machine"
                [ .apply "Halt" []
                , .fvar "a", .fvar "b", .apply "Done" [] ] }
  ]
  congruenceCollections := []
}

end Mettapedia.Languages.MinskyLite.LanguageDef
