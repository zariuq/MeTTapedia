import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# MM0-Lite Language Definition

A minimal proof-checking kernel in `LanguageDef` form.

Design:
- stack machine for proof terms
- one external theorem lookup relation (`thmConcl`)
- deterministic acceptance when stack finishes as `[goal]`

This is intentionally small but executable through the generic MeTTaIL engine,
so it can be exported and compared across runtime backends.
-/

namespace Mettapedia.Languages.MM0Lite.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

def mm0Lite : LanguageDef := {
  name := "MM0Lite",
  types := ["Formula", "Instr", "Program", "Stack", "ProofResult", "ProofState", "Thm"],
  terms := [
    -- Formula
    { label := "AtomP", category := "Formula", params := [],
      syntaxPattern := [.terminal "P"] },
    { label := "AtomQ", category := "Formula", params := [],
      syntaxPattern := [.terminal "Q"] },
    { label := "AtomR", category := "Formula", params := [],
      syntaxPattern := [.terminal "R"] },
    { label := "Implies", category := "Formula",
      params := [.simple "a" (.base "Formula"), .simple "b" (.base "Formula")],
      syntaxPattern := [.terminal "(", .nonTerminal "a", .terminal "->", .nonTerminal "b", .terminal ")"] },

    -- Theorem names
    { label := "ThmImpPQ", category := "Thm", params := [],
      syntaxPattern := [.terminal "thm_imp_p_q"] },
    { label := "ThmImpQR", category := "Thm", params := [],
      syntaxPattern := [.terminal "thm_imp_q_r"] },

    -- Instructions
    { label := "IPush", category := "Instr",
      params := [.simple "formula" (.base "Formula")],
      syntaxPattern := [.terminal "push", .nonTerminal "formula"] },
    { label := "IUse", category := "Instr",
      params := [.simple "th" (.base "Thm")],
      syntaxPattern := [.terminal "use", .nonTerminal "th"] },
    { label := "IMP", category := "Instr", params := [],
      syntaxPattern := [.terminal "mp"] },

    -- Program list
    { label := "INil", category := "Program", params := [],
      syntaxPattern := [.terminal "[]"] },
    { label := "ICons", category := "Program",
      params := [.simple "i" (.base "Instr"), .simple "tail" (.base "Program")],
      syntaxPattern := [.terminal "[", .nonTerminal "i", .terminal "::", .nonTerminal "tail", .terminal "]"] },

    -- Stack list
    { label := "SNil", category := "Stack", params := [],
      syntaxPattern := [.terminal "{}"] },
    { label := "SCons", category := "Stack",
      params := [.simple "formula" (.base "Formula"), .simple "tail" (.base "Stack")],
      syntaxPattern := [.terminal "{", .nonTerminal "formula", .terminal ";", .nonTerminal "tail", .terminal "}"] },

    -- Result
    { label := "Pending", category := "ProofResult", params := [],
      syntaxPattern := [.terminal "pending"] },
    { label := "Verified", category := "ProofResult", params := [],
      syntaxPattern := [.terminal "verified"] },
    { label := "Error", category := "ProofResult", params := [],
      syntaxPattern := [.terminal "error"] },

    -- Checker state
    { label := "MMState", category := "ProofState",
      params := [ .simple "prog" (.base "Program")
                , .simple "goal" (.base "Formula")
                , .simple "stack" (.base "Stack")
                , .simple "out" (.base "ProofResult")],
      syntaxPattern := [.terminal "state", .nonTerminal "prog", .nonTerminal "goal",
                        .nonTerminal "stack", .nonTerminal "out"] }
  ],
  equations := [],
  rewrites := [
    -- push f
    { name := "R_Push",
      typeContext := [("f", .base "Formula"), ("prog", .base "Program"),
                      ("goal", .base "Formula"), ("st", .base "Stack")],
      premises := [],
      left := .apply "MMState"
                [ .apply "ICons" [.apply "IPush" [.fvar "f"], .fvar "prog"]
                , .fvar "goal", .fvar "st", .apply "Pending" [] ],
      right := .apply "MMState"
                [ .fvar "prog", .fvar "goal"
                , .apply "SCons" [.fvar "f", .fvar "st"], .apply "Pending" [] ] },

    -- use theorem: theorem conclusion provided by relation env
    { name := "R_Use",
      typeContext := [("th", .base "Thm"), ("prog", .base "Program"),
                      ("goal", .base "Formula"), ("st", .base "Stack"),
                      ("concl", .base "Formula")],
      premises := [ .relationQuery "thmConcl" [.fvar "th", .fvar "concl"] ],
      left := .apply "MMState"
                [ .apply "ICons" [.apply "IUse" [.fvar "th"], .fvar "prog"]
                , .fvar "goal", .fvar "st", .apply "Pending" [] ],
      right := .apply "MMState"
                [ .fvar "prog", .fvar "goal"
                , .apply "SCons" [.fvar "concl", .fvar "st"], .apply "Pending" [] ] },

    -- modus ponens: (A -> B), A |- B
    { name := "R_MP",
      typeContext := [("a", .base "Formula"), ("b", .base "Formula"),
                      ("prog", .base "Program"), ("goal", .base "Formula"),
                      ("st", .base "Stack")],
      premises := [],
      left := .apply "MMState"
                [ .apply "ICons" [.apply "IMP" [], .fvar "prog"]
                , .fvar "goal"
                , .apply "SCons"
                    [ .apply "Implies" [.fvar "a", .fvar "b"]
                    , .apply "SCons" [.fvar "a", .fvar "st"]]
                , .apply "Pending" [] ],
      right := .apply "MMState"
                [ .fvar "prog", .fvar "goal"
                , .apply "SCons" [.fvar "b", .fvar "st"], .apply "Pending" [] ] },

    -- accept only when program is done and stack is exactly [goal]
    { name := "R_Accept",
      typeContext := [("goal", .base "Formula")],
      premises := [],
      left := .apply "MMState"
                [ .apply "INil" [], .fvar "goal"
                , .apply "SCons" [.fvar "goal", .apply "SNil" []]
                , .apply "Pending" [] ],
      right := .apply "MMState"
                [ .apply "INil" [], .fvar "goal"
                , .apply "SCons" [.fvar "goal", .apply "SNil" []]
                , .apply "Verified" [] ] }
  ],
  congruenceCollections := []
}

end Mettapedia.Languages.MM0Lite.LanguageDef
