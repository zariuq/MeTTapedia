import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# IMP Language Definition

A Software-Foundations-style imperative core, rendered as a `LanguageDef`
with explicit continuation/state-machine semantics.

Current surface:
- Peano naturals (`0`, `S n`)
- variables `x`, `y`, `z`
- arithmetic `+`, `*`
- booleans `true`, `false`, `<=`, `==`, `not`, `and`
- statements `skip`, assignment, sequencing, `if`, `while`
- explicit runtime state `ImpState(control, store, kont, status)`

The design goal is to pressure the shared mettail runtime with:
- real user grammar from Lean
- deterministic small-step transitions
- one genuine lookup family (`storeGet`)
- tiny primitive relations only (`storeSet`, `natAdd`, `natMul`, `natLe`, `natEq`)
-/

namespace Mettapedia.Languages.IMP.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

private abbrev tbase (name : String) : TypeExpr := .base name
private abbrev simple (name ty : String) : TermParam := .simple name (tbase ty)

def imp : LanguageDef := {
  name := "IMP"
  types := ["Nat", "ImpVar", "Bool", "AAtom", "AMul", "AExp", "BAtom", "BNeg", "BConj", "BExp",
            "StmtAtom", "Stmt", "Control", "Kont", "Store", "Status", "State"]
  terms := [
    -- Peano naturals.
    { label := "Zero", category := "Nat", params := [],
      syntaxPattern := [.terminal "0"] },
    { label := "Succ", category := "Nat", params := [simple "n" "Nat"],
      syntaxPattern := [.terminal "S", .nonTerminal "n"] },

    -- Fixed variable names for the first executable IMP slice.
    { label := "VarX", category := "ImpVar", params := [],
      syntaxPattern := [.terminal "x"] },
    { label := "VarY", category := "ImpVar", params := [],
      syntaxPattern := [.terminal "y"] },
    { label := "VarZ", category := "ImpVar", params := [],
      syntaxPattern := [.terminal "z"] },

    -- Boolean values.
    { label := "BoolTrue", category := "Bool", params := [],
      syntaxPattern := [.terminal "true"] },
    { label := "BoolFalse", category := "Bool", params := [],
      syntaxPattern := [.terminal "false"] },

    -- Arithmetic grammar with precedence: AAtom < AMul < AExp.
    { label := "ANat", category := "AAtom", params := [simple "n" "Nat"],
      syntaxPattern := [.nonTerminal "n"] },
    { label := "AVar", category := "AAtom", params := [simple "x" "ImpVar"],
      syntaxPattern := [.nonTerminal "x"] },
    { label := "AParen", category := "AAtom", params := [simple "e" "AExp"],
      syntaxPattern := [.terminal "(", .nonTerminal "e", .terminal ")"] },
    { label := "AMulAtom", category := "AMul", params := [simple "a" "AAtom"],
      syntaxPattern := [.nonTerminal "a"] },
    { label := "AMulTimes", category := "AMul", params := [simple "lhs" "AMul", simple "rhs" "AAtom"],
      syntaxPattern := [.nonTerminal "lhs", .terminal "*", .nonTerminal "rhs"] },
    { label := "AExpMul", category := "AExp", params := [simple "m" "AMul"],
      syntaxPattern := [.nonTerminal "m"] },
    { label := "AExpPlus", category := "AExp", params := [simple "lhs" "AExp", simple "rhs" "AMul"],
      syntaxPattern := [.nonTerminal "lhs", .terminal "+", .nonTerminal "rhs"] },

    -- Boolean grammar with precedence: BAtom < BNeg < BConj < BExp.
    { label := "BTrueAtom", category := "BAtom", params := [],
      syntaxPattern := [.terminal "true"] },
    { label := "BFalseAtom", category := "BAtom", params := [],
      syntaxPattern := [.terminal "false"] },
    { label := "BLe", category := "BAtom", params := [simple "lhs" "AExp", simple "rhs" "AExp"],
      syntaxPattern := [.nonTerminal "lhs", .terminal "<=", .nonTerminal "rhs"] },
    { label := "BEq", category := "BAtom", params := [simple "lhs" "AExp", simple "rhs" "AExp"],
      syntaxPattern := [.nonTerminal "lhs", .terminal "==", .nonTerminal "rhs"] },
    { label := "BParen", category := "BAtom", params := [simple "b" "BExp"],
      syntaxPattern := [.terminal "(", .nonTerminal "b", .terminal ")"] },
    { label := "BNegAtom", category := "BNeg", params := [simple "b" "BAtom"],
      syntaxPattern := [.nonTerminal "b"] },
    { label := "BNot", category := "BNeg", params := [simple "b" "BNeg"],
      syntaxPattern := [.terminal "not", .nonTerminal "b"] },
    { label := "BConjNeg", category := "BConj", params := [simple "b" "BNeg"],
      syntaxPattern := [.nonTerminal "b"] },
    { label := "BAnd", category := "BConj", params := [simple "lhs" "BConj", simple "rhs" "BNeg"],
      syntaxPattern := [.nonTerminal "lhs", .terminal "and", .nonTerminal "rhs"] },
    { label := "BExpConj", category := "BExp", params := [simple "b" "BConj"],
      syntaxPattern := [.nonTerminal "b"] },

    -- Statement grammar with sequencing as the outer precedence level.
    { label := "Skip", category := "StmtAtom", params := [],
      syntaxPattern := [.terminal "skip"] },
    { label := "Assign", category := "StmtAtom", params := [simple "x" "ImpVar", simple "e" "AExp"],
      syntaxPattern := [.nonTerminal "x", .terminal ":=", .nonTerminal "e"] },
    { label := "If", category := "StmtAtom", params := [simple "b" "BExp", simple "t" "Stmt", simple "els" "Stmt"],
      syntaxPattern := [.terminal "if", .nonTerminal "b", .terminal "then", .nonTerminal "t",
                        .terminal "else", .nonTerminal "els"] },
    { label := "While", category := "StmtAtom", params := [simple "b" "BExp", simple "body" "Stmt"],
      syntaxPattern := [.terminal "while", .nonTerminal "b", .terminal "do", .nonTerminal "body"] },
    { label := "StmtParen", category := "StmtAtom", params := [simple "s" "Stmt"],
      syntaxPattern := [.terminal "{", .nonTerminal "s", .terminal "}"] },
    { label := "StmtAtomPromote", category := "Stmt", params := [simple "s" "StmtAtom"],
      syntaxPattern := [.nonTerminal "s"] },
    { label := "Seq", category := "Stmt", params := [simple "s1" "Stmt", simple "s2" "StmtAtom"],
      syntaxPattern := [.nonTerminal "s1", .terminal ";", .nonTerminal "s2"] },

    -- Runtime store: fixed slots for x/y/z, still exposed as a first-class term.
    { label := "Store", category := "Store", params := [simple "x" "Nat", simple "y" "Nat", simple "z" "Nat"],
      syntaxPattern := [.terminal "store", .terminal "(", .nonTerminal "x", .separator ",",
                        .nonTerminal "y", .separator ",", .nonTerminal "z", .terminal ")"] },

    -- Runtime status.
    { label := "Running", category := "Status", params := [],
      syntaxPattern := [.terminal "running"] },
    { label := "Done", category := "Status", params := [],
      syntaxPattern := [.terminal "done"] },
    { label := "Stuck", category := "Status", params := [],
      syntaxPattern := [.terminal "stuck"] },

    -- Runtime control terms.
    { label := "Start", category := "State", params := [simple "stmt" "Stmt", simple "store" "Store"],
      syntaxPattern := [.terminal "run", .nonTerminal "stmt", .terminal "with", .nonTerminal "store"] },
    { label := "RunStmt", category := "Control", params := [simple "stmt" "Stmt"],
      syntaxPattern := [.terminal "run_stmt", .nonTerminal "stmt"] },
    { label := "RunA", category := "Control", params := [simple "expr" "AExp"],
      syntaxPattern := [.terminal "run_a", .nonTerminal "expr"] },
    { label := "RunB", category := "Control", params := [simple "expr" "BExp"],
      syntaxPattern := [.terminal "run_b", .nonTerminal "expr"] },
    { label := "RetNat", category := "Control", params := [simple "n" "Nat"],
      syntaxPattern := [.terminal "ret_nat", .nonTerminal "n"] },
    { label := "RetBool", category := "Control", params := [simple "b" "Bool"],
      syntaxPattern := [.terminal "ret_bool", .nonTerminal "b"] },
    { label := "RetUnit", category := "Control", params := [],
      syntaxPattern := [.terminal "ret_unit"] },

    -- Continuation stack frames.
    { label := "KDone", category := "Kont", params := [],
      syntaxPattern := [.terminal "kdone"] },
    { label := "KSeq", category := "Kont", params := [simple "stmt" "Stmt", simple "k" "Kont"],
      syntaxPattern := [.terminal "kseq", .nonTerminal "stmt", .nonTerminal "k"] },
    { label := "KAssign", category := "Kont", params := [simple "x" "ImpVar", simple "k" "Kont"],
      syntaxPattern := [.terminal "kassign", .nonTerminal "x", .nonTerminal "k"] },
    { label := "KIf", category := "Kont", params := [simple "t" "Stmt", simple "els" "Stmt", simple "k" "Kont"],
      syntaxPattern := [.terminal "kif", .nonTerminal "t", .nonTerminal "els", .nonTerminal "k"] },
    { label := "KWhile", category := "Kont", params := [simple "b" "BExp", simple "body" "Stmt", simple "k" "Kont"],
      syntaxPattern := [.terminal "kwhile", .nonTerminal "b", .nonTerminal "body", .nonTerminal "k"] },
    { label := "KPlusL", category := "Kont", params := [simple "rhs" "AMul", simple "k" "Kont"],
      syntaxPattern := [.terminal "kplus_l", .nonTerminal "rhs", .nonTerminal "k"] },
    { label := "KPlusR", category := "Kont", params := [simple "lhs" "Nat", simple "k" "Kont"],
      syntaxPattern := [.terminal "kplus_r", .nonTerminal "lhs", .nonTerminal "k"] },
    { label := "KTimesL", category := "Kont", params := [simple "rhs" "AAtom", simple "k" "Kont"],
      syntaxPattern := [.terminal "ktimes_l", .nonTerminal "rhs", .nonTerminal "k"] },
    { label := "KTimesR", category := "Kont", params := [simple "lhs" "Nat", simple "k" "Kont"],
      syntaxPattern := [.terminal "ktimes_r", .nonTerminal "lhs", .nonTerminal "k"] },
    { label := "KLeL", category := "Kont", params := [simple "rhs" "AExp", simple "k" "Kont"],
      syntaxPattern := [.terminal "kle_l", .nonTerminal "rhs", .nonTerminal "k"] },
    { label := "KLeR", category := "Kont", params := [simple "lhs" "Nat", simple "k" "Kont"],
      syntaxPattern := [.terminal "kle_r", .nonTerminal "lhs", .nonTerminal "k"] },
    { label := "KEqL", category := "Kont", params := [simple "rhs" "AExp", simple "k" "Kont"],
      syntaxPattern := [.terminal "keq_l", .nonTerminal "rhs", .nonTerminal "k"] },
    { label := "KEqR", category := "Kont", params := [simple "lhs" "Nat", simple "k" "Kont"],
      syntaxPattern := [.terminal "keq_r", .nonTerminal "lhs", .nonTerminal "k"] },
    { label := "KNot", category := "Kont", params := [simple "k" "Kont"],
      syntaxPattern := [.terminal "knot", .nonTerminal "k"] },
    { label := "KAndL", category := "Kont", params := [simple "rhs" "BNeg", simple "k" "Kont"],
      syntaxPattern := [.terminal "kand_l", .nonTerminal "rhs", .nonTerminal "k"] },

    -- Full runtime state.
    { label := "ImpState", category := "State",
      params := [simple "control" "Control", simple "store" "Store", simple "kont" "Kont", simple "status" "Status"],
      syntaxPattern := [.terminal "state", .nonTerminal "control", .nonTerminal "store",
                        .nonTerminal "kont", .nonTerminal "status"] }
  ]
  equations := []
  rewrites := [
    -- Start from a user program and store.
    { name := "R_Start"
      typeContext := [("stmt", tbase "Stmt"), ("store", tbase "Store")]
      premises := []
      left := .apply "Start" [.fvar "stmt", .fvar "store"]
      right := .apply "ImpState"
                [ .apply "RunStmt" [.fvar "stmt"]
                , .fvar "store"
                , .apply "KDone" []
                , .apply "Running" [] ] },

    -- Statement evaluation front-end.
    { name := "R_Skip"
      typeContext := [("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunStmt" [.apply "StmtAtomPromote" [.apply "Skip" []]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetUnit" []
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_Assign"
      typeContext := [("x", tbase "ImpVar"), ("e", tbase "AExp"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunStmt" [.apply "StmtAtomPromote" [.apply "Assign" [.fvar "x", .fvar "e"]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunA" [.fvar "e"]
                 , .fvar "store"
                 , .apply "KAssign" [.fvar "x", .fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_Seq"
      typeContext := [("s1", tbase "Stmt"), ("s2", tbase "StmtAtom"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunStmt" [.apply "Seq" [.fvar "s1", .fvar "s2"]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunStmt" [.fvar "s1"]
                 , .fvar "store"
                 , .apply "KSeq" [.apply "StmtAtomPromote" [.fvar "s2"], .fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_If"
      typeContext := [("b", tbase "BExp"), ("t", tbase "Stmt"), ("els", tbase "Stmt"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunStmt" [.apply "StmtAtomPromote" [.apply "If" [.fvar "b", .fvar "t", .fvar "els"]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunB" [.fvar "b"]
                 , .fvar "store"
                 , .apply "KIf" [.fvar "t", .fvar "els", .fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_While"
      typeContext := [("b", tbase "BExp"), ("body", tbase "Stmt"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunStmt" [.apply "StmtAtomPromote" [.apply "While" [.fvar "b", .fvar "body"]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunB" [.fvar "b"]
                 , .fvar "store"
                 , .apply "KWhile" [.fvar "b", .fvar "body", .fvar "k"]
                 , .apply "Running" [] ] },

    -- Arithmetic evaluation.
    { name := "R_ANat"
      typeContext := [("n", tbase "Nat"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunA" [.apply "AExpMul" [.apply "AMulAtom" [.apply "ANat" [.fvar "n"]]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetNat" [.fvar "n"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_AVar"
      typeContext := [("x", tbase "ImpVar"), ("store", tbase "Store"), ("k", tbase "Kont"), ("n", tbase "Nat")]
      premises := [ .relationQuery "storeGet" [.fvar "store", .fvar "x", .fvar "n"] ]
      left := .apply "ImpState"
                [ .apply "RunA" [.apply "AExpMul" [.apply "AMulAtom" [.apply "AVar" [.fvar "x"]]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetNat" [.fvar "n"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_AParen"
      typeContext := [("e", tbase "AExp"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunA" [.apply "AExpMul" [.apply "AMulAtom" [.apply "AParen" [.fvar "e"]]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunA" [.fvar "e"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_AMul"
      typeContext := [("lhs", tbase "AMul"), ("rhs", tbase "AAtom"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunA" [.apply "AExpMul" [.apply "AMulTimes" [.fvar "lhs", .fvar "rhs"]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunA" [.apply "AExpMul" [.fvar "lhs"]]
                 , .fvar "store"
                 , .apply "KTimesL" [.fvar "rhs", .fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_APlus"
      typeContext := [("lhs", tbase "AExp"), ("rhs", tbase "AMul"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunA" [.apply "AExpPlus" [.fvar "lhs", .fvar "rhs"]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunA" [.fvar "lhs"]
                 , .fvar "store"
                 , .apply "KPlusL" [.fvar "rhs", .fvar "k"]
                 , .apply "Running" [] ] },

    -- Boolean evaluation.
    { name := "R_BTrue"
      typeContext := [("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunB" [.apply "BExpConj" [.apply "BConjNeg" [.apply "BNegAtom" [.apply "BTrueAtom" []]]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetBool" [.apply "BoolTrue" []]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_BFalse"
      typeContext := [("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunB" [.apply "BExpConj" [.apply "BConjNeg" [.apply "BNegAtom" [.apply "BFalseAtom" []]]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetBool" [.apply "BoolFalse" []]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_BParen"
      typeContext := [("b", tbase "BExp"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunB" [.apply "BExpConj" [.apply "BConjNeg" [.apply "BNegAtom" [.apply "BParen" [.fvar "b"]]]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunB" [.fvar "b"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_BLe"
      typeContext := [("lhs", tbase "AExp"), ("rhs", tbase "AExp"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunB" [.apply "BExpConj" [.apply "BConjNeg" [.apply "BNegAtom" [.apply "BLe" [.fvar "lhs", .fvar "rhs"]]]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunA" [.fvar "lhs"]
                 , .fvar "store"
                 , .apply "KLeL" [.fvar "rhs", .fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_BEq"
      typeContext := [("lhs", tbase "AExp"), ("rhs", tbase "AExp"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunB" [.apply "BExpConj" [.apply "BConjNeg" [.apply "BNegAtom" [.apply "BEq" [.fvar "lhs", .fvar "rhs"]]]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunA" [.fvar "lhs"]
                 , .fvar "store"
                 , .apply "KEqL" [.fvar "rhs", .fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_BNot"
      typeContext := [("b", tbase "BNeg"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunB" [.apply "BExpConj" [.apply "BConjNeg" [.apply "BNot" [.fvar "b"]]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunB" [.apply "BExpConj" [.apply "BConjNeg" [.fvar "b"]]]
                 , .fvar "store"
                 , .apply "KNot" [.fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_BAnd"
      typeContext := [("lhs", tbase "BConj"), ("rhs", tbase "BNeg"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RunB" [.apply "BExpConj" [.apply "BAnd" [.fvar "lhs", .fvar "rhs"]]]
                , .fvar "store", .fvar "k", .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunB" [.apply "BExpConj" [.fvar "lhs"]]
                 , .fvar "store"
                 , .apply "KAndL" [.fvar "rhs", .fvar "k"]
                 , .apply "Running" [] ] },

    -- Continuation frames.
    { name := "R_KSeq"
      typeContext := [("stmt", tbase "Stmt"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetUnit" []
                , .fvar "store"
                , .apply "KSeq" [.fvar "stmt", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunStmt" [.fvar "stmt"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KAssign"
      typeContext := [("n", tbase "Nat"), ("store", tbase "Store"), ("x", tbase "ImpVar"), ("k", tbase "Kont"), ("store2", tbase "Store")]
      premises := [ .relationQuery "storeSet" [.fvar "store", .fvar "x", .fvar "n", .fvar "store2"] ]
      left := .apply "ImpState"
                [ .apply "RetNat" [.fvar "n"]
                , .fvar "store"
                , .apply "KAssign" [.fvar "x", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetUnit" []
                 , .fvar "store2", .fvar "k", .apply "Running" [] ] },

    { name := "R_KIf_True"
      typeContext := [("t", tbase "Stmt"), ("els", tbase "Stmt"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetBool" [.apply "BoolTrue" []]
                , .fvar "store"
                , .apply "KIf" [.fvar "t", .fvar "els", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunStmt" [.fvar "t"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KIf_False"
      typeContext := [("t", tbase "Stmt"), ("els", tbase "Stmt"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetBool" [.apply "BoolFalse" []]
                , .fvar "store"
                , .apply "KIf" [.fvar "t", .fvar "els", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunStmt" [.fvar "els"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KWhile_True"
      typeContext := [("b", tbase "BExp"), ("body", tbase "Stmt"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetBool" [.apply "BoolTrue" []]
                , .fvar "store"
                , .apply "KWhile" [.fvar "b", .fvar "body", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunStmt" [.fvar "body"]
                 , .fvar "store"
                 , .apply "KSeq"
                    [ .apply "StmtAtomPromote" [.apply "While" [.fvar "b", .fvar "body"]]
                    , .fvar "k" ]
                 , .apply "Running" [] ] },

    { name := "R_KWhile_False"
      typeContext := [("b", tbase "BExp"), ("body", tbase "Stmt"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetBool" [.apply "BoolFalse" []]
                , .fvar "store"
                , .apply "KWhile" [.fvar "b", .fvar "body", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetUnit" []
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KPlus_L"
      typeContext := [("n", tbase "Nat"), ("rhs", tbase "AMul"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetNat" [.fvar "n"]
                , .fvar "store"
                , .apply "KPlusL" [.fvar "rhs", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunA" [.apply "AExpMul" [.fvar "rhs"]]
                 , .fvar "store"
                 , .apply "KPlusR" [.fvar "n", .fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_KPlus_R"
      typeContext := [("lhs", tbase "Nat"), ("rhs", tbase "Nat"), ("store", tbase "Store"), ("k", tbase "Kont"), ("sum", tbase "Nat")]
      premises := [ .relationQuery "natAdd" [.fvar "lhs", .fvar "rhs", .fvar "sum"] ]
      left := .apply "ImpState"
                [ .apply "RetNat" [.fvar "rhs"]
                , .fvar "store"
                , .apply "KPlusR" [.fvar "lhs", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetNat" [.fvar "sum"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KTimes_L"
      typeContext := [("n", tbase "Nat"), ("rhs", tbase "AAtom"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetNat" [.fvar "n"]
                , .fvar "store"
                , .apply "KTimesL" [.fvar "rhs", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunA" [.apply "AExpMul" [.apply "AMulAtom" [.fvar "rhs"]]]
                 , .fvar "store"
                 , .apply "KTimesR" [.fvar "n", .fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_KTimes_R"
      typeContext := [("lhs", tbase "Nat"), ("rhs", tbase "Nat"), ("store", tbase "Store"), ("k", tbase "Kont"), ("prod", tbase "Nat")]
      premises := [ .relationQuery "natMul" [.fvar "lhs", .fvar "rhs", .fvar "prod"] ]
      left := .apply "ImpState"
                [ .apply "RetNat" [.fvar "rhs"]
                , .fvar "store"
                , .apply "KTimesR" [.fvar "lhs", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetNat" [.fvar "prod"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KLe_L"
      typeContext := [("lhs", tbase "Nat"), ("rhs", tbase "AExp"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetNat" [.fvar "lhs"]
                , .fvar "store"
                , .apply "KLeL" [.fvar "rhs", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunA" [.fvar "rhs"]
                 , .fvar "store"
                 , .apply "KLeR" [.fvar "lhs", .fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_KLe_R"
      typeContext := [("lhs", tbase "Nat"), ("rhs", tbase "Nat"), ("store", tbase "Store"), ("k", tbase "Kont"), ("out", tbase "Bool")]
      premises := [ .relationQuery "natLe" [.fvar "lhs", .fvar "rhs", .fvar "out"] ]
      left := .apply "ImpState"
                [ .apply "RetNat" [.fvar "rhs"]
                , .fvar "store"
                , .apply "KLeR" [.fvar "lhs", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetBool" [.fvar "out"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KEq_L"
      typeContext := [("lhs", tbase "Nat"), ("rhs", tbase "AExp"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetNat" [.fvar "lhs"]
                , .fvar "store"
                , .apply "KEqL" [.fvar "rhs", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunA" [.fvar "rhs"]
                 , .fvar "store"
                 , .apply "KEqR" [.fvar "lhs", .fvar "k"]
                 , .apply "Running" [] ] },

    { name := "R_KEq_R"
      typeContext := [("lhs", tbase "Nat"), ("rhs", tbase "Nat"), ("store", tbase "Store"), ("k", tbase "Kont"), ("out", tbase "Bool")]
      premises := [ .relationQuery "natEq" [.fvar "lhs", .fvar "rhs", .fvar "out"] ]
      left := .apply "ImpState"
                [ .apply "RetNat" [.fvar "rhs"]
                , .fvar "store"
                , .apply "KEqR" [.fvar "lhs", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetBool" [.fvar "out"]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KNot_True"
      typeContext := [("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetBool" [.apply "BoolTrue" []]
                , .fvar "store"
                , .apply "KNot" [.fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetBool" [.apply "BoolFalse" []]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KNot_False"
      typeContext := [("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetBool" [.apply "BoolFalse" []]
                , .fvar "store"
                , .apply "KNot" [.fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetBool" [.apply "BoolTrue" []]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KAnd_True"
      typeContext := [("rhs", tbase "BNeg"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetBool" [.apply "BoolTrue" []]
                , .fvar "store"
                , .apply "KAndL" [.fvar "rhs", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RunB" [.apply "BExpConj" [.apply "BConjNeg" [.fvar "rhs"]]]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_KAnd_False"
      typeContext := [("rhs", tbase "BNeg"), ("store", tbase "Store"), ("k", tbase "Kont")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetBool" [.apply "BoolFalse" []]
                , .fvar "store"
                , .apply "KAndL" [.fvar "rhs", .fvar "k"]
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetBool" [.apply "BoolFalse" []]
                 , .fvar "store", .fvar "k", .apply "Running" [] ] },

    { name := "R_Final"
      typeContext := [("store", tbase "Store")]
      premises := []
      left := .apply "ImpState"
                [ .apply "RetUnit" []
                , .fvar "store"
                , .apply "KDone" []
                , .apply "Running" [] ]
      right := .apply "ImpState"
                 [ .apply "RetUnit" []
                 , .fvar "store"
                 , .apply "KDone" []
                 , .apply "Done" [] ] }
  ]
  congruenceCollections := []
}

end Mettapedia.Languages.IMP.LanguageDef
