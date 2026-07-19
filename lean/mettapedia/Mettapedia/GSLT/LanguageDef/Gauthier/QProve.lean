import Mettapedia.GSLT.LanguageDef.Gauthier.E1

/-!
# Gauthier OEIS qprove syntax

The SML qprove surface exposes an operator table and formula syntax, but the
checkout does not contain a qprove program evaluator analogous to the integer
and list evaluators.  This file therefore records exactly the syntax-level
languageDef data: operator names, arities, higher-order arities, and formula
well-formedness for the fixed-arity formula symbols visible in `qsyntax.sml`.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierQProve

open Mettapedia.GSLT.LanguageDef.GauthierE1

inductive Prim where
  | x
  | y
  | hd
  | tl
  | push
  | null
  | isV
  | isNot
  | isOr
  | sameId
  | dest
  | cond
  | while
  deriving DecidableEq, Repr

def qproveSignature : Signature Prim := [
  entry "x" 0 0 .x,
  entry "y" 0 0 .y,
  entry "hd" 1 0 .hd,
  entry "tl" 1 0 .tl,
  entry "push" 2 0 .push,
  entry "null" 0 0 .null,
  entry "is_v" 1 0 .isV,
  entry "is_not" 1 0 .isNot,
  entry "is_or" 1 0 .isOr,
  entry "same_id" 2 0 .sameId,
  entry "dest" 1 0 .dest,
  entry "cond" 3 0 .cond,
  entry "while" 4 2 .while
]

namespace P

def X : Prog := .node 0 []
def Y : Prog := .node 1 []
def hd (a : Prog) : Prog := .node 2 [a]
def tl (a : Prog) : Prog := .node 3 [a]
def push (a b : Prog) : Prog := .node 4 [a, b]
def null : Prog := .node 5 []
def isV (a : Prog) : Prog := .node 6 [a]
def isNot (a : Prog) : Prog := .node 7 [a]
def isOr (a : Prog) : Prog := .node 8 [a]
def sameId (a b : Prog) : Prog := .node 9 [a, b]
def dest (a : Prog) : Prog := .node 10 [a]
def cond (c t f : Prog) : Prog := .node 11 [c, t, f]
def whileP (step stop c init : Prog) : Prog := .node 12 [step, stop, c, init]

end P

theorem push_wellFormed :
    WellFormed qproveSignature (P.push P.X P.Y) :=
  recognize_sound (sig := qproveSignature) (toks := [0, 1, 4])
    (p := P.push P.X P.Y) (by rfl)

theorem while_wellFormed :
    WellFormed qproveSignature (P.whileP P.X P.Y P.null P.X) :=
  recognize_sound (sig := qproveSignature) (toks := [0, 1, 5, 0, 12])
    (p := P.whileP P.X P.Y P.null P.X) (by rfl)

theorem bad_while_not_wellFormed :
    Not (WellFormed qproveSignature (.node 12 [P.X, P.Y])) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [qproveSignature, entryAt, listGet?] at hentry
      cases hentry
      simp [entry] at hlen

theorem bad_operator_not_wellFormed :
    Not (WellFormed qproveSignature (.node 99 [])) := by
  intro h
  cases h with
  | node hentry _ _ =>
      simp [qproveSignature, entryAt, listGet?] at hentry

structure QId where
  classTag : Nat
  index : Int
  deriving DecidableEq, Repr

namespace QId

def prog (i : Nat) : QId := { classTag := 0, index := Int.ofNat i }
def int (i : Int) : QId := { classTag := 1, index := i }
def skolem (i : Nat) : QId := { classTag := 2, index := Int.ofNat i }
def var (i : Nat) : QId := { classTag := 3, index := Int.ofNat i }
def bound (i : Nat) : QId := { classTag := 4, index := Int.ofNat i }
def logic (i : Nat) : QId := { classTag := 5, index := Int.ofNat i }

def notOp : QId := logic 0
def orOp : QId := logic 1
def forallOp : QId := logic 2
def eqOp : QId := logic 3
def geqOp : QId := logic 4

end QId

inductive Formula where
  | atom : QId -> List Formula -> Formula
  deriving Repr

namespace Formula

def zero : Formula := .atom (QId.int 0) []
def one : Formula := .atom (QId.int 1) []
def x0 : Formula := .atom (QId.var 0) []
def x1 : Formula := .atom (QId.var 1) []
def neg (p : Formula) : Formula := .atom QId.notOp [p]
def orF (p q : Formula) : Formula := .atom QId.orOp [p, q]
def forallF (vars body : Formula) : Formula := .atom QId.forallOp [vars, body]
def eq (p q : Formula) : Formula := .atom QId.eqOp [p, q]
def geq (p q : Formula) : Formula := .atom QId.geqOp [p, q]
def add (p q : Formula) : Formula := .atom (QId.prog 3) [p, q]
def cond (c t f : Formula) : Formula := .atom (QId.prog 8) [c, t, f]
def loop2h (f g h c a : Formula) : Formula := .atom (QId.prog 16) [f, g, h, c, a]

def addCommExample : Formula := eq (add x0 one) (add one x0)
def guardedExample : Formula := neg (geq x0 zero)

end Formula

def progFormulaArity? : Nat -> Option Nat
  | 0 => some 0
  | 1 => some 0
  | 2 => some 0
  | 3 => some 2
  | 4 => some 2
  | 5 => some 2
  | 6 => some 2
  | 7 => some 2
  | 8 => some 3
  | 9 => some 3
  | 10 => some 0
  | 11 => some 0
  | 12 => some 2
  | 13 => some 5
  | 14 => some 2
  | 15 => some 1
  | 16 => some 5
  | _ => none

def logicFormulaArity? : Nat -> Option Nat
  | 0 => some 1
  | 1 => some 2
  -- The SML syntax names `forall`; the SMT S-expression surface uses
  -- the binary `(forall vars body)` shape.  This remains syntax only.
  | 2 => some 2
  | 3 => some 2
  | 4 => some 2
  | _ => none

def natIndex? (i : Int) : Option Nat :=
  if i < 0 then none else some i.toNat

def formulaArity? (id : QId) : Option Nat :=
  match id.classTag with
  | 0 =>
      match natIndex? id.index with
      | none => none
      | some i => progFormulaArity? i
  | 1 => some 0
  | 2 =>
      match natIndex? id.index with
      | none => none
      | some _ => some 0
  | 3 =>
      match natIndex? id.index with
      | none => none
      | some _ => some 0
  | 4 =>
      match natIndex? id.index with
      | none => none
      | some _ => some 0
  | 5 =>
      match natIndex? id.index with
      | none => none
      | some i => logicFormulaArity? i
  | _ => none

inductive FormulaWellFormed : Formula -> Prop where
  | atom {id : QId} {args : List Formula} {n : Nat} :
      formulaArity? id = some n ->
      args.length = n ->
      (forall a, List.Mem a args -> FormulaWellFormed a) ->
      FormulaWellFormed (.atom id args)

namespace FormulaWellFormed

theorem nullary {id : QId}
    (h : formulaArity? id = some 0) :
    FormulaWellFormed (.atom id []) :=
  .atom h rfl (by intro a hmem; cases hmem)

theorem unary {id : QId} {a : Formula}
    (h : formulaArity? id = some 1)
    (ha : FormulaWellFormed a) :
    FormulaWellFormed (.atom id [a]) :=
  .atom h rfl (by
    intro c hc
    cases List.mem_cons.mp hc with
    | inl h =>
        cases h
        exact ha
    | inr hc =>
        cases hc)

theorem binary {id : QId} {a b : Formula}
    (h : formulaArity? id = some 2)
    (ha : FormulaWellFormed a)
    (hb : FormulaWellFormed b) :
    FormulaWellFormed (.atom id [a, b]) :=
  .atom h rfl (by
    intro c hc
    cases List.mem_cons.mp hc with
    | inl h =>
        cases h
        exact ha
    | inr hc =>
        cases List.mem_cons.mp hc with
        | inl h =>
            cases h
            exact hb
        | inr hc =>
            cases hc)

theorem ternary {id : QId} {a b c : Formula}
    (h : formulaArity? id = some 3)
    (ha : FormulaWellFormed a)
    (hb : FormulaWellFormed b)
    (hc : FormulaWellFormed c) :
    FormulaWellFormed (.atom id [a, b, c]) :=
  .atom h rfl (by
    intro d hd
    cases List.mem_cons.mp hd with
    | inl h =>
        cases h
        exact ha
    | inr hd =>
        cases List.mem_cons.mp hd with
        | inl h =>
            cases h
            exact hb
        | inr hd =>
            cases List.mem_cons.mp hd with
            | inl h =>
                cases h
                exact hc
            | inr hd =>
                cases hd)

end FormulaWellFormed

theorem formula_x0_wellFormed :
    FormulaWellFormed Formula.x0 :=
  FormulaWellFormed.nullary rfl

theorem formula_add_comm_wellFormed :
    FormulaWellFormed Formula.addCommExample :=
  FormulaWellFormed.binary (id := QId.eqOp) rfl
    (FormulaWellFormed.binary (id := QId.prog 3) rfl
      formula_x0_wellFormed
      (FormulaWellFormed.nullary (id := QId.int 1) rfl))
    (FormulaWellFormed.binary (id := QId.prog 3) rfl
      (FormulaWellFormed.nullary (id := QId.int 1) rfl)
      formula_x0_wellFormed)

theorem formula_guarded_wellFormed :
    FormulaWellFormed Formula.guardedExample :=
  FormulaWellFormed.unary (id := QId.notOp) rfl
    (FormulaWellFormed.binary (id := QId.geqOp) rfl
      formula_x0_wellFormed
      (FormulaWellFormed.nullary (id := QId.int 0) rfl))

theorem bad_eq_formula_not_wellFormed :
    Not (FormulaWellFormed (.atom QId.eqOp [Formula.x0])) := by
  intro h
  cases h with
  | atom hArity hlen _ =>
      simp [QId.eqOp, QId.logic, formulaArity?, natIndex?, logicFormulaArity?] at hArity
      cases hArity
      simp at hlen

theorem bad_unknown_program_formula_not_wellFormed :
    Not (FormulaWellFormed (.atom (QId.prog 99) [])) := by
  intro h
  cases h with
  | atom hArity _ _ =>
      simp [QId.prog, formulaArity?, natIndex?, progFormulaArity?] at hArity

end Mettapedia.GSLT.LanguageDef.GauthierQProve
