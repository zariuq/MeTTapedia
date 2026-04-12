/-
# WAM Basic Definitions

Foundational types for Warren Abstract Machine formalization.
Based on:
- Warren (1983): An Abstract Prolog Instruction Set
- Aït-Kaci (1991): WAM: A Tutorial Reconstruction
- Bohrer & Crary (2018): TWAM: A Certifying Abstract Machine

## Overview

The WAM uses a heap-based term representation with:
- REF cells for variables (self-referential when unbound)
- STR cells pointing to functor cells
- CON cells for constants (0-ary functors)
- LIS cells for list pairs (specialized 2-ary structure)

Register allocation distinguishes:
- Argument registers A1..An (same as X1..Xn, used for predicate arguments)
- Temporary registers Xi (heap references)
- Permanent registers Yn (stack variables, introduced in L2)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

namespace Mettapedia.AutoBooks.ClaudeProcWam.WAM

/-! ## Basic Types -/

/-- Functors are pairs (symbol, arity). Two functors are equal iff same symbol and arity. -/
structure Functor where
  symbol : String
  arity : Nat
  deriving DecidableEq, Hashable, Repr

instance : ToString Functor where
  toString f := s!"{f.symbol}/{f.arity}"

/-- Constants are 0-ary functors -/
def Functor.isConstant (f : Functor) : Bool := f.arity == 0

/-- Create a constant functor -/
def mkConstant (s : String) : Functor := ⟨s, 0⟩

/-- Create a functor with given arity -/
def mkFunctor (s : String) (n : Nat) : Functor := ⟨s, n⟩

/-! ## Address Types -/

/-- Heap addresses are natural numbers -/
abbrev HeapAddr := Nat

/-- Register index -/
abbrev RegIndex := Nat

/-- Code addresses -/
abbrev CodeAddr := Nat

/-! ## Heap Cell Tags

The WAM uses tagged cells to distinguish different kinds of heap data.
-/

/-- Tag indicating the type of a heap cell -/
inductive CellTag where
  | REF  -- Reference (variable) cell
  | STR  -- Structure cell (points to functor)
  | CON  -- Constant cell
  | LIS  -- List cell (points to head, tail follows)
  deriving DecidableEq, Repr

instance : ToString CellTag where
  toString
    | .REF => "REF"
    | .STR => "STR"
    | .CON => "CON"
    | .LIS => "LIS"

/-! ## Heap Cells

A heap cell is a tagged value. The value interpretation depends on the tag:
- REF: address of the referenced cell (self for unbound)
- STR: address of the functor cell
- CON: the constant symbol
- LIS: address of the list head (tail is at head+1)
-/

/-- A heap cell: tagged data -/
inductive HeapCell where
  | ref (addr : HeapAddr)       -- Variable reference
  | str (addr : HeapAddr)       -- Structure pointer
  | con (f : Functor)           -- Constant (0-ary functor)
  | lis (addr : HeapAddr)       -- List pointer
  | functor (f : Functor)       -- Functor cell (not tagged, follows STR)
  deriving DecidableEq, Repr

/-- Get the tag of a heap cell -/
def HeapCell.tag : HeapCell → Option CellTag
  | .ref _ => some .REF
  | .str _ => some .STR
  | .con _ => some .CON
  | .lis _ => some .LIS
  | .functor _ => none  -- Functor cells are untagged

instance : ToString HeapCell where
  toString
    | .ref a => s!"⟨REF, {a}⟩"
    | .str a => s!"⟨STR, {a}⟩"
    | .con f => s!"⟨CON, {f}⟩"
    | .lis a => s!"⟨LIS, {a}⟩"
    | .functor f => s!"{f}"

/-! ## Register Types

WAM has three types of registers:
- Argument registers: A1..An (first n registers, used for passing arguments)
- Temporary registers: X1..Xm (general purpose, overlaps with Ai)
- Permanent registers: Y1..Yk (stack-allocated, survive calls)

In this formalization, we use a unified register file where:
- Indices 0..n-1 are argument registers (and also X1..Xn)
- Permanent registers are addressed separately
-/

/-- Variable register reference (X or A register) -/
structure XReg where
  index : RegIndex
  deriving DecidableEq, Repr

/-- Permanent register reference (Y register) -/
structure YReg where
  index : RegIndex
  deriving DecidableEq, Repr

/-- A register is either temporary (X) or permanent (Y) -/
inductive VarReg where
  | x : XReg → VarReg
  | y : YReg → VarReg
  deriving DecidableEq, Repr

/-- Argument register is just an X register with special semantics -/
abbrev ArgReg := XReg

instance : ToString XReg where
  toString r := s!"X{r.index}"

instance : ToString YReg where
  toString r := s!"Y{r.index}"

instance : ToString VarReg where
  toString
    | .x r => toString r
    | .y r => toString r

/-! ## Mode

The WAM operates in two modes:
- Read mode: matching against existing heap data
- Write mode: building new heap data
-/

/-- Machine mode for unification -/
inductive Mode where
  | read   -- Reading/matching existing heap structure
  | write  -- Writing/building new heap structure
  deriving DecidableEq, Repr

instance : ToString Mode where
  toString
    | .read => "read"
    | .write => "write"

/-! ## Instruction Labels

Labels are used for control flow (procedure calls, backtracking).
-/

/-- Procedure label (predicate name with arity) -/
structure ProcLabel where
  name : String
  arity : Nat
  deriving DecidableEq, Hashable, Repr

instance : ToString ProcLabel where
  toString p := s!"{p.name}/{p.arity}"

/-- Code label (for internal jumps within procedures) -/
structure CodeLabel where
  proc : ProcLabel
  offset : Nat
  deriving DecidableEq, Repr

/-! ## First-Order Terms (Source Syntax)

Before compilation, Prolog terms are represented as trees.
-/

/-- Source-level variable names -/
abbrev VarName := String

/-- First-order term (source representation) -/
inductive Term where
  | var : VarName → Term
  | app : Functor → List Term → Term
  deriving Repr

/-- A constant is a term with 0-ary functor and no subterms -/
def Term.const (s : String) : Term := .app (mkConstant s) []

/-- Check if a term is a variable -/
def Term.isVar : Term → Bool
  | .var _ => true
  | .app _ _ => false

/-- Get variables in a term -/
def Term.vars : Term → List VarName
  | .var v => [v]
  | .app _ ts => (ts.map Term.vars).flatten

instance : ToString Term where
  toString t := go t
where
  go : Term → String
    | .var v => v
    | .app f [] => f.symbol
    | .app f ts =>
      let args := String.intercalate ", " (ts.map go)
      s!"{f.symbol}({args})"

/-! ## Atoms and Clauses

Prolog atoms are terms applied to predicates.
-/

/-- An atom is a predicate applied to arguments -/
structure Atom where
  pred : ProcLabel
  args : List Term
  deriving Repr

instance : ToString Atom where
  toString a :=
    if a.args.isEmpty then a.pred.name
    else
      let args := String.intercalate ", " (a.args.map toString)
      s!"{a.pred.name}({args})"

/-- A clause is head :- body (fact if body is empty) -/
structure Clause where
  head : Atom
  body : List Atom
  deriving Repr

/-- A Prolog program is a list of clauses -/
abbrev Program := List Clause

/-- A query is a list of atoms to prove -/
abbrev Query := List Atom

end Mettapedia.AutoBooks.ClaudeProcWam.WAM
