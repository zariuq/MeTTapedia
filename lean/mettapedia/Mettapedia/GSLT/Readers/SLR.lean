import Mettapedia.OSLF.Framework.GrammarDerives

/-!
# SLR(1) tables for a token-level grammar, computed ahead of time

A two-level reader cuts bytes into tokens (`TokenProfile.tokenize`) and then parses the token
list with the grammar rows. This module computes the parser tables from the rows, once, before
any source is read: the LR(0) automaton, the FIRST and FOLLOW sets, and the SLR(1) actions. The
tables are data; generic engines (one in MeTTa, one in C) run them.

A token-level grammar has three kinds of terminals: a fixed spelling written in a row
(`lit "$p"`), a token sort that has no rows of its own (`tok "label_tok"`, any nonempty run of the
sort's bytes), and the end of input. Two terminals *overlap* when one token can be both, for
example `lit "("` and `tok "symbol_tok"`; a table is usable only if overlapping terminals never
ask for different actions in one state (`tokenConflicts`).

The tables are not trusted. Every tree an engine returns is checked by the trusted tree check
(`TreeCheck`), whose agreement with `GrammarDerives.Derives` is proved there.

Example: for the rows `s ::= "a" s | "b"` the automaton has a shift on `a` and on `b` from the
start state and no conflict. Negative example: the ambiguous `e ::= e "+" e | "x"` has a
shift/reduce conflict on `+`. Both are checked by the executable controls at the end.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.SLR

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives

/-- A symbol of a token-level grammar. -/
inductive Sym where
  | lit (spelling : String)
  | tok (sort : String)
  | eof
  | nt (sort : String)
  deriving DecidableEq, Repr, Inhabited, BEq

def Sym.isTerminal : Sym → Bool
  | .nt _ => false
  | _ => true

/-- One production: the row's label, its sort, and its items as symbols. -/
structure Prod where
  label : String
  lhs : String
  rhs : List Sym
  deriving DecidableEq, Repr, Inhabited

/-- A row's item as a symbol: a terminal spelling, a token sort, or a phrase sort. Items the
derivation relation does not cover have no symbol. -/
def lowerItem (tokenSorts : List String) (r : GrammarRule) : SyntaxItem → Option Sym
  | .terminal t => some (.lit t)
  | .nonTerminal n => (paramSort? r n).map fun s => if tokenSorts.contains s then .tok s else .nt s
  | _ => none

def lowerRow (tokenSorts : List String) (r : GrammarRule) : Option Prod := do
  let rhs ← r.syntaxPattern.mapM (lowerItem tokenSorts r)
  pure { label := r.label, lhs := r.category, rhs }

/-- Production 0 is the augmented start `rdr-accept-start → start $eof`; the rows follow in order. -/
def productions (tokenSorts : List String) (start : String) (lang : LanguageDef) :
    Option (List Prod) := do
  let rows ← lang.terms.mapM (lowerRow tokenSorts)
  pure ({ label := "rdr-accept-start", lhs := "rdr-accept-start", rhs := [.nt start, .eof] } :: rows)

/-! ## LR(0) items and states -/

/-- An item: a production index and the position of the dot. -/
abbrev Item := Nat × Nat

def itemLe (a b : Item) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

def normalize (items : List Item) : List Item := (items.mergeSort itemLe).eraseDups

def symAt (prods : Array Prod) (item : Item) : Option Sym :=
  (prods.getD item.1 default).rhs[item.2]?

def closureStep (prods : Array Prod) (items : List Item) : List Item :=
  let added := items.flatMap fun item =>
    match symAt prods item with
    | some (.nt sort) =>
        (List.range prods.size).filterMap fun p =>
          if (prods.getD p default).lhs == sort then some (p, 0) else none
    | _ => []
  normalize (items ++ added)

def closure (prods : Array Prod) : Nat → List Item → List Item
  | 0, items => items
  | fuel + 1, items =>
      let next := closureStep prods items
      if next == items then items else closure prods fuel next

def gotoState (prods : Array Prod) (fuel : Nat) (items : List Item) (sym : Sym) : List Item :=
  closure prods fuel (normalize (items.filterMap fun item =>
    if symAt prods item == some sym then some (item.1, item.2 + 1) else none))

/-- The symbols that appear after a dot in a state, in a fixed order. -/
def nextSyms (prods : Array Prod) (items : List Item) : List Sym :=
  (items.filterMap (symAt prods)).eraseDups

/-- The canonical LR(0) collection, explored breadth first; returns the states and the
transitions `(from, symbol, to)`. -/
def collection (prods : Array Prod) (fuel : Nat) :
    Nat → List (List Item) → List (Nat × Sym × Nat) → Nat → List (List Item) × List (Nat × Sym × Nat)
  | 0, states, edges, _ => (states, edges)
  | rounds + 1, states, edges, cursor =>
      if h : cursor < states.length then
        let state := states[cursor]
        let (states', edges') := (nextSyms prods state).foldl
          (fun (acc : List (List Item) × List (Nat × Sym × Nat)) sym =>
            let target := gotoState prods fuel state sym
            match acc.1.findIdx? (· == target) with
            | some index => (acc.1, acc.2 ++ [(cursor, sym, index)])
            | none => (acc.1 ++ [target], acc.2 ++ [(cursor, sym, acc.1.length)]))
          (states, edges)
        collection prods fuel rounds states' edges' (cursor + 1)
      else (states, edges)

/-! ## Nullable, FIRST and FOLLOW -/

def nullableStep (prods : List Prod) (nullable : List String) : List String :=
  (nullable ++ (prods.filterMap fun p =>
    if p.rhs.all (fun s => match s with | .nt n => nullable.contains n | _ => false)
    then some p.lhs else none)).eraseDups

def fixpoint {α : Type} [BEq α] (step : α → α) : Nat → α → α
  | 0, a => a
  | fuel + 1, a => let b := step a; if b == a then a else fixpoint step fuel b

/-- FIRST of a symbol string, given the FIRST sets of phrase sorts. -/
def firstOfSeq (nullable : List String) (first : List (String × List Sym)) : List Sym → List Sym
  | [] => []
  | .nt n :: rest =>
      let here := (first.lookup n).getD []
      if nullable.contains n then (here ++ firstOfSeq nullable first rest).eraseDups else here
  | s :: _ => [s]

def seqNullable (nullable : List String) (syms : List Sym) : Bool :=
  syms.all fun s => match s with | .nt n => nullable.contains n | _ => false

def firstStep (prods : List Prod) (nullable : List String) (first : List (String × List Sym)) :
    List (String × List Sym) :=
  let sorts := (prods.map (·.lhs)).eraseDups
  sorts.map fun sort =>
    (sort, (((first.lookup sort).getD []) ++
      (prods.filter (·.lhs == sort)).flatMap (fun p => firstOfSeq nullable first p.rhs)).eraseDups)

def followStep (prods : List Prod) (nullable : List String) (first : List (String × List Sym))
    (follow : List (String × List Sym)) : List (String × List Sym) :=
  let sorts := (prods.map (·.lhs)).eraseDups
  sorts.map fun sort =>
    let fromRows := prods.flatMap fun p =>
      (List.range p.rhs.length).flatMap fun i =>
        if p.rhs[i]? == some (.nt sort) then
          let rest := p.rhs.drop (i + 1)
          firstOfSeq nullable first rest ++
            (if seqNullable nullable rest then (follow.lookup p.lhs).getD [] else [])
        else []
    (sort, (((follow.lookup sort).getD []) ++ fromRows).eraseDups)

/-! ## Actions -/

inductive Action where
  | shift (state : Nat)
  | reduce (production : Nat)
  | accept
  deriving DecidableEq, Repr, BEq

structure Tables where
  prods : List Prod
  states : List (List Item)
  actions : List (Nat × Sym × Action)
  gotos : List (Nat × String × Nat)
  conflicts : List (Nat × Sym × List Action)
  deriving Repr

def build (prods : List Prod) : Tables :=
  let arr := prods.toArray
  let fuel := 4 * (prods.foldl (fun n p => n + p.rhs.length + 1) 1)
  let start := closure arr fuel [(0, 0)]
  let (states, edges) := collection arr fuel (64 * fuel) [start] [] 0
  let nullable := fixpoint (nullableStep prods) fuel []
  let first := fixpoint (firstStep prods nullable) fuel []
  let follow := fixpoint (followStep prods nullable first) fuel [("rdr-accept-start", [])]
  let raw : List (Nat × Sym × Action) :=
    (List.range states.length).flatMap fun s =>
      let items := states.getD s []
      let shifts := edges.filterMap fun (f, sym, t) =>
        if f == s && sym.isTerminal then
          if sym == .eof then some (s, sym, Action.accept) else some (s, sym, Action.shift t)
        else none
      let reduces := items.flatMap fun (p, d) =>
        let prod := arr.getD p default
        if p != 0 && d == prod.rhs.length then
          ((follow.lookup prod.lhs).getD []).map fun a => (s, a, Action.reduce p)
        else []
      shifts ++ reduces
  let keys := (raw.map fun (s, a, _) => (s, a)).eraseDups
  let grouped := keys.map fun (s, a) =>
    (s, a, (raw.filterMap fun (s', a', act) => if s' == s && a' == a then some act else none).eraseDups)
  let conflicts := grouped.filter fun (_, _, acts) => acts.length > 1
  let actions := grouped.filterMap fun (s, a, acts) =>
    match acts with | [act] => some (s, a, act) | _ => none
  let gotos := edges.filterMap fun (f, sym, t) =>
    match sym with | .nt n => some (f, n, t) | _ => none
  { prods, states, actions, gotos, conflicts }

/-! ## Overlapping terminals

`overlaps member a b` says one token can be both terminals; `member sort spelling` decides
whether a fixed spelling is a token of a token sort, and `classesMeet` whether two token sorts
share a token. -/

def overlaps (member : String → String → Bool) (classesMeet : String → String → Bool) :
    Sym → Sym → Bool
  | .lit x, .lit y => x == y
  | .lit x, .tok c => member c x
  | .tok c, .lit x => member c x
  | .tok c, .tok d => c == d || classesMeet c d
  | _, _ => false

/-- States in which two different overlapping terminals ask for different actions. -/
def tokenConflicts (member : String → String → Bool) (classesMeet : String → String → Bool)
    (tables : Tables) : List (Nat × Sym × Sym) :=
  tables.actions.flatMap fun (s, a, act) =>
    tables.actions.filterMap fun (s', b, act') =>
      if s == s' && a != b && overlaps member classesMeet a b && act != act' then some (s, a, b)
      else none

/-! ## Controls -/

private def rowsAB : List Prod :=
  [{ label := "rdr-accept-start", lhs := "rdr-accept-start", rhs := [.nt "s", .eof] },
   { label := "more", lhs := "s", rhs := [.lit "a", .nt "s"] },
   { label := "end", lhs := "s", rhs := [.lit "b"] }]

private def rowsAmb : List Prod :=
  [{ label := "rdr-accept-start", lhs := "rdr-accept-start", rhs := [.nt "e", .eof] },
   { label := "plus", lhs := "e", rhs := [.nt "e", .lit "+", .nt "e"] },
   { label := "x", lhs := "e", rhs := [.lit "x"] }]

/-! Executable controls, evaluated when this file is checked (the table builder uses well-founded
sorting, which the kernel does not unfold; the tables are untrusted data in any case). -/

-- Positive control: `s ::= "a" s | "b"` has a conflict-free SLR(1) table with 6 states.
#guard (build rowsAB).conflicts.isEmpty && (build rowsAB).states.length == 6

-- Negative control: the ambiguous `e ::= e "+" e | "x"` has a shift/reduce conflict on `+`.
#guard !(build rowsAmb).conflicts.isEmpty

end Mettapedia.GSLT.Readers.SLR
