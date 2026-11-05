/-!
# Erased code equations

Lean computes a definition by the equation theorems it proves about it:
`List.map.eq_2 : List.map f (h :: t) = f h :: List.map f t`. Erasing types,
proofs and universe levels from such a theorem leaves a rewrite rule that
an untyped language can run. This module is the target side of that
erasure: erased terms, the patterns of an equation's left side, a
function's equations as one first-match list, and their printing as PeTTa
MeTTa.

A function's equations are listed in Lean's order. A later equation of an
overlapping definition carries hypotheses saying that the earlier patterns
did not match; the list discharges them by trying the equations in order.
PeTTa fires every matching rule, so the whole list becomes one rule whose
body is a first-match `case`.

Natural numbers are PeTTa integers. A pattern `n + k` (Lean's `Nat.succ`
applied `k` times) matches a number at least `k` and binds `n` to the
difference; it is compiled to a guard, because PeTTa patterns cannot
compute.

Every Lean name becomes a PeTTa symbol. The spelling keeps the familiar
dotted form and escapes every character that is not safe in a symbol; the
exporter refuses an export in which two names share a symbol.
-/

namespace Mettapedia.Languages.Lean.CodeEquations

/-! ## Names -/

/-- Characters kept as they are in a symbol component. `%` (the escape),
`.` (the separator) and `#` (the number marker) are never safe. -/
def safeChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' ||
    (c.toNat > 127 && c.toNat != 0x2E && !c.isWhitespace)

/-- Six lowercase hexadecimal digits of a code point (code points are below
`0x110000`, so six digits always suffice). -/
def hex6 (n : Nat) : String :=
  let d (i : Nat) : Char :=
    let v := (n / 16 ^ i) % 16
    if v < 10 then Char.ofNat (48 + v) else Char.ofNat (87 + v)
  String.ofList [d 5, d 4, d 3, d 2, d 1, d 0]

/-- One escaped character: itself when safe, otherwise `%` and six hex
digits of its code point. -/
def escapeChar (c : Char) : String :=
  if safeChar c then c.toString else "%" ++ hex6 c.toNat

/-- A string component, escaped character by character. -/
def escapeComponent (s : String) : String :=
  String.join (s.toList.map escapeChar)

/-- A Lean name as a PeTTa symbol: components joined by `.`, a numeric
component written `#n`. A name in the root namespace starts with `%`, so it
cannot meet a symbol of the target's own (PeTTa defines `id`, `max`, `not`
and others); `%` never occurs in an escaped component. The anonymous name is
`%anonymous`. -/
def encodeName (n : Lean.Name) : String :=
  match n with
  | .anonymous => "%anonymous"
  | .str .anonymous s => "%" ++ escapeComponent s
  | .num .anonymous k => "%#" ++ toString k
  | _ => ".".intercalate (parts n [])
where
  /-- The escaped components of a name, outermost first. -/
  parts : Lean.Name → List String → List String
    | .anonymous, acc => acc
    | .str p s, acc => parts p (escapeComponent s :: acc)
    | .num p k, acc => parts p (("#" ++ toString k) :: acc)

/-! ## Erased terms -/

/-- A pattern on the left side of an erased equation. -/
inductive EPat where
  /-- A variable, bound to the argument. -/
  | var (name : String)
  /-- A position whose value the equation does not inspect. -/
  | wild
  /-- A natural number literal. -/
  | nat (n : Nat)
  /-- `p + k` for a natural number: matches numbers `≥ k`, binding `p` to
  the difference. `k > 0`. -/
  | succ (k : Nat) (p : EPat)
  /-- A constructor applied to patterns for its kept fields. -/
  | ctor (name : Lean.Name) (args : List EPat)
  deriving Inhabited, Repr, BEq

/-- An erased term: what remains of a Lean term after types, proofs and
universe levels are gone. -/
inductive ETerm where
  /-- A variable. -/
  | var (name : String)
  /-- A natural number literal. -/
  | nat (n : Nat)
  /-- A string literal. -/
  | str (s : String)
  /-- An erased argument kept in position (a type or a proof passed where the
  signature keeps the argument). -/
  | erased
  /-- A named function or constructor, applied to arguments. With fewer
  arguments than its arity it is a partial application; a nullary function
  is the call `(f)`, a nullary constructor its bare symbol. -/
  | app (head : Lean.Name) (nullary : Bool) (args : List ETerm)
  /-- A function value applied to arguments. -/
  | apv (fn : ETerm) (args : List ETerm)
  /-- `fun x₁ … xₙ => body`. -/
  | lam (params : List String) (body : ETerm)
  /-- A lazy conditional on a Boolean value. -/
  | ite (c t e : ETerm)
  /-- A strict `let`. -/
  | letE (name : String) (value body : ETerm)
  /-- A first-match case over the values of several terms. -/
  | case (scrutinees : List ETerm) (alts : List (List EPat × ETerm)) (fallback : Option ETerm)
  /-- A primitive operation of the target, written as its symbol. -/
  | prim (op : String) (args : List ETerm)
  deriving Inhabited, Repr

/-- One equation theorem, erased: the patterns of its left side over the
function's kept parameters, its right side, and the theorem it came from. -/
structure EBranch where
  pats : List EPat
  rhs : ETerm
  theorem_ : Lean.Name
  deriving Inhabited, Repr

/-- A function's code: its kept arity and its equations in first-match order. -/
structure EFunction where
  name : Lean.Name
  arity : Nat
  branches : List EBranch
  deriving Inhabited, Repr

/-! ## Printing as PeTTa -/

/-- A PeTTa string literal. -/
def quoteString (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | c => c.toString) ++ "\""

/-- A PeTTa variable. Pattern and parameter names are already safe; any
other character is escaped like a name component. -/
def varName (x : String) : String := "$" ++ escapeComponent x

/-- How a constructor's symbol is spelled: Lean's Booleans are PeTTa's. -/
def ctorSymbol (n : Lean.Name) : String :=
  if n == ``Bool.true then "true"
  else if n == ``Bool.false then "false"
  else encodeName n

def EPat.render : EPat → String
  | .var x => varName x
  | .wild => "$_"
  | .nat n => toString n
  | .succ _ p => p.render
  | .ctor c [] => ctorSymbol c
  | .ctor c args => "(" ++ " ".intercalate (ctorSymbol c :: args.map EPat.render) ++ ")"

partial def ETerm.render : ETerm → String
  | .var x => varName x
  | .nat n => toString n
  | .str s => quoteString s
  | .erased => "erased"
  | .app h true [] => ctorSymbol h
  | .app h false [] => "(" ++ encodeName h ++ ")"
  | .app h _ args => "(" ++ " ".intercalate (ctorSymbol h :: args.map ETerm.render) ++ ")"
  | .apv f [] => f.render
  | .apv f args => "(" ++ " ".intercalate (f.render :: args.map ETerm.render) ++ ")"
  | .lam ps b => "(|-> (" ++ " ".intercalate (ps.map varName) ++ ") " ++ b.render ++ ")"
  | .ite c t e => "(if " ++ c.render ++ " " ++ t.render ++ " " ++ e.render ++ ")"
  | .letE x v b => "(let " ++ varName x ++ " " ++ v.render ++ " " ++ b.render ++ ")"
  | .case ss alts fb =>
      let scrut := "(lean-args " ++ " ".intercalate (ss.map ETerm.render) ++ ")"
      let alt (a : List EPat × ETerm) :=
        "((lean-args " ++ " ".intercalate (a.1.map EPat.render) ++ ") " ++ a.2.render ++ ")"
      let fbAlt := match fb with
        | some e => [s!"($lean-otherwise {e.render})"]
        | none => []
      "(case " ++ scrut ++ " (" ++ " ".intercalate (alts.map alt ++ fbAlt) ++ "))"
  | .prim op [] => "(" ++ op ++ ")"
  | .prim op args => "(" ++ " ".intercalate (op :: args.map ETerm.render) ++ ")"

/-! ## First-match lists -/

/-- The guards a pattern needs: each `succ k p` at a variable position becomes
"the value is at least `k`", binding `p` to the value minus `k`. Returns the
pattern with every `succ` replaced by a fresh variable, and the guards as
(variable, k, inner pattern) in order. -/
partial def EPat.splitSucc (fresh : Nat) : EPat → EPat × List (String × Nat × EPat) × Nat
  | .succ k p =>
      let v := s!"lean_n{fresh}"
      (.var v, [(v, k, p)], fresh + 1)
  | .ctor c args =>
      let (args', gs, f) := args.foldl (fun (acc : List EPat × List (String × Nat × EPat) × Nat) a =>
        let (p, g, f') := a.splitSucc acc.2.2
        (acc.1 ++ [p], acc.2.1 ++ g, f')) ([], [], fresh)
      (.ctor c args', gs, f)
  | p => (p, [], fresh)

/-- The body of one branch under its guards: each guard tests the bound
number and, when it holds, binds the inner pattern (a variable, or a further
nested pattern matched by a one-alternative case); otherwise the list goes
on with `rest`. -/
partial def guarded (gs : List (String × Nat × EPat)) (body rest : ETerm) : ETerm :=
  match gs with
  | [] => body
  | (v, k, inner) :: more =>
      let pred := ETerm.prim "-" [.var v, .nat k]
      let inside := guarded more body rest
      let bound := match inner with
        | .var x => ETerm.letE x pred inside
        | .wild => inside
        | p => ETerm.case [pred] [([p], inside)] (some rest)
      .ite (.prim ">=" [.var v, .nat k]) bound rest

/-- A function's equations as one first-match term over its parameters.
Branches without guards share one `case`; a guarded branch continues with the
remaining branches when its guard fails. -/
partial def compileBranches (params : List String) (bs : List EBranch) : ETerm :=
  match bs with
  | [] => .prim "empty" []
  | _ =>
    let args := params.map ETerm.var
    let rec plainRun (bs : List EBranch) (acc : List (List EPat × ETerm)) :
        List (List EPat × ETerm) × List EBranch :=
      match bs with
      | b :: more =>
          let (pats, gs, _) := b.pats.foldl (fun (st : List EPat × List (String × Nat × EPat) × Nat) p =>
            let (p', g, f') := p.splitSucc st.2.2
            (st.1 ++ [p'], st.2.1 ++ g, f')) ([], [], 0)
          if gs.isEmpty then plainRun more (acc ++ [(pats, b.rhs)]) else (acc, bs)
      | [] => (acc, [])
    let (plain, rest) := plainRun bs []
    match rest with
    | [] => .case args plain (some (.prim "empty" []))
    | b :: more =>
        let (pats, gs, _) := b.pats.foldl (fun (st : List EPat × List (String × Nat × EPat) × Nat) p =>
          let (p', g, f') := p.splitSucc st.2.2
          (st.1 ++ [p'], st.2.1 ++ g, f')) ([], [], 0)
        let after := compileBranches params more
        let here := ETerm.case args [(pats, guarded gs b.rhs after)] (some after)
        if plain.isEmpty then here else .case args plain (some here)

/-- The PeTTa rule of a function: `(= (f $p₁ … $pₙ) body)`. A nullary
function is the call `(f)`. -/
def EFunction.render (f : EFunction) : String :=
  let params := (List.range f.arity).map (fun i => s!"lean_a{i}")
  let head := if f.arity == 0 then "(" ++ encodeName f.name ++ ")"
    else "(" ++ " ".intercalate (encodeName f.name :: params.map varName) ++ ")"
  let body := compileBranches params f.branches
  "(= " ++ head ++ " " ++ body.render ++ ")"

/-! ## Controls -/

#guard encodeName `List.map == "List.map"
#guard encodeName `instHAdd == "%instHAdd"
#guard encodeName (.str .anonymous "a.b") == "%a%00002eb"
#guard encodeName (.num `x 3) == "x.#3"
#guard (EFunction.render { name := `List.length, arity := 1, branches :=
    [{ pats := [.ctor `List.nil []], rhs := .nat 0, theorem_ := `List.length.eq_1 },
     { pats := [.ctor `List.cons [.var "head", .var "tail"]],
       rhs := .prim "+" [.app `List.length false [.var "tail"], .nat 1], theorem_ := `List.length.eq_2 }] }) ==
  "(= (List.length $lean_a0) (case (lean-args $lean_a0) (((lean-args List.nil) 0) ((lean-args (List.cons $head $tail)) (+ (List.length $tail) 1)) ($lean-otherwise (empty)))))"

end Mettapedia.Languages.Lean.CodeEquations
