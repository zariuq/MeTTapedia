import Mettapedia.GSLT.Readers.MM0.Math
import Mettapedia.GSLT.Readers.MM0.Load

/-!
# What an `.mm0` specification says each statement must be

The `.mm0` reader (generated from `MM0Syntax.module`) gives statement trees whose formulas are
math strings. This module reads them in file order, keeps the notations in a `Math.Env`, reads
every formula under the notations declared before it (`Math.Env.read`: lexer, untrusted parser,
trusted tree check, elaboration), and prints each sort, term, definition, axiom and theorem as a
canonical line: binders by position, variables as `#i`, dependencies as sorted positions.

    provable sort wff;                      (sort wff 0 0 1 0)
    term im (a b: wff): wff;                (term im ((r wff ()) (r wff ())) (r wff ()))
    infixr im: $->$ prec 25;                (no line: a notation)
    axiom ax_1 (a b: wff): $ a -> b -> a $; (axiom ax_1 ((r wff ()) (r wff ())) () (im #0 (im #1 #0)))

`MM0.Load` prints the same line for each statement of the `.mmu` proof file and requires it to be
the next line here; binder and hypothesis names are not part of a line, so statements match up to
renaming. A definition without a value in the `.mm0` gives only its header; a definition's dummy
variables are numbered after its arguments in order of first occurrence, with their sorts listed.
Input and output statements are refused (not supported).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.MM0.Expect

open Mettapedia.GSLT.Readers.Metamath.Load (SX)
open Mettapedia.GSLT.Readers.MM0.Load (tok? depsText)
open Mettapedia.GSLT.Readers.MM0.Math

/-! ## Statement trees -/

/-- One variable of a binder group: its name (`none` when blank or anonymous), sort, whether it is
a bound variable, its dependencies by name, whether it is a dummy. -/
structure B where
  name : Option String
  sort : String
  bound : Bool
  deps : List String
  dummy : Bool
  deriving Repr

/-- A binder group of an axiom or theorem: variables, or hypotheses (one formula per name). -/
inductive Group where
  | vars (bs : List B)
  | hyps (count : Nat) (formula : String)
  deriving Repr

/-- The end of an arrow: a type (`sort deps`) or, for an assertion, a formula. -/
inductive ArrowItem where
  | type (sort : String) (deps : List String)
  | formula (math : String)
  deriving Repr

inductive Stmt where
  | sort (name : String) (mods : List Bool)
  | term (name : String) (groups : List Group) (arrow : List ArrowItem)
  | def_ (name : String) (groups : List Group) (arrow : List ArrowItem) (value : Option String)
  | assert (kind : String) (name : String) (groups : List Group) (arrow : List ArrowItem)
  | delimiter (left right : String)
  | prefix_ (term : String) (tok : String) (prec : Prec)
  | infix_ (right : Bool) (term : String) (tok : String) (prec : Prec)
  | coercion (term src tgt : String)
  | notation (term : String) (groups : List Group) (ret : ArrowItem) (head : String) (prec : Prec)
      (items : List (Sum (String × Prec) String))
  | io (kind : String)
  deriving Repr

partial def idsOf : SX → Option (List String)
  | .list [.atom "ids_empty"] => some []
  | .list [.atom "ids_more", x, rest] => do pure ((← tok? x) :: (← idsOf rest))
  | _ => none

/-- Names that may be blank (`_` is `none`). -/
partial def bidsOf : SX → Option (List (Option String))
  | .list [.atom "bids_empty"] => some []
  | .list [.atom "bids_more", x, rest] => do pure (some (← tok? x) :: (← bidsOf rest))
  | .list [.atom "bids_blank", rest] => do pure (none :: (← bidsOf rest))
  | _ => none

def typOf : SX → Option (String × List String)
  | .list [.atom "typ_deps", s, deps] => do pure ((← tok? s), (← idsOf deps))
  | _ => none

partial def arrowOf : SX → Option (List ArrowItem)
  | .list [.atom "arrow_last", t] => do let (s, d) ← typOf t; pure [.type s d]
  | .list [.atom "arrow_more", t, rest] => do let (s, d) ← typOf t; pure (.type s d :: (← arrowOf rest))
  | _ => none

partial def farrowOf : SX → Option (List ArrowItem)
  | .list [.atom "farrow_last", m] => do pure [.formula (← tok? m)]
  | .list [.atom "farrow_type", t, rest] => do let (s, d) ← typOf t; pure (.type s d :: (← farrowOf rest))
  | .list [.atom "farrow_hyp", m, rest] => do pure (.formula (← tok? m) :: (← farrowOf rest))
  | _ => none

def varsGroup (names : List (Option String)) (bound : Bool) (t : String × List String) : Group :=
  .vars (names.map fun n => ⟨n, t.1, bound, t.2, false⟩)

def groupOf : SX → Option Group
  | .list [.atom "tbinder_bound", ids, t] => do pure (varsGroup ((← idsOf ids).map some) true (← typOf t))
  | .list [.atom "tbinder_regular", bids, t] => do pure (varsGroup (← bidsOf bids) false (← typOf t))
  | .list [.atom "fbinder_bound", ids, t] => do pure (varsGroup ((← idsOf ids).map some) true (← typOf t))
  | .list [.atom "fbinder_regular", bids, t] => do pure (varsGroup (← bidsOf bids) false (← typOf t))
  | .list [.atom "fbinder_hyp", bids, m] => do pure (.hyps (← bidsOf bids).length (← tok? m))
  | _ => none

partial def groupsOf (more empty : String) : SX → Option (List Group)
  | .list [.atom l] => if l == empty then some [] else none
  | .list [.atom l, g, rest] => if l == more then do pure ((← groupOf g) :: (← groupsOf more empty rest)) else none
  | _ => none

/-- A dummy identifier: `.x` (a dummy), `x`, or `_`. -/
def dummyIdOf : SX → Option (Option String × Bool)
  | .list [.atom "dummy_dot", x] => do pure (some (← tok? x), true)
  | .list [.atom "dummy_plain", x] => do pure (some (← tok? x), false)
  | .list [.atom "dummy_blank"] => some (none, false)
  | _ => none

partial def dummyIdsOf : SX → Option (List (Option String × Bool))
  | .list [.atom "dummy_ids_empty"] => some []
  | .list [.atom "dummy_ids_more", d, rest] => do pure ((← dummyIdOf d) :: (← dummyIdsOf rest))
  | _ => none

def dgroupOf : SX → Option Group
  | .list [.atom k, ids, t] =>
      if k == "dbinder_bound" || k == "dbinder_regular" then do
        let (s, deps) ← typOf t
        let bound := k == "dbinder_bound"
        pure (.vars ((← dummyIdsOf ids).map fun (n, dummy) => ⟨n, s, bound || dummy, deps, dummy⟩))
      else none
  | _ => none

partial def dgroupsOf : SX → Option (List Group)
  | .list [.atom "dbinders_empty"] => some []
  | .list [.atom "dbinders_more", g, rest] => do pure ((← dgroupOf g) :: (← dgroupsOf rest))
  | _ => none

def precOf : SX → Option Prec
  | .list [.atom "prec_number", n] => do
      let k ← (← tok? n).toNat?
      if k ≤ precBound then some (.num k) else none
  | .list [.atom "prec_zero"] => some (.num 0)
  | .list [.atom "prec_max"] => some .max
  | _ => none

def precConstOf : SX → Option (String × Prec)
  | .list [.atom "prec_const_one", m, p] => do pure ((← tok? m), (← precOf p))
  | _ => none

partial def nlitsOf : SX → Option (List (Sum (String × Prec) String))
  | .list [.atom "nlits_empty"] => some []
  | .list [.atom "nlits_more", .list [.atom "nlit_const", c], rest] => do
      pure (.inl (← precConstOf c) :: (← nlitsOf rest))
  | .list [.atom "nlits_more", .list [.atom "nlit_var", x], rest] => do
      pure (.inr (← tok? x) :: (← nlitsOf rest))
  | _ => none

def flagOf (yes : String) : SX → Bool
  | .list [.atom l] => l == yes
  | _ => false

def stmtOf : SX → Option Stmt
  | .list [.atom "statement_sort", p, s, v, f, n] =>
      do pure (.sort (← tok? n) [flagOf "pure_yes" p, flagOf "strict_yes" s, flagOf "provable_yes" v, flagOf "free_yes" f])
  | .list [.atom "statement_term", n, bs, a] =>
      do pure (.term (← tok? n) (← groupsOf "tbinders_more" "tbinders_empty" bs) (← arrowOf a))
  | .list [.atom "statement_axiom", n, bs, a] =>
      do pure (.assert "axiom" (← tok? n) (← groupsOf "fbinders_more" "fbinders_empty" bs) (← farrowOf a))
  | .list [.atom "statement_theorem", n, bs, a] =>
      do pure (.assert "theorem" (← tok? n) (← groupsOf "fbinders_more" "fbinders_empty" bs) (← farrowOf a))
  | .list [.atom "statement_def_abstract", n, bs, a] =>
      do pure (.def_ (← tok? n) (← dgroupsOf bs) (← arrowOf a) none)
  | .list [.atom "statement_def_value", n, bs, a, v] =>
      do pure (.def_ (← tok? n) (← dgroupsOf bs) (← arrowOf a) (some (← tok? v)))
  | .list [.atom "statement_delimiter_both", m] => do let m ← tok? m; pure (.delimiter m m)
  | .list [.atom "statement_delimiter_lr", l, r] => do pure (.delimiter (← tok? l) (← tok? r))
  | .list [.atom "statement_prefix", n, m, p] => do pure (.prefix_ (← tok? n) (← tok? m) (← precOf p))
  | .list [.atom "statement_infixl", n, m, p] => do pure (.infix_ false (← tok? n) (← tok? m) (← precOf p))
  | .list [.atom "statement_infixr", n, m, p] => do pure (.infix_ true (← tok? n) (← tok? m) (← precOf p))
  | .list [.atom "statement_coercion", n, a, b] => do pure (.coercion (← tok? n) (← tok? a) (← tok? b))
  | .list [.atom "statement_notation", n, bs, t, c, items] => do
      let (s, d) ← typOf t
      let (head, p) ← precConstOf c
      pure (.notation (← tok? n) (← groupsOf "tbinders_more" "tbinders_empty" bs) (.type s d) head p (← nlitsOf items))
  | .list [.atom "statement_input", k, _] => do pure (.io (← tok? k))
  | .list [.atom "statement_output", k, _] => do pure (.io (← tok? k))
  | _ => none

/-! ## Canonical lines -/

/-- A math string's single constant token (a notation constant: `$ -> $`). -/
def constOf (m : String) : Except String String :=
  match (inside m).splitOn " " |>.flatMap (·.splitOn "\n") |>.filter (· != "") with
  | [t] => .ok t
  | _ => .error s!"{m} is not one token"

/-- The words of a delimiter statement's math string. -/
def wordsOf (m : String) : List String :=
  (inside m).splitOn " " |>.flatMap (·.splitOn "\n") |>.filter (· != "")

/-- An expression as a canonical text: variables by position (`#i`), applications in parentheses. -/
partial def exprText (pos : String → Option Nat) : EExpr → Except String String
  | .var x => match pos x with
      | some i => .ok s!"#{i}"
      | none => .error s!"variable {x} has no position"
  | .app f args => do
      let parts ← args.mapM (exprText pos)
      pure ("(" ++ " ".intercalate (f :: parts) ++ ")")

/-- The positions of a statement's variables: arguments first, then (for a definition's value)
dummies in order of first occurrence. -/
partial def dummyOrder (isDummy : String → Bool) : EExpr → List String → List String
  | .var x, acc => if isDummy x && !acc.contains x then acc ++ [x] else acc
  | .app _ args, acc => args.foldl (fun acc e => dummyOrder isDummy e acc) acc


/-- The state of a reading: the notation environment, the canonical binders of each term (for the
`notation` check), the lines so far. -/
structure State where
  env : Env := {}
  sigs : List (String × String) := []
  lines : Array String := #[]
  deriving Inhabited

/-- A statement's binders: the arguments in order (with their canonical text), the dummies, the
hypotheses. Dependencies must name earlier bound arguments; hypotheses follow the variables. -/
structure Binders where
  args : List B := []
  dummies : List B := []
  hyps : List String := []
  deriving Inhabited

def Binders.add (bs : Binders) (b : B) : Except String Binders := do
  if !bs.hyps.isEmpty then throw "a variable after a hypothesis"
  if b.bound && !b.deps.isEmpty then throw "a bound variable with dependencies"
  if b.dummy && !b.deps.isEmpty then throw "a dummy with dependencies"
  for d in b.deps do
    if !(bs.args.any fun a => a.name == some d && a.bound) then throw s!"{d} is not an earlier bound variable"
  if let some n := b.name then
    if (bs.args ++ bs.dummies).any (·.name == some n) then throw s!"variable {n} declared twice"
  if b.dummy then pure { bs with dummies := bs.dummies ++ [b] } else pure { bs with args := bs.args ++ [b] }

def Binders.ofGroups (groups : List Group) : Except String Binders :=
  groups.foldlM (fun bs g => match g with
    | .vars vs => vs.foldlM Binders.add bs
    | .hyps k m => pure { bs with hyps := bs.hyps ++ List.replicate k m }) {}

def Binders.pos (bs : Binders) (x : String) : Option Nat := bs.args.findIdx? (·.name == some x)

def Binders.binderText (bs : Binders) (b : B) : String :=
  if b.bound then s!"(b {b.sort})"
  else s!"(r {b.sort} {depsText (b.deps.filterMap bs.pos)})"

def Binders.argsText (bs : Binders) : String :=
  "(" ++ " ".intercalate (bs.args.map bs.binderText) ++ ")"

def Binders.scope (bs : Binders) : List Var :=
  (bs.args ++ bs.dummies).filterMap fun b => b.name.map fun n => ⟨n, b.sort, b.bound⟩

def State.checkSort (st : State) (s : String) : Except String Unit :=
  if st.env.sorts.any (·.1 == s) then .ok () else .error s!"unknown sort {s}"

/-- A term's or definition's binders with its arrow: the arrow's types before the last are
anonymous arguments, the last is the sort. -/
def termBinders (st : State) (groups : List Group) (arrow : List ArrowItem) :
    Except String (Binders × String × List String) := do
  let mut bs ← Binders.ofGroups groups
  let mut ret : Option (String × List String) := none
  for (item, k) in arrow.zip (List.range arrow.length) do
    match item with
    | .type s deps =>
        if k + 1 == arrow.length then ret := some (s, deps)
        else bs ← bs.add ⟨none, s, false, deps, false⟩
    | .formula _ => throw "a formula in a term's type"
  let some (s, deps) := ret | throw "no sort"
  for b in bs.args ++ bs.dummies do st.checkSort b.sort
  st.checkSort s
  for d in deps do
    if !(bs.args.any fun a => a.name == some d && a.bound) then throw s!"{d} is not a bound argument"
  pure (bs, s, deps)

def retText (bs : Binders) (s : String) (deps : List String) : String :=
  s!"(r {s} {depsText (deps.filterMap bs.pos)})"

/-- Read one statement: notations change the environment; the others print their line. -/
def step (st : State) : Stmt → Except String State
  | .sort n mods => do
      if st.env.sorts.any (·.1 == n) then throw s!"sort {n} declared twice"
      let bit := fun (b : Bool) => if b then "1" else "0"
      let env := { st.env with sorts := st.env.sorts ++ [(n, mods.getD 2 false)] }
      pure { st with env, lines := st.lines.push s!"(sort {n} {" ".intercalate (mods.map bit)})" }
  | .term n groups arrow => do
      if (st.env.term? n).isSome then throw s!"term {n} declared twice"
      let (bs, s, deps) ← termBinders st groups arrow
      if !bs.hyps.isEmpty || !bs.dummies.isEmpty then throw s!"{n}: hypotheses or dummies in a term"
      let env := { st.env with terms := st.env.terms ++ [⟨n, bs.args.map (fun b => (b.sort, b.bound)), s⟩] }
      let sig := s!"{bs.argsText} {retText bs s deps}"
      pure { st with env, sigs := st.sigs ++ [(n, sig)], lines := st.lines.push s!"(term {n} {sig})" }
  | .def_ n groups arrow value => do
      if (st.env.term? n).isSome then throw s!"term {n} declared twice"
      let (bs, s, deps) ← termBinders st groups arrow
      let sig := s!"{bs.argsText} {retText bs s deps}"
      let line ← match value with
        | none => pure s!"(def {n} {sig})"
        | some m => do
            let (e, s') ← st.env.read bs.scope m
            let e ← st.env.coerce e s' s
            let dummyNames := bs.dummies.filterMap (·.name)
            let order := dummyOrder (dummyNames.contains ·) e []
            let pos := fun x => match bs.pos x with
              | some i => some i
              | none => (order.findIdx? (· == x)).map (bs.args.length + ·)
            let sorts := order.filterMap fun x => (bs.dummies.find? (·.name == some x)).map (·.sort)
            pure s!"(def {n} {sig} ({" ".intercalate sorts}) {← exprText pos e})"
      -- the definition is in scope from here on, not in its own value
      let env := { st.env with terms := st.env.terms ++ [⟨n, bs.args.map (fun b => (b.sort, b.bound)), s⟩] }
      pure { st with env, sigs := st.sigs ++ [(n, sig)], lines := st.lines.push line }
  | .assert kind n groups arrow => do
      let mut bs ← Binders.ofGroups groups
      let mut concl : Option String := none
      for (item, k) in arrow.zip (List.range arrow.length) do
        match item with
        | .type s deps => bs ← bs.add ⟨none, s, false, deps, false⟩
        | .formula m =>
            if k + 1 == arrow.length then concl := some m
            else bs := { bs with hyps := bs.hyps ++ [m] }
      let some c := concl | throw s!"{n}: no conclusion"
      for b in bs.args do st.checkSort b.sort
      let formula := fun (m : String) => do
        let (e, s) ← st.env.read bs.scope m
        let e ← st.env.toProvable e s
        exprText bs.pos e
      let hs ← bs.hyps.mapM formula
      let c ← formula c
      pure { st with lines := st.lines.push s!"({kind} {n} {bs.argsText} ({" ".intercalate hs}) {c})" }
  | .delimiter l r => do
      let env ← st.env.addDelimiters (wordsOf l) (wordsOf r)
      pure { st with env }
  | .prefix_ f m p => do pure { st with env := ← st.env.addPrefix f (← constOf m) p }
  | .infix_ right f m p => do pure { st with env := ← st.env.addInfix right f (← constOf m) p }
  | .coercion f a b => do pure { st with env := ← st.env.addCoercion f a b }
  | .notation f groups ret head p items => do
      let (bs, s, deps) ← termBinders st groups [ret]
      let some sig := st.sigs.lookup f | throw s!"unknown term {f}"
      if s!"{bs.argsText} {retText bs s deps}" != sig then throw s!"notation {f}: binders differ from the term's"
      let names := bs.args.map fun b => b.name.getD "_"
      let items ← items.mapM fun i => match i with
        | .inl (m, q) => do pure (NLit.const (← constOf m) q)
        | .inr x => pure (NLit.var x)
      pure { st with env := ← st.env.addNotation f names (← constOf head) p items }
  | .io k => .error s!"{k}: input and output statements are not supported"

/-- The canonical lines of a specification's statement items, or the first item that cannot be
decoded or read. -/
def expect (items : List SX) : Except String (Array String) := do
  let mut st : State := {}
  for (x, k) in items.zip (List.range items.length) do
    match stmtOf x with
    | none => throw s!"unreadable statement item {k}"
    | some s =>
        match step st s with
        | .ok st' => st := st'
        | .error e => throw s!"statement {k}: {e}"
  pure st.lines

end Mettapedia.GSLT.Readers.MM0.Expect
