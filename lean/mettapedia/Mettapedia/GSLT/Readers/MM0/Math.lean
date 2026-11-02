import Mettapedia.GSLT.Readers.TreeCheck

/-!
# MM0 math strings: the secondary lexer, the notation grammar, elaboration

An `.mm0` formula is a math string, `$ ... $`, read under the notations the file has declared
before it (mm0.md, "Notations" and "Grammar for math strings"):

    infixr im: $->$ prec 25;   prefix not: $~$ prec 40;
    $ ~ a -> b $   reads as   im (not a) b

Three layers, each the specification of the C code that runs it:

* `mathTokens`: split at whitespace, after every left delimiter and before every right delimiter
  (`a*b(**{}) c` with `(` left, `)` right and `*` both gives `a * b( * * {} ) c`).
* `Env.grammar`: the expression grammar of mm0.md as a token-level `TreeCheck.Grammar` with one
  phrase sort `E.p` per precedence the notations use: parentheses and variables at `max`,
  applications `f e₁ … eₙ` at 1024 (a term with no arguments at `max`, as the reference verifiers
  read it), one production per `prefix`/`notation` head and per `infixl`/`infixr` operator, and
  `E.a → E.b` for `a < b`. A math string's tree is accepted only by `TreeCheck.check` over this
  grammar, whose agreement with derivations is `TreeCheck.check_iff`; `grammar_wellFormed` gives
  its hypothesis for every grammar built here. The parser (`parse`) is not trusted.
* `elabTree`: a checked tree to an expression, inserting coercions along the unique coercion path.

The declarations are checked as MM0 requires (`Env.addPrefix`, `Env.addInfix`,
`Env.addNotation`, `Env.addCoercion`): one precedence per constant, one associativity per level
(a prefix, or a notation ending in a variable, counts as right-associative), a `prefix` or
`notation` head used once, never an operator and never after a variable, an operator declared once
(it may also follow a variable in a notation, at its one precedence: both are mm0.md's infixy
constants), infix precedences below `max`, `(` and `)` never declared, the coercion graph acyclic
as an undirected graph and reaching at most one provable sort from each sort.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.MM0.Math

open Mettapedia.GSLT.Readers.SLR (Sym Prod)
open Mettapedia.GSLT.Readers.TreeCheck (Tree Grammar)

/-! ## Precedences -/

/-- A precedence: a number, or `max` above every number. -/
inductive Prec where
  | num (n : Nat)
  | max
  deriving DecidableEq, Repr, Inhabited

def Prec.le : Prec → Prec → Bool
  | _, .max => true
  | .max, .num _ => false
  | .num a, .num b => decide (a ≤ b)

def Prec.lt (a b : Prec) : Bool := a.le b && a != b

/-- One above (only taken below `max`). -/
def Prec.succ : Prec → Prec
  | .num n => .num (n + 1)
  | .max => .max

def Prec.name : Prec → String
  | .num n => toString n
  | .max => "max"

/-- The phrase sort of expressions at a precedence. -/
def lvl (p : Prec) : String := "E." ++ p.name

def appPrec : Prec := .num 1024

/-- The largest precedence number accepted (MM0 asks for at least 2046). -/
def precBound : Nat := 65534

/-! ## The secondary lexer -/

def isMathSpace (b : Nat) : Bool := b == 32 || b == 10

/-- `cur` is the current token, last byte first. A cut falls between two bytes of a run when the
first is a left delimiter or the second a right delimiter. -/
def lexGo (left right : List Nat) : List Nat → List Nat → List (List Nat)
  | cur, [] => if cur.isEmpty then [] else [cur.reverse]
  | cur, b :: rest =>
      if isMathSpace b then
        (if cur.isEmpty then [] else [cur.reverse]) ++ lexGo left right [] rest
      else match cur with
        | [] => lexGo left right [b] rest
        | last :: _ =>
            if left.contains last || right.contains b then cur.reverse :: lexGo left right [b] rest
            else lexGo left right (b :: cur) rest

def ofBytes (bs : List Nat) : String := String.ofList (bs.map Char.ofNat)

def bytesOf (s : String) : List Nat := s.toList.map Char.toNat

/-- The tokens of a math string's inside (the text between its `$`s). -/
def mathTokens (left right : List Nat) (text : String) : List String :=
  (lexGo left right [] (bytesOf text)).map ofBytes

/-- A math string token `$ ... $` without its `$`s. -/
def inside (s : String) : String := String.ofList ((s.toList.drop 1).dropLast)

/-! ## Notations -/

/-- A notation's item after its head: a constant, or the argument with this index read at this
precedence. -/
inductive Lit where
  | const (tok : String)
  | var (index : Nat) (prec : Prec)
  deriving DecidableEq, Repr

/-- A term or definition as math strings see it: its arguments' sorts (and which are bound
variables) and its sort. -/
structure TermSig where
  name : String
  args : List (String × Bool)
  ret : String
  deriving Repr

/-- A `prefix` or `notation`: its head constant, its precedence, its term, its items. -/
structure Notation where
  head : String
  prec : Prec
  term : String
  lits : List Lit
  deriving Repr

structure Infix where
  tok : String
  prec : Nat
  term : String
  right : Bool
  deriving Repr

structure Coercion where
  term : String
  src : String
  tgt : String
  deriving Repr

/-- What the math strings of a file see at a point: delimiters, constants with their precedence,
the constants that follow a variable in a notation (infixy), notations, infix operators, the
associativity of each level, terms, coercions, and the sorts (with `provable`). -/
structure Env where
  left : List Nat := []
  right : List Nat := []
  consts : List (String × Prec) := []
  infixy : List String := []
  notations : List Notation := []
  infixes : List Infix := []
  assoc : List (Prec × Bool) := []
  terms : List TermSig := []
  coercions : List Coercion := []
  sorts : List (String × Bool) := []
  deriving Repr, Inhabited

def Env.term? (env : Env) (f : String) : Option TermSig := env.terms.find? (·.name == f)
def Env.notation? (env : Env) (c : String) : Option Notation := env.notations.find? (·.head == c)
def Env.infix? (env : Env) (c : String) : Option Infix := env.infixes.find? (·.tok == c)
def Env.isConst (env : Env) (t : String) : Bool := t == "(" || t == ")" || env.consts.any (·.1 == t)
def Env.isHead (env : Env) (t : String) : Bool :=
  (env.notation? t).isSome || (env.infix? t).isSome
def Env.provable (env : Env) (s : String) : Bool := env.sorts.any (fun (n, p) => n == s && p)

/-- Every constant has one precedence. -/
def Env.setPrec (env : Env) (tok : String) (p : Prec) : Except String Env :=
  if tok == "(" || tok == ")" then .error "( and ) are not declared as tokens"
  else match env.consts.lookup tok with
    | some q => if q == p then .ok env else .error s!"two precedences for {tok}"
    | none => .ok { env with consts := env.consts ++ [(tok, p)] }

/-- One associativity per level. -/
def Env.setAssoc (env : Env) (p : Prec) (right : Bool) : Except String Env :=
  match env.assoc.lookup p with
  | some r => if r == right then .ok env else .error s!"level {p.name} both left and right associative"
  | none => .ok { env with assoc := env.assoc ++ [(p, right)] }

/-- A `prefix` or `notation` head is new: no notation or operator has it, and no notation has it
after a variable (mm0.md: the first token is not shared with a prefix or infixy constant). -/
def Env.newHead (env : Env) (tok : String) : Except String Unit :=
  if env.isHead tok then .error s!"{tok} is already a notation or an operator"
  else if env.infixy.contains tok then .error s!"{tok} follows a variable in a notation"
  else .ok ()

/-- `prefix f: $c$ prec p`: `c e₁ … eₙ` with the last argument at `p`, the others at `max`. -/
def Env.addPrefix (env : Env) (f tok : String) (p : Prec) : Except String Env := do
  let some t := env.term? f | throw s!"unknown term {f}"
  env.newHead tok
  let env ← env.setPrec tok p
  let n := t.args.length
  let lits := (List.range n).map fun i => Lit.var i (if i + 1 == n then p else .max)
  let env ← if n > 0 then env.setAssoc p true else pure env
  pure { env with notations := env.notations ++ [⟨tok, p, f, lits⟩] }

/-- `infixl`/`infixr f: $c$ prec p`. The operator is infixy: it may also follow a variable in a
notation (`,` in `infixr pr: $,$ prec 55` and `notation sab ... = ($S\$:100) x ($,$:55) A`), at the
same precedence; it is never a notation head and is declared once. -/
def Env.addInfix (env : Env) (right : Bool) (f tok : String) (p : Prec) : Except String Env := do
  let some t := env.term? f | throw s!"unknown term {f}"
  if t.args.length != 2 then throw s!"{f} is not binary"
  let .num n := p | throw "an infix operator below max"
  if env.isHead tok then throw s!"{tok} is already a notation or an operator"
  let env ← env.setPrec tok p
  let env ← env.setAssoc p right
  pure { env with infixes := env.infixes ++ [⟨tok, n, f, right⟩] }

/-- A notation's items as written: a constant with its precedence, or an argument's name. -/
inductive NLit where
  | const (tok : String) (prec : Prec)
  | var (name : String)
  deriving Repr

/-- The precedence of each argument item (mm0.md's `P`): one above the constant after it, `max`
before another argument, the notation's own precedence at the end. -/
def notationLits (names : List String) (p : Prec) : List NLit → Except String (List Lit)
  | [] => .ok []
  | .const c _ :: rest => do pure (.const c :: (← notationLits names p rest))
  | .var v :: rest => do
      let some i := names.findIdx? (· == v) | throw s!"{v} is not an argument"
      let q ← match rest with
        | [] => pure p
        | .var _ :: _ => pure .max
        | .const _ q :: _ =>
            match q with
            | .num m => pure (Prec.num (m + 1))
            | .max => throw "a constant after a variable below max"
      pure (.var i q :: (← notationLits names p rest))

/-- `notation f (binders): ty = (c: p) items`: the head `c` at `p`; every argument once. -/
def Env.addNotation (env : Env) (f : String) (names : List String) (head : String) (p : Prec)
    (items : List NLit) : Except String Env := do
  let some t := env.term? f | throw s!"unknown term {f}"
  if names.length != t.args.length then throw s!"{f}: {names.length} binders for {t.args.length}"
  env.newHead head
  let mut env ← env.setPrec head p
  let lits ← notationLits names p items
  for i in List.range names.length do
    if (lits.filter fun l => match l with
        | .var j _ => j == i
        | .const _ => false).length != 1 then
      throw s!"{f}: argument {i} must appear exactly once"
  -- a constant after a variable is infixy: never a notation head (an infix operator may be one)
  let mut prev : Option NLit := none
  for item in items do
    match item, prev with
    | .const c q, some (.var _) =>
        if (env.notation? c).isSome || c == head then throw s!"{c} follows a variable and is a notation head"
        env ← env.setPrec c q
        env := { env with infixy := if env.infixy.contains c then env.infixy else env.infixy ++ [c] }
    | .const c q, _ => env ← env.setPrec c q
    | .var _, _ => pure ()
    prev := some item
  env ← match items.getLast? with
    | some (.var _) => env.setAssoc p true
    | _ => pure env
  pure { env with notations := env.notations ++ [⟨head, p, f, lits⟩] }

/-! ## Coercions -/

/-- The coercion terms from `a` to `b`, outermost last, by a search bounded by `fuel`. -/
def coePath (cs : List Coercion) : Nat → String → String → Option (List String)
  | 0, a, b => if a == b then some [] else none
  | fuel + 1, a, b =>
      if a == b then some []
      else cs.findSome? fun c => if c.src == a then (coePath cs fuel c.tgt b).map (c.term :: ·) else none

/-- Sorts joined by coercions in either direction (an undirected search bounded by `fuel`). -/
def connected (cs : List Coercion) : Nat → List String → String → String → Bool
  | 0, _, a, b => a == b
  | fuel + 1, seen, a, b =>
      a == b || cs.any fun c =>
        (c.src == a && !seen.contains c.tgt && connected cs fuel (a :: seen) c.tgt b) ||
        (c.tgt == a && !seen.contains c.src && connected cs fuel (a :: seen) c.src b)

/-- The provable sorts a sort reaches by coercions (itself included). -/
def Env.provableReach (env : Env) (s : String) : List String :=
  (env.sorts.filter fun (t, p) => p && (coePath env.coercions env.coercions.length s t).isSome).map (·.1)

def Env.addCoercion (env : Env) (f a b : String) : Except String Env := do
  let some t := env.term? f | throw s!"unknown term {f}"
  if t.args.map (·.1) != [a] || t.args.any (·.2) || t.ret != b then
    throw s!"{f} is not a coercion from {a} to {b}"
  if connected env.coercions (env.coercions.length + 1) [] a b then
    throw s!"coercion {a} > {b} closes a cycle"
  let env := { env with coercions := env.coercions ++ [⟨f, a, b⟩] }
  for (s, _) in env.sorts do
    if (env.provableReach s).length > 1 then throw s!"{s} reaches two provable sorts"
  pure env

def Env.addDelimiters (env : Env) (left right : List String) : Except String Env := do
  let one (s : String) : Except String Nat := match bytesOf s with
    | [b] => .ok b
    | _ => .error s!"delimiter {s} is not one character"
  let ls ← left.mapM one
  let rs ← right.mapM one
  pure { env with left := env.left ++ ls, right := env.right ++ rs }

/-! ## The grammar of a statement's math strings -/

def termLabel (f : String) : String := "app." ++ f
def notaLabel (c : String) : String := "nota." ++ c
def infixLabel (c : String) : String := "infix." ++ c
def liftLabel (a b : Prec) : String := "lift." ++ a.name ++ "." ++ b.name

def parenProd : Prod := { label := "paren", lhs := lvl .max, rhs := [.lit "(", .nt (lvl (.num 0)), .lit ")"] }
def varProd : Prod := { label := "var", lhs := lvl .max, rhs := [.tok "var"] }

/-- `f e₁ … eₙ` at 1024 with its arguments at `max`; with no argument, `f` at `max`. -/
def termProd (t : TermSig) : Prod :=
  if t.args.isEmpty then { label := termLabel t.name, lhs := lvl .max, rhs := [.lit t.name] }
  else { label := termLabel t.name, lhs := lvl appPrec, rhs := .lit t.name :: t.args.map fun _ => .nt (lvl .max) }

def litSym : Lit → Sym
  | .const c => .lit c
  | .var _ q => .nt (lvl q)

def notationProd (n : Notation) : Prod :=
  { label := notaLabel n.head, lhs := lvl n.prec, rhs := .lit n.head :: n.lits.map litSym }

def infixProd (i : Infix) : Prod :=
  { label := infixLabel i.tok, lhs := lvl (.num i.prec),
    rhs := if i.right then [.nt (lvl (.num (i.prec + 1))), .lit i.tok, .nt (lvl (.num i.prec))]
           else [.nt (lvl (.num i.prec)), .lit i.tok, .nt (lvl (.num (i.prec + 1)))] }

def liftProd (a b : Prec) : Prod := { label := liftLabel a b, lhs := lvl a, rhs := [.nt (lvl b)] }

/-- The precedences the productions use. -/
def Env.levels (env : Env) : List Prec :=
  let ps : List Prec := [.num 0, appPrec, .max] ++
    env.notations.flatMap (fun n => n.prec :: n.lits.filterMap fun l => match l with
      | .var _ q => some q
      | .const _ => none) ++
    env.infixes.flatMap fun i => [.num i.prec, .num (i.prec + 1)]
  ps.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []

/-- The label of a lift between two of the levels. -/
def Env.isLift (env : Env) (label : String) : Bool :=
  env.levels.any fun a => env.levels.any fun b => a.lt b && liftLabel a b == label

/-- The grammar of the math strings of a statement whose variables are `scope`: a variable shadows
a term of the same name; a declared constant is never a variable or a term. -/
def Env.grammar (env : Env) (scope : List String) : Grammar :=
  let ls := env.levels
  { prods := [parenProd, varProd] ++
      (env.terms.filter fun t => !scope.contains t.name && !env.isConst t.name).map termProd ++
      env.notations.map notationProd ++ env.infixes.map infixProd ++
      ls.flatMap (fun a => (ls.filter fun b => a.lt b).map (liftProd a)),
    tokenSorts := ["var"],
    inSort := fun c x => c == "var" && scope.contains x && !env.isConst x }

theorem lvl_ne_var (p : Prec) : lvl p ≠ "var" := by
  intro h
  have h1 := congrArg String.toList h
  rw [lvl, String.toList_append] at h1
  have h2 : "E.".toList = ['E', '.'] := by decide +kernel
  have h3 : "var".toList = ['v', 'a', 'r'] := by decide +kernel
  rw [h2, h3] at h1
  simp at h1

/-- Every phrase sort on a production's right side is a level. -/
def LevelsOnly (p : Prod) : Prop := ∀ n, Sym.nt n ∈ p.rhs → ∃ q, n = lvl q

theorem levelsOnly_paren : LevelsOnly parenProd := by
  intro n h; simp [parenProd] at h; exact ⟨_, h⟩

theorem levelsOnly_var : LevelsOnly varProd := by
  intro n h; simp [varProd] at h

theorem levelsOnly_term (t : TermSig) : LevelsOnly (termProd t) := by
  intro n h
  unfold termProd at h
  split at h
  · simp at h
  · simp at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨_, rfl⟩

theorem levelsOnly_notation (m : Notation) : LevelsOnly (notationProd m) := by
  intro n h
  simp only [notationProd, List.mem_cons, List.mem_map] at h
  rcases h with h | ⟨l, _, hl⟩
  · cases h
  · cases l with
    | const c => cases hl
    | var i q => simp [litSym] at hl; exact ⟨q, hl.symm⟩

theorem levelsOnly_infix (i : Infix) : LevelsOnly (infixProd i) := by
  intro n h
  unfold infixProd at h
  split at h <;> simp at h <;> rcases h with h | h <;> exact ⟨_, h⟩

theorem levelsOnly_lift (a b : Prec) : LevelsOnly (liftProd a b) := by
  intro n h; simp [liftProd] at h; exact ⟨_, h⟩

/-- `TreeCheck.check_iff` applies to every grammar built here. -/
theorem grammar_wellFormed (env : Env) (scope : List String) :
    TreeCheck.WellFormed (env.grammar scope) := by
  intro p hp n hn
  have hl : LevelsOnly p := by
    simp only [Env.grammar, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
      List.mem_filter, List.not_mem_nil, or_false] at hp
    rcases hp with ((((rfl | rfl) | ⟨t, _, rfl⟩) | ⟨m, _, rfl⟩) | ⟨i, _, rfl⟩) | ⟨a, _, b, _, rfl⟩
    · exact levelsOnly_paren
    · exact levelsOnly_var
    · exact levelsOnly_term t
    · exact levelsOnly_notation m
    · exact levelsOnly_infix i
    · exact levelsOnly_lift a b
  obtain ⟨q, rfl⟩ := hl n hn
  show (["var"] : List String).contains (lvl q) = false
  simp only [List.contains_cons, List.contains_nil, Bool.or_false]
  exact beq_false_of_ne (lvl_ne_var q)

/-! ## The parser (not trusted: its trees are checked) -/

def lift (q : Prec) (t : Tree) (lv : Prec) : Option Tree :=
  if lv == q then some t else if q.le lv then some (.node (liftLabel q lv) [t]) else none

section Parse
variable (env : Env) (scope : List String) (toks : Array String)

mutual
/-- An expression at precedence `q` from token `i`: its tree, its level, the next token. -/
partial def pExpr (q : Prec) (i : Nat) : Option (Tree × Prec × Nat) := do
  let (t, lv, j) ← pPrefix q i
  pLhs q t lv j

partial def pPrefix (q : Prec) (i : Nat) : Option (Tree × Prec × Nat) := do
  let tok ← toks[i]?
  if tok == "(" then
    let (t, lv, j) ← pExpr (.num 0) (i + 1)
    let t ← lift (.num 0) t lv
    if toks[j]? == some ")" then some (.node "paren" [t], .max, j + 1) else none
  else match env.notation? tok with
  | some n =>
      if !q.le n.prec then none
      else do
        let (kids, j) ← pLits n.lits (i + 1)
        some (.node (notaLabel n.head) kids, n.prec, j)
  | none =>
      if env.isConst tok then none
      else if scope.contains tok then some (.node "var" [.leaf "var" tok], .max, i + 1)
      else match env.term? tok with
        | none => none
        | some t =>
            if t.args.isEmpty then some (.node (termLabel t.name) [], .max, i + 1)
            else if !q.le appPrec then none
            else do
              let (kids, j) ← pArgs t.args.length (i + 1)
              some (.node (termLabel t.name) kids, appPrec, j)

partial def pLits : List Lit → Nat → Option (List Tree × Nat)
  | [], i => some ([], i)
  | .const c :: rest, i => if toks[i]? == some c then pLits rest (i + 1) else none
  | .var _ q :: rest, i => do
      let (t, lv, j) ← pExpr q i
      let t ← lift q t lv
      let (ts, k) ← pLits rest j
      some (t :: ts, k)

partial def pArgs : Nat → Nat → Option (List Tree × Nat)
  | 0, i => some ([], i)
  | n + 1, i => do
      let (t, lv, j) ← pExpr .max i
      let t ← lift .max t lv
      let (ts, k) ← pArgs n j
      some (t :: ts, k)

/-- Extend `lhs` (at level `lv`) with operators of precedence at least `q`. -/
partial def pLhs (q : Prec) (lhs : Tree) (lv : Prec) (i : Nat) : Option (Tree × Prec × Nat) :=
  match toks[i]? >>= env.infix? with
  | none => some (lhs, lv, i)
  | some op =>
      let p := Prec.num op.prec
      if !q.le p then some (lhs, lv, i)
      else do
        let l ← lift (if op.right then p.succ else p) lhs lv
        let rslot := if op.right then p else p.succ
        let (r, rv, j) ← pPrefix rslot (i + 1)
        let (r, rv, k) ← pClimb op.right p r rv j
        let r ← lift rslot r rv
        pLhs q (.node (infixLabel op.tok) [l, r]) p k

/-- Extend a right operand with the operators that bind tighter than the one before it. -/
partial def pClimb (right : Bool) (p : Prec) (r : Tree) (rv : Prec) (i : Nat) :
    Option (Tree × Prec × Nat) :=
  match toks[i]? >>= env.infix? with
  | none => some (r, rv, i)
  | some op2 =>
      let p2 := Prec.num op2.prec
      if (if right then p.le p2 else p.lt p2) then do
        let (r, rv, j) ← pLhs p2 r rv i
        if j == i then some (r, rv, i) else pClimb right p r rv j
      else some (r, rv, i)
end

end Parse

/-- The tree of a math string's tokens at precedence 0, if the parser finds one. -/
def parse (env : Env) (scope : List String) (toks : List String) : Option Tree := do
  let (t, lv, j) ← pExpr env scope toks.toArray (.num 0) 0
  if j != toks.length then none
  else lift (.num 0) t lv

/-! ## Elaboration -/

/-- An elaborated expression: a variable or a term applied to arguments. -/
inductive EExpr where
  | var (name : String)
  | app (f : String) (args : List EExpr)
  deriving Repr, Inhabited

mutual
/-- The expression as text: a variable by its name, an application in parentheses. -/
def EExpr.text : EExpr → String
  | .var x => x
  | .app f args => "(" ++ f ++ EExpr.textArgs args ++ ")"

def EExpr.textArgs : List EExpr → String
  | [] => ""
  | e :: es => " " ++ EExpr.text e ++ EExpr.textArgs es
end

/-- A variable in scope: its name, sort, and whether it is a bound variable. -/
structure Var where
  name : String
  sort : String
  bound : Bool
  deriving Repr

def applyPath (e : EExpr) (path : List String) : EExpr := path.foldl (fun acc f => .app f [acc]) e

def Env.coerce (env : Env) (e : EExpr) (s target : String) : Except String EExpr :=
  match coePath env.coercions env.coercions.length s target with
  | some path => .ok (applyPath e path)
  | none => .error s!"an expression of sort {s} where {target} is wanted"

/-- A formula: coerced to the provable sort its sort reaches. -/
def Env.toProvable (env : Env) (e : EExpr) (s : String) : Except String EExpr :=
  match env.provableReach s with
  | [t] => env.coerce e s t
  | _ => .error s!"an expression of sort {s}, which reaches no provable sort"

/-- The arguments of `t` from its elaborated children with their argument indices, each at its
binder's sort; a bound binder takes a bound variable of its sort as it is. -/
def Env.args (env : Env) (scope : List Var) (t : TermSig) (xs : List ((EExpr × String) × Nat)) :
    Except String (List EExpr) := do
  if xs.length != t.args.length then throw s!"{t.name}: {xs.length} arguments for {t.args.length}"
  xs.mapM fun ((e, s'), i) => do
    let (s, bound) := t.args.getD i ("", false)
    if bound then
      match e with
      | .var x =>
          if scope.any (fun v => v.name == x && v.bound) && s' == s then pure e
          else throw s!"{t.name}: {x} is not a bound variable of sort {s}"
      | _ => throw s!"{t.name}: an expression where a bound variable is wanted"
    else env.coerce e s' s

/-- A node from its elaborated children. -/
def Env.elabNode (env : Env) (scope : List Var) (label : String) (es : List (EExpr × String)) :
    Except String (EExpr × String) :=
  if label == "paren" || env.isLift label then
    match es with
    | [e] => .ok e
    | _ => .error s!"{label}: one child"
  else
    match env.terms.find? (termLabel ·.name == label) with
    | some t => do pure (.app t.name (← env.args scope t (es.zip (List.range es.length))), t.ret)
    | none =>
      match env.notations.find? (notaLabel ·.head == label) with
      | some n => do
          let some t := env.term? n.term | throw s!"unknown term {n.term}"
          let idx := n.lits.filterMap fun l => match l with
            | .var i _ => some i
            | .const _ => none
          let placed := es.zip idx
          let ordered := (List.range t.args.length).filterMap fun i => placed.find? (·.2 == i)
          pure (.app t.name (← env.args scope t ordered), t.ret)
      | none =>
        match env.infixes.find? (infixLabel ·.tok == label) with
        | some op => do
            let some t := env.term? op.term | throw s!"unknown term {op.term}"
            pure (.app t.name (← env.args scope t (es.zip [0, 1])), t.ret)
        | none => .error s!"no production {label}"

mutual
/-- A checked tree's expression and sort. -/
def elabTree (env : Env) (scope : List Var) : Tree → Except String (EExpr × String)
  | .leaf _ _ => .error "a token where an expression is wanted"
  | .node label kids =>
      if label == "var" then
        match kids with
        | [.leaf "var" x] => match scope.find? (·.name == x) with
            | some v => .ok (.var x, v.sort)
            | none => .error s!"unknown variable {x}"
        | _ => .error "var: one token"
      else do
        let es ← elabTrees env scope kids
        env.elabNode scope label es

def elabTrees (env : Env) (scope : List Var) : List Tree → Except String (List (EExpr × String))
  | [] => .ok []
  | t :: ts => do
      let e ← elabTree env scope t
      let es ← elabTrees env scope ts
      pure (e :: es)
end

/-- A math string read in a scope: tokens, the parser's tree, the trusted check, elaboration. -/
def Env.read (env : Env) (scope : List Var) (math : String) : Except String (EExpr × String) := do
  let toks := mathTokens env.left env.right (inside math)
  let names := scope.map (·.name)
  let some t := parse env names toks | throw s!"no reading of {math}"
  if !TreeCheck.check (env.grammar names) (lvl (.num 0)) toks t then
    throw s!"the reading of {math} does not check"
  elabTree env scope t

/-! ## Controls -/

/-- mm0.md's lexer example: `(` left, `)` right, `*` both. -/
theorem lexer_control :
    mathTokens [40, 42] [41, 42] "a*b(**{}) c" = ["a", "*", "b(", "*", "*", "{}", ")", "c"] := by
  decide +kernel

private def demo0 : Env :=
  { sorts := [("wff", true), ("nat", false)],
    terms := [⟨"im", [("wff", false), ("wff", false)], "wff"⟩, ⟨"not", [("wff", false)], "wff"⟩,
              ⟨"al", [("nat", true), ("wff", false)], "wff"⟩, ⟨"z", [], "nat"⟩,
              ⟨"eq", [("nat", false), ("nat", false)], "wff"⟩] }

/-- `->` right-associative at 25, `~` prefix at 40, `A.` prefix at 41 (a bound variable, then a
formula at 41), `=` left-associative at 50. -/
private def demo : Env :=
  let env := demo0
  let env := (env.addInfix true "im" "->" (.num 25)).toOption.getD env
  let env := (env.addPrefix "not" "~" (.num 40)).toOption.getD env
  let env := (env.addPrefix "al" "A." (.num 41)).toOption.getD env
  (env.addInfix false "eq" "=" (.num 50)).toOption.getD env

private def scope : List Var := [⟨"a", "wff", false⟩, ⟨"b", "wff", false⟩, ⟨"x", "nat", true⟩]

private def names : List String := ["a", "b", "x"]

/-- `~ a -> b` as the grammar derives it: `->` (right-associative at 25) takes `~ a` (level 40,
lifted to its left slot 26) and `b` (lifted from `max` to its right slot 25). -/
private def tildeFirst : Tree :=
  .node "lift.0.25" [.node "infix.->" [
    .node "lift.26.40" [.node "nota.~" [.node "lift.40.max" [.node "var" [.leaf "var" "a"]]]],
    .node "lift.25.max" [.node "var" [.leaf "var" "b"]]]]

/-- The other grouping, `~ (a -> b)` without the parentheses: `->` at 25 is below the slot of `~`
(40), and no production lowers a level. -/
private def tildeLast : Tree :=
  .node "lift.0.40" [.node "nota.~" [.node "lift.40.25" [.node "infix.->" [
    .node "lift.26.max" [.node "var" [.leaf "var" "a"]],
    .node "lift.25.max" [.node "var" [.leaf "var" "b"]]]]]]

/-- Positive control: the trusted check accepts `tildeFirst`, which elaborates to `im (not a) b`. -/
theorem check_control :
    TreeCheck.check (demo.grammar names) (lvl (.num 0)) ["~", "a", "->", "b"] tildeFirst = true ∧
    ((elabTree demo scope tildeFirst).toOption.map fun (e, s) => (e.text, s)) =
      some ("(im (not a) b)", "wff") := by
  decide +kernel

/-- Negative controls: the other grouping does not check; a tree missing its lift does not check;
a tree of other tokens does not check. -/
theorem check_refusals :
    TreeCheck.check (demo.grammar names) (lvl (.num 0)) ["~", "a", "->", "b"] tildeLast = false ∧
    TreeCheck.check (demo.grammar names) (lvl (.num 0)) ["~", "a", "->", "b"]
      (.node "infix.->" [.node "nota.~" [.node "lift.40.max" [.node "var" [.leaf "var" "a"]]],
        .node "lift.25.max" [.node "var" [.leaf "var" "b"]]]) = false ∧
    TreeCheck.check (demo.grammar names) (lvl (.num 0)) ["~", "b", "->", "b"] tildeFirst = false := by
  decide +kernel

/-- Declarations MM0 refuses: two precedences for one constant, a left-associative operator on a
right-associative level, a head declared twice. -/
theorem declaration_refusals :
    (demo.addInfix false "eq" "->" (.num 30)).toOption.isNone = true ∧
    (demo.addInfix false "eq" "=>" (.num 25)).toOption.isNone = true ∧
    (demo.addPrefix "not" "~" (.num 40)).toOption.isNone = true := by
  decide +kernel

private def coeEnv : Env :=
  { sorts := [("s", false), ("t", false), ("u", false), ("p", true), ("q", true)],
    terms := [⟨"st", [("s", false)], "t"⟩, ⟨"tu", [("t", false)], "u"⟩, ⟨"us", [("u", false)], "s"⟩,
              ⟨"sp", [("s", false)], "p"⟩, ⟨"uq", [("u", false)], "q"⟩] }

/-- Coercions: a chain is accepted; the edge closing a cycle is refused; a sort reaching two
provable sorts is refused; a formula of sort `s` is coerced along the unique path. -/
theorem coercion_controls :
    ((coeEnv.addCoercion "st" "s" "t") >>= (·.addCoercion "tu" "t" "u")).toOption.isSome = true ∧
    ((coeEnv.addCoercion "st" "s" "t") >>= (·.addCoercion "tu" "t" "u") >>=
      (·.addCoercion "us" "u" "s")).toOption.isNone = true ∧
    ((coeEnv.addCoercion "st" "s" "t") >>= (·.addCoercion "tu" "t" "u") >>=
      (·.addCoercion "sp" "s" "p") >>= (·.addCoercion "uq" "u" "q")).toOption.isNone = true ∧
    (((coeEnv.addCoercion "st" "s" "t") >>= (·.addCoercion "tu" "t" "u") >>=
      (·.addCoercion "uq" "u" "q")) >>= (·.toProvable (.var "v") "s")).toOption.map EExpr.text =
      some "(uq (tu (st v)))" := by
  decide +kernel

/-! Tests of the whole reading, the untrusted parser included (evaluated, not proved). -/

#guard (demo.read scope "$ ~ a -> b -> a $").toOption.map (·.1.text) == some "(im (not a) (im b a))"
#guard (demo.read scope "$ A. x x = z $").toOption.map (·.1.text) == some "(al x (eq x (z)))"
#guard (demo.read scope "$ ( ~ a ) -> b $").toOption.map (·.1.text) == some "(im (not a) b)"
#guard (demo.read scope "$ ~ ( a -> b ) $").toOption.map (·.1.text) == some "(not (im a b))"
#guard (demo.read scope "$ a -> $").toOption.isNone
#guard (demo.read scope "$ A. z a $").toOption.isNone
#guard (demo.read scope "$ ~ c $").toOption.isNone
#guard (demo.read scope "$ ( a $").toOption.isNone

end Mettapedia.GSLT.Readers.MM0.Math
