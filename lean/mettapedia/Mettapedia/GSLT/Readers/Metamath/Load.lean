import Mettapedia.GSLT.Readers.TreeCheck

/-!
# Loading a Metamath database into kernel version 2

The generated C reader turns a `.mm` file into checked statement items. This module is Metamath's
loading semantics, as an executable definition: it walks the items in source order, keeps the
scopes (`${ $}`), the active variables, hypotheses and distinct-variable pairs, computes each
assertion's frame (the mandatory floating hypotheses of the variables that occur, every active
essential hypothesis, the distinct pairs among mandatory variables), decodes normal and compressed
proofs, and prints kernel-version-2 messages:

* an axiom becomes `(admit-rule mm:L FORMALS PREMISES CONCLUSION)`; a syntax axiom
  `wi $a wff ( ph -> ps ) $.` is the constructor rule
  `(admit-rule mm:wi ($v1 $v2) (prem (mm.wff $v1) (prem (mm.wff $v2) no-prem)) (mm.wff (mm:wi $v1 $v2)))`;
* a theorem becomes `(claim mm:L ROOT FORMALS DUMMIES HYPS LOCALS DVL CONCLUSION () PROOF)`, whose
  nodes are labels and children only: a step saved with `Z` and used again is one node cited twice.
  PROOF is a chain of cells `(node N RULE CHILDREN REST)` ending in `no-node`, children first;
  DUMMIES are the non-mandatory variables whose floating hypotheses the proof cites.

Math strings are parsed with the database's own syntax axioms (a `|-` formula parses as a `wff`, the
grammatical convention of set.mm) by a memoizing top-down parser, which is untrusted: every tree is
accepted only by `TreeCheck.check` against the grammar of those axioms.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.Metamath.Load

open Mettapedia.GSLT.Readers.SLR (Sym Prod)
open Mettapedia.GSLT.Readers.TreeCheck (Tree Grammar)

/-! ## The reader's items -/

inductive SX where
  | atom (s : String)
  | str (s : String)
  | list (xs : List SX)
  deriving Inhabited, Repr

/-- Read one S-expression line (iteratively, with an explicit stack). In a string, a backslash
quotes the next character, and backslash-`n` is a newline (a quoted token's newline, as the
engines print it). -/
def parseSX (line : String) : Option SX := Id.run do
  let cs := line.toList.toArray
  let mut stack : List (List SX) := [[]]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '(' then
      stack := [] :: stack
      i := i + 1
    else if c == ')' then
      match stack with
      | top :: below :: rest => stack := ((SX.list top.reverse) :: below) :: rest
      | _ => return none
      i := i + 1
    else if c == '"' then
      let mut j := i + 1
      let mut acc : List Char := []
      while j < cs.size && cs[j]! != '"' do
        if cs[j]! == '\\' && j + 1 < cs.size then
          acc := (if cs[j+1]! == 'n' then '\n' else cs[j+1]!) :: acc
          j := j + 2
        else
          acc := cs[j]! :: acc
          j := j + 1
      match stack with
      | top :: rest => stack := ((SX.str (String.ofList acc.reverse)) :: top) :: rest
      | [] => return none
      i := j + 1
    else if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
      i := i + 1
    else
      let mut j := i
      let mut acc : List Char := []
      while j < cs.size && cs[j]! != ' ' && cs[j]! != '(' && cs[j]! != ')' && cs[j]! != '\n' do
        acc := cs[j]! :: acc
        j := j + 1
      match stack with
      | top :: rest => stack := ((SX.atom (String.ofList acc.reverse)) :: top) :: rest
      | [] => return none
      i := j
  match stack with
  | [[x]] => some x
  | _ => none

/-- `(rdr:item N TREE)` lines, as a map from item number to tree. -/
def readItems (text : String) : Std.HashMap Nat SX := Id.run do
  let mut m : Std.HashMap Nat SX := {}
  for line in text.splitOn "\n" do
    if line.startsWith "(rdr:item " then
      match parseSX line with
      | some (.list [.atom _, .atom n, t]) =>
          match n.toNat? with
          | some k => m := m.insert k t
          | none => pure ()
      | _ => pure ()
  return m

/-! ## Statements in source order -/

inductive Ev where
  | c (syms : List String)
  | v (syms : List String)
  | d (syms : List String)
  | f (lab tc var : String)
  | e (lab : String) (form : List String)
  | a (lab : String) (form : List String)
  | pn (lab : String) (form : List String) (proof : List String)
  | pc (lab : String) (form : List String) (hdr : List String) (body : String)
  | incl (path : String)
  | open_ | close
  deriving Inhabited, Repr

def leafText : SX → Option String
  | .list [.atom "tok", .atom _, .str s] => some s
  | _ => none

/-- A right-nested list: `(more HEAD REST)` / `(one HEAD)` / `(empty)`, with leaves. -/
partial def listOf (items : Std.HashMap Nat SX) : SX → List String
  | .list [.atom "item", .atom n] => match n.toNat? >>= items.get? with
      | some t => listOf items t
      | none => []
  | .list (.atom _ :: kids) => kids.flatMap fun k => match leafText k with
      | some s => [s]
      | none => listOf items k
  | _ => []

def resolve (items : Std.HashMap Nat SX) : SX → SX
  | .list [.atom "item", .atom n] => (n.toNat? >>= items.get?).getD default
  | t => t

partial def statementEvs (items : Std.HashMap Nat SX) (t : SX) : List Ev :=
  match resolve items t with
  | .list (.atom label :: kids) =>
      match label, kids with
      | "statement_const", [s] => [.c (listOf items s)]
      | "statement_var", [s] => [.v (listOf items s)]
      | "statement_disjoint", [s] => [.d (listOf items s)]
      | "statement_float", [l, tc, v] => [.f ((leafText l).getD "") ((leafText tc).getD "") ((leafText v).getD "")]
      | "statement_essential", [l, f] => [.e ((leafText l).getD "") (listOf items f)]
      | "statement_axiom", [l, f] => [.a ((leafText l).getD "") (listOf items f)]
      | "statement_theorem_normal", [l, f, p] => [.pn ((leafText l).getD "") (listOf items f) (listOf items p)]
      | "statement_theorem_compressed", [l, f, h, b] =>
          [.pc ((leafText l).getD "") (listOf items f) (listOf items h) (String.join (listOf items b))]
      | "statement_include", [p] => [.incl ((leafText p).getD "")]
      | "statement_block", [db] => .open_ :: databaseEvs items db ++ [.close]
      | "outer_statement_inner", [s] => statementEvs items s
      | _, _ => []
  | _ => []
where
  databaseEvs (items : Std.HashMap Nat SX) (db : SX) : List Ev := Id.run do
    let mut out : Array Ev := #[]
    let mut cur := resolve items db
    let mut fuel := 10000000
    while fuel > 0 do
      fuel := fuel - 1
      match cur with
      | .list [.atom "database_more", s, rest] =>
          out := out ++ (statementEvs items s).toArray
          cur := resolve items rest
      | .list [.atom "outer_database_more", s, rest] =>
          out := out ++ (statementEvs items s).toArray
          cur := resolve items rest
      | _ => fuel := 0
    return out.toList

/-- The events of the whole database: the root is the last item. -/
def events (items : Std.HashMap Nat SX) (root : Nat) : List Ev :=
  statementEvs.databaseEvs items (.list [.atom "item", .atom (toString root)])

/-! ## Math strings: the grammar of the syntax axioms, a parser, and the trusted check -/

/-- A syntax row: label, typecode, and symbols (`.inl` a constant, `.inr` a typecode slot). -/
structure SynRow where
  label : String
  tc : String
  rhs : List (String ⊕ String)
  deriving Inhabited, Repr

/-- All parses of `toks[i:]` at typecode `tc`, memoized by `(tc, i)`; fuel bounds the depth. -/
partial def parseAt (rows : List SynRow) (varTc : String → Option String) (toks : Array String)
    (memo : IO.Ref (Std.HashMap (String × Nat) (List (Tree × Nat)))) (tc : String) (i : Nat) :
    IO (List (Tree × Nat)) := do
  match (← memo.get).get? (tc, i) with
  | some r => return r
  | none =>
      memo.modify (·.insert (tc, i) [])   -- the seed of left recursion: grown below until stable
      let mut out : List (Tree × Nat) := []
      let mut grow := true
      while grow do
        out := []
        if h : i < toks.size then
          let t := toks[i]
          if varTc t == some tc then out := (Tree.node ("var:" ++ t) [], i + 1) :: out
        for r in rows do
          if r.tc == tc then
            let mut partials : List (List Tree × Nat) := [([], i)]
            for s in r.rhs do
              let mut next : List (List Tree × Nat) := []
              for (kids, j) in partials do
                match s with
                | .inl c =>
                    if h : j < toks.size then
                      if toks[j] == c then
                        next := (kids, j + 1) :: next
                | .inr t =>
                    for (sub, k) in ← parseAt rows varTc toks memo t j do
                      next := (kids ++ [sub], k) :: next
              partials := next
            for (kids, j) in partials do
              out := (Tree.node r.label kids, j) :: out
        let before := (((← memo.get).get? (tc, i)).getD []).map (·.2)
        if out.all (fun (_, e) => before.contains e) then grow := false
        else memo.modify (·.insert (tc, i) (out ++ (((← memo.get).get? (tc, i)).getD [])))
      return (((← memo.get).get? (tc, i)).getD [])

/-- The token-level grammar of the syntax rows and the variables, for `TreeCheck.check`. -/
def mathGrammar (rows : List SynRow) (vars : List (String × String)) : Grammar :=
  { prods := rows.map (fun r => { label := r.label, lhs := r.tc,
                                  rhs := r.rhs.map fun s => match s with
                                    | .inl c => Sym.lit c
                                    | .inr t => Sym.nt t })
             ++ vars.map (fun (v, tc) => { label := "var:" ++ v, lhs := tc, rhs := [Sym.lit v] }),
    tokenSorts := [], inSort := fun _ _ => false }

/-- Structural equality of trees. -/
partial def treeEq : Tree → Tree → Bool
  | .leaf s x, .leaf s' x' => s == s' && x == x'
  | .node l ks, .node l' ks' =>
      l == l' && ks.length == ks'.length && (ks.zip ks').all fun (a, b) => treeEq a b
  | _, _ => false

/-- Parse a formula at a typecode; the unique parse that the trusted check accepts. A formula
with two different trees is outside the grammatical form (the kernel compares trees, Metamath
compares strings), and is refused here rather than read one way. -/
def parseFormula (rows : List SynRow) (vars : List (String × String)) (tc : String)
    (toks : List String) : IO (Except String Tree) := do
  let memo ← IO.mkRef {}
  let varTc := fun v => vars.lookup v
  let all ← parseAt rows varTc toks.toArray memo tc 0
  let full := (all.filter (·.2 == toks.length)).map (·.1)
  let distinct := full.foldl (fun acc t => if acc.any (treeEq t) then acc else acc ++ [t]) []
  match distinct with
  | [] => return .error s!"no parse at {tc}: {toks}"
  | [t] =>
      if TreeCheck.check (mathGrammar rows vars) tc toks t then return .ok t
      else return .error s!"tree check refused at {tc}: {toks}"
  | _ => return .error s!"ambiguous: {distinct.length} trees at {tc}: {toks}"

/-! ## Printing kernel data -/

def tc' (tc : String) : String := "mm." ++ tc

partial def treeMetta (varName : String → String) : Tree → String
  | .node l [] => if l.startsWith "var:" then varName (l.drop 4).toString else s!"(mm:{l})"
  | .node l kids => s!"(mm:{l} " ++ " ".intercalate (kids.map (treeMetta varName)) ++ ")"
  | .leaf _ x => x

partial def treeVars : Tree → List String
  | .node l [] => if l.startsWith "var:" then [(l.drop 4).toString] else []
  | .node _ kids => kids.flatMap treeVars
  | .leaf _ _ => []

def consList (xs : List String) : String :=
  xs.foldr (fun x acc => s!"(prem {x} {acc})") "no-prem"

/-- Some of a proof's nodes (each `N RULE CHILDREN`) as the cell chain
`(node N RULE CHILDREN (node ... TAIL))`, built in one pass. -/
def proofCells (nodes : List String) (tail : String) : String :=
  String.join (nodes.map fun nd => "(node " ++ nd ++ " ") ++ tail ++
    String.ofList (List.replicate nodes.length ')')

/-- Nodes per message: the kernel keeps every step of a command until the command ends, so a long
proof goes as a claim carrying its first nodes and `(chunk ID K CHAIN)` messages carrying the rest. -/
def chunkNodes : Nat := 50

/-- A proof's chains: the first ends in `(more 1)` when a chunk follows, chunk `k` in `(more k+1)`,
and the last in `no-node`. -/
def proofChunks (nodes : List String) : List String :=
  let parts := (nodes.toChunks chunkNodes)
  let parts := if parts.isEmpty then [[]] else parts
  parts.zipIdx.map fun (p, k) =>
    proofCells p (if k + 1 < parts.length then s!"(more {k + 1})" else "no-node")

/-! ## The database fold -/

inductive Hyp where
  | flt (lab tc var : String)
  | ess (lab : String) (tc : String) (tree : Tree) (vars : List String)
  deriving Inhabited

structure Assertion where
  arity : Nat
  deriving Inhabited

structure St where
  vars : Array String := #[]
  hyps : Array Hyp := #[]
  dvs : Array (String × String) := #[]
  scopes : List (Nat × Nat × Nat) := []
  rows : Array SynRow := #[]
  syntaxTcs : List String := []
  asserts : Std.HashMap String Assertion := {}
  out : Array String := #[]
  errors : Array String := #[]
  claims : Nat := 0
  admitted : Nat := 0

def activeVarTcs (st : St) : List (String × String) :=
  st.hyps.toList.filterMap fun h => match h with
    | .flt _ tc v => some (v, tc)
    | _ => none

/-- Metamath's provable typecode is `|-`; every other typecode is a syntax typecode, and a `|-`
formula parses as a `wff` (the grammatical convention of set.mm and its relatives). -/
def isSyntaxTc (tc : String) : Bool := tc != "|-"

def parseTc (_st : St) (tc : String) : String := if isSyntaxTc tc then tc else "wff"

/-- The frame of an assertion: mandatory hypotheses in order, and mandatory variables in order. -/
def frame (st : St) (formVars : List String) : List Hyp × List String :=
  let essVars := st.hyps.toList.flatMap fun h => match h with
    | .ess _ _ _ vs => vs
    | _ => []
  let mand := (essVars ++ formVars).eraseDups
  let hs := st.hyps.toList.filter fun h => match h with
    | .flt _ _ v => mand.contains v
    | .ess .. => true
  let order := hs.filterMap fun h => match h with
    | .flt _ _ v => some v
    | _ => none
  (hs, order)

def varName (order : List String) (v : String) : String :=
  match order.findIdx? (· == v) with
  | some i => s!"$v{i + 1}"
  | none => s!"$u{v.length}"

def hypMetta (vn : String → String) : Hyp → String
  | .flt _ tc v => s!"({tc' tc} {vn v})"
  | .ess _ tc t _ => s!"({tc' tc} {treeMetta vn t})"

/-- The active distinct pairs among `vs`, each unordered pair once (oriented by the order of `vs`):
distinctness is symmetric and the kernel looks a pair up in both orientations. -/
def dvAmong (st : St) (vs : List String) : List (String × String) :=
  (st.dvs.toList.filter fun (x, y) =>
    match vs.findIdx? (· == x), vs.findIdx? (· == y) with
    | some i, some j => i < j
    | _, _ => false).eraseDups

/-- Decode a compressed proof body into numbers (1-based) and `Z` marks (0). -/
def decodeCompressed (body : String) : List Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut acc := 0
  for ch in body.toList do
    if ch == 'Z' then out := out.push 0
    else if 'U' ≤ ch && ch ≤ 'Y' then acc := acc * 5 + (ch.toNat - 'U'.toNat + 1)
    else if 'A' ≤ ch && ch ≤ 'T' then
      out := out.push (acc * 20 + (ch.toNat - 'A'.toNat + 1))
      acc := 0
  return out.toList

/-- A proof as kernel nodes, labels and children only. -/
def proofNodes (st : St) (mandLabels : List String) (localLabels : List String)
    (steps : List (Sum String Nat)) (hdr : List String) (compressed : Bool) :
    Except String (List String × String) := do
  let mut stack : Array String := #[]
  let mut saved : Array String := #[]
  let mut nodes : Array String := #[]
  let mut n := 0
  for step in steps do
    let lab : Option String ← match step with
      | .inl l => pure (some l)
      | .inr 0 =>
          if stack.isEmpty then throw "Z on an empty stack"
          saved := saved.push stack.back!
          pure none
      | .inr k =>
          let m := mandLabels.length
          if k ≤ m then pure (some (mandLabels.getD (k - 1) ""))
          else if k ≤ m + hdr.length then pure (some (hdr.getD (k - m - 1) ""))
          else
            match saved[k - m - hdr.length - 1]? with
            | some ref => stack := stack.push ref; pure none
            | none => throw s!"saved step {k} out of range"
    match lab with
    | none => pure ()
    | some l =>
        match mandLabels.findIdx? (· == l) with
        | some i => stack := stack.push s!"(hyp {i})"
        | none =>
            match localLabels.findIdx? (· == l) with
            | some i => stack := stack.push s!"(local {i})"
            | none =>
                match st.asserts.get? l with
                | none => throw s!"unknown label {l}"
                | some a =>
                    if stack.size < a.arity then throw s!"stack underflow at {l}"
                    let kids := (stack.toList.drop (stack.size - a.arity))
                    stack := stack.shrink (stack.size - a.arity)
                    n := n + 1
                    nodes := nodes.push (s!"{n} mm:{l} (" ++ " ".intercalate kids ++ ")")
                    stack := stack.push (toString n)
  let _ := compressed
  match stack.toList with
  | [root] => pure (nodes.toList, root)
  | _ => throw s!"the proof leaves {stack.size} entries"

def step (st : St) (ev : Ev) : IO St := do
  match ev with
  | .open_ => return { st with scopes := (st.vars.size, st.hyps.size, st.dvs.size) :: st.scopes }
  | .close =>
      match st.scopes with
      | (nv, nh, nd) :: rest =>
          return { st with vars := st.vars.shrink nv, hyps := st.hyps.shrink nh,
                           dvs := st.dvs.shrink nd, scopes := rest }
      | [] => return { st with errors := st.errors.push "unbalanced $}" }
  | .c _ => return st
  | .incl p => return { st with errors := st.errors.push s!"include {p} not followed" }
  | .v syms => return { st with vars := st.vars ++ syms.toArray }
  | .d syms =>
      let pairs := syms.flatMap fun x => syms.filterMap fun y => if x != y then some (x, y) else none
      return { st with dvs := st.dvs ++ pairs.toArray }
  | .f lab tc v =>
      let st := if st.syntaxTcs.contains tc then st else { st with syntaxTcs := tc :: st.syntaxTcs }
      return { st with hyps := st.hyps.push (.flt lab tc v),
                       asserts := st.asserts.insert lab ⟨0⟩ }
  | .e lab form =>
      match form with
      | [] => return { st with errors := st.errors.push s!"{lab}: empty" }
      | tc :: body =>
          match ← parseFormula st.rows.toList (activeVarTcs st) (parseTc st tc) body with
          | .error msg => return { st with errors := st.errors.push s!"{lab}: {msg}" }
          | .ok t => return { st with hyps := st.hyps.push (.ess lab tc t (treeVars t).eraseDups) }
  | .a lab form =>
      match form with
      | [] => return { st with errors := st.errors.push s!"{lab}: empty" }
      | tc :: body =>
          let vtc := activeVarTcs st
          let st := if isSyntaxTc tc && !st.syntaxTcs.contains tc then { st with syntaxTcs := tc :: st.syntaxTcs } else st
          if isSyntaxTc tc then
            -- a syntax axiom: its tree is the constructor applied to its variables in order
            let vs := (body.filter fun s => (vtc.lookup s).isSome).eraseDups
            let rhs : List (String ⊕ String) := body.map fun s =>
              match vtc.lookup s with
              | some t => .inr t
              | none => .inl s
            let row : SynRow := { label := lab, tc := tc, rhs := rhs }
            let t : Tree := .node lab (vs.map fun v => .node ("var:" ++ v) [])
            let st := { st with rows := st.rows.push row }
            emitAxiom st lab tc t vs
          else
            match ← parseFormula st.rows.toList vtc (parseTc st tc) body with
            | .error msg => return { st with errors := st.errors.push s!"{lab}: {msg}" }
            | .ok t => emitAxiom st lab tc t (treeVars t).eraseDups
  | .pn lab form proof => emitTheorem st lab form ((proof.map Sum.inl)) [] false
  | .pc lab form hdr body =>
      emitTheorem st lab form ((decodeCompressed body).map Sum.inr) hdr true
where
  emitAxiom (st : St) (lab tc : String) (t : Tree) (vs : List String) : IO St := do
    let (hs, order) := frame st vs
    let vn := varName order
    let prems := hs.map (hypMetta vn) ++
      (dvAmong st order).map fun (x, y) => s!"(dv {vn x} {vn y})"
    let msg := s!"(admit-rule mm:{lab} (" ++ " ".intercalate (order.map vn) ++ ") " ++
      consList prems ++ s!" ({tc' tc} {treeMetta vn t}))"
    return { st with out := st.out.push s!"!(transform &admit () (add-atom &admit {msg}))",
                     asserts := st.asserts.insert lab ⟨hs.length⟩, admitted := st.admitted + 1 }
  emitTheorem (st : St) (lab : String) (form : List String) (steps : List (Sum String Nat))
      (hdr : List String) (compressed : Bool) : IO St := do
    match form with
    | [] => return { st with errors := st.errors.push s!"{lab}: empty" }
    | tc :: body =>
        match ← parseFormula st.rows.toList (activeVarTcs st) (parseTc st tc) body with
        | .error msg => return { st with errors := st.errors.push s!"{lab}: {msg}" }
        | .ok t =>
            let (hs, order) := frame st (treeVars t).eraseDups
            let mandLabels := hs.map fun h => match h with | .flt l _ _ => l | .ess l _ _ _ => l
            -- optional floats: the active floats of non-mandatory variables that the proof cites
            -- (every variable of a proof's terms comes from a float the proof cites, so the others
            -- play no part in the claim)
            let cited : Std.HashSet String := Std.HashSet.ofList (hdr ++ steps.filterMap fun s =>
              match s with
              | .inl l => some l
              | .inr _ => none)
            let optional := st.hyps.toList.filterMap fun h => match h with
              | .flt l tc v => if order.contains v || !cited.contains l then none else some (l, tc, v)
              | _ => none
            let localLabels := optional.map (·.1)
            let dummies := optional.map (·.2.2)
            let allVars := order ++ dummies
            let vn := fun v => match order.findIdx? (· == v) with
              | some i => s!"$v{i + 1}"
              | none => match dummies.findIdx? (· == v) with
                | some j => s!"$d{j + 1}"
                | none => s!"$u{v.length}"
            match proofNodes st mandLabels localLabels steps hdr compressed with
            | .error msg => return { st with errors := st.errors.push s!"{lab}: {msg}" }
            | .ok (nodes, root) =>
                let hyps := hs.map (hypMetta vn) ++
                  (dvAmong st order).map fun (x, y) => s!"(dv {vn x} {vn y})"
                let locals := optional.map fun (_, tc, v) => s!"({tc' tc} {vn v})"
                let dvl := (dvAmong st allVars).filter fun (x, y) => dummies.contains x || dummies.contains y
                let msg := s!"(claim mm:{lab} {root} (" ++ " ".intercalate (order.map vn) ++ ") (" ++
                  " ".intercalate (dummies.map vn) ++ ") " ++ consList hyps ++ " (" ++
                  " ".intercalate locals ++ ") (" ++
                  " ".intercalate (dvl.map fun (x, y) => s!"({vn x} {vn y})") ++ ") " ++
                  s!"({tc' tc} {treeMetta vn t}) () "
                let chains := proofChunks nodes
                let first := s!"!(transform &submit () (add-atom &submit {msg}{chains.headD "no-node"})))"
                let rest := (chains.drop 1).zipIdx.map fun (ch, k) =>
                  s!"!(transform &submit () (add-atom &submit (chunk mm:{lab} {k + 1} {ch})))"
                return { st with out := (st.out.push first) ++ rest.toArray,
                                 asserts := st.asserts.insert lab ⟨hs.length⟩, claims := st.claims + 1 }

/-- Load events; stop after `maxClaims` theorems. -/
def load (evs : List Ev) (maxClaims : Nat) : IO St := do
  let mut st : St := {}
  for ev in evs do
    if st.claims ≥ maxClaims then break
    st ← step st ev
  return st

end Mettapedia.GSLT.Readers.Metamath.Load
