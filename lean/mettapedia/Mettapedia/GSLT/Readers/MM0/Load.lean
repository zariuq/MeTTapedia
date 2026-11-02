import Mettapedia.GSLT.Readers.Metamath.Load

/-!
# Loading an MM0 proof file (`.mmu`) into kernel version 2

The generated `.mmu` reader turns a file into checked statement trees. This module is MM0's
loading semantics as an executable definition. It walks the statements in order, checks each
declaration (sorts and modifiers, binders and dependencies, the typing of every statement
expression, provable sorts for hypotheses and conclusions, a definition's dummies and free
variables), and prints kernel-version-2 messages. With a specification (`loadSpec`) every
statement that is not local must also match the `.mm0` file (`MM0.Expect`).

Encoding (MM0 → kernel version 2):
* a sort `s` is the unary judgment `mm0.s` ("an expression of sort `s`"); `mm0.pf E` is "`E` is
  proved"; `mm0.cv E F` is "`E` and `F` are convertible";
* bound variables: `mm0.bv.s x` ("`x` is a bound variable of sort `s`") for a sort that is not
  `strict`; `mm0.nf x E` ("the bound variable `x` is not among the variables of `E`", MM0's
  `Vars`: a bound variable is its own, a regular variable has its dependencies, a term has its
  arguments'). Its rules come from the presentation: `nf.f` per term (from its arguments),
  `nf-sym` (independence of two bound variables turned around), and for a dummy `nf-fresh` (a
  dummy is fresh: it is not free wherever it does not occur, `absent-from` with the dummy first);
  a statement's dependency facts (`nfPairs`) are its hypotheses. No proof decides a side
  condition on a claim's formals (the kernel would refuse it, F5): two bound binders are told
  apart by their declared fact, not by `differ`;
* dummies: a theorem's dummies are the claim's fresh names, each with the local `mm0.dbv.s d`;
  `mm0.dbv.s` is the only kind of judgment declared as a sort (`admit-sort`), and the kernel
  refuses any rule that concludes it and any claim that states it outside a local; `mm0:dbv.s`
  makes it `mm0.bv.s d`; a sort that is `free` has no dummies;
* a term or definition `c` is the constructor rule `mm0:c` (a bound argument is a bound
  variable), with `mm0:cv-cong.c` (typed: each side's arguments have their binders' facts) and
  `mm0:nf.c`; a definition also gets `mm0:cv-unfold.c`, from its arguments and dummy instances
  (bound variables, not among the arguments' variables, pairwise different) to
  `cv (c args) value[args, dummies]`;
* `mm0:cv-refl.s` (per sort), `mm0:cv-sym`, `mm0:cv-trans`, and `mm0:conv` (from `cv E F` and
  `pf F`, `pf E`: MM0's `(:conv E C P)`, where `C` converts `E` to what `P` proves);
* an axiom is a rule (binder facts, the dependency facts `nfPairs`, then its hypotheses); a
  theorem is a claim whose nodes are labels and children only: a theorem step's children are the
  facts of its arguments, the `mm0.nf` derivations its dependency facts ask for, then its
  subproofs; an argument term is built once per claim; `(:let h P Q)` names P's node.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.MM0.Load

open Mettapedia.GSLT.Readers.Metamath.Load (SX parseSX readItems leafText)

/-! ## The statements -/

inductive Expr where
  | var (name : String)
  | app (head : String) (args : List Expr)
  deriving Inhabited, Repr, BEq, Hashable

/-- A binder: its name (`_` for a blank one), its sort, and `none` for a bound binder or the
dependencies of a regular one. -/
structure Binder where
  name : String
  sort : String
  deps : Option (List String)
  deriving Inhabited, Repr

inductive Conv where
  | var (name : String)
  | app (head : String) (args : List Conv)
  | sym (inner : Conv)
  | unfold (head : String) (args : List Expr) (dummies : List String) (inner : Conv)
  deriving Inhabited, Repr

inductive Proof where
  | hyp (name : String)
  | thm (head : String) (args : List Expr) (subproofs : List Proof)
  | conv (target : Expr) (conversion : Conv) (inner : Proof)
  | let_ (name : String) (shared body : Proof)
  deriving Inhabited, Repr

structure SortMods where
  pure : Bool
  strict : Bool
  provable : Bool
  free : Bool
  deriving Inhabited, Repr

inductive Stmt where
  | sort (name : String) (mods : SortMods)
  | term (name : String) (args : List Binder) (ret : String) (deps : List String)
  | axiom_ (name : String) (args : List Binder) (hyps : List Expr) (concl : Expr)
  | def_ (name : String) (args : List Binder) (ret : String) (deps : List String)
      (dummies : List (String × String)) (value : Expr)
  | theorem (name : String) (args : List Binder) (hyps : List (String × Expr)) (concl : Expr)
      (dummies : List (String × String)) (proof : Proof)
  | io (kind : String)
  deriving Inhabited, Repr

/-! ## Reading statement trees (the reader's `(rdr:item N TREE)` lines) -/

def tok? (t : SX) : Option String := leafText t

partial def listOf {α : Type} (more empty : String) (item : SX → Option α) : SX → Option (List α)
  | .list [.atom l] => if l == empty then some [] else none
  | .list [.atom l, first, rest] =>
      if l == more then do
        let x ← item first
        let xs ← listOf more empty item rest
        pure (x :: xs)
      else none
  | _ => none

/-- `dummies_more` carries name and sort inline: `(dummies_more NAME SORT REST)`. -/
partial def dummiesOf : SX → Option (List (String × String))
  | .list [.atom "dummies_empty"] => some []
  | .list [.atom "dummies_more", n, s, rest] => do
      let n ← tok? n
      let s ← tok? s
      let more ← dummiesOf rest
      pure ((n, s) :: more)
  | _ => none

partial def hypsOf (expr : SX → Option Expr) : SX → Option (List (String × Expr))
  | .list [.atom "hyps_empty"] => some []
  | .list [.atom "hyps_more", n, e, rest] => do
      let n ← tok? n
      let e ← expr e
      let more ← hypsOf expr rest
      pure ((n, e) :: more)
  | _ => none

def idsOf : SX → Option (List String) := listOf "ids_more" "ids_empty" tok?

partial def exprOf : SX → Option Expr
  | .list [.atom "expr_var", n] => (tok? n).map .var
  | .list [.atom "expr_app", h, args] => do
      let h ← tok? h
      let args ← listOf "exprs_more" "exprs_empty" exprOf args
      pure (.app h args)
  | _ => none

def exprsOf : SX → Option (List Expr) := listOf "exprs_more" "exprs_empty" exprOf

def binderOf : SX → Option Binder
  | .list [.atom "binder_bound", n, s] => do pure ⟨← tok? n, ← tok? s, none⟩
  | .list [.atom "binder_regular", n, s, d] => do pure ⟨← tok? n, ← tok? s, some (← idsOf d)⟩
  | .list [.atom "binder_bound_blank", s] => do pure ⟨"_", ← tok? s, none⟩
  | .list [.atom "binder_regular_blank", s, d] => do pure ⟨"_", ← tok? s, some (← idsOf d)⟩
  | _ => none

def bindersOf : SX → Option (List Binder) := listOf "binders_more" "binders_empty" binderOf

partial def convOf : SX → Option Conv
  | .list [.atom "conv_var", n] => (tok? n).map .var
  | .list [.atom "conv_app", h, args] => do
      pure (.app (← tok? h) (← listOf "convs_more" "convs_empty" convOf args))
  | .list [.atom "conv_sym", c] => (convOf c).map .sym
  | .list [.atom "conv_unfold", h, args, ds, c] => do
      pure (.unfold (← tok? h) (← exprsOf args) (← idsOf ds) (← convOf c))
  | _ => none

partial def proofOf : SX → Option Proof
  | .list [.atom "proof_hyp", n] => (tok? n).map .hyp
  | .list [.atom "proof_thm", h, args, ps] => do
      pure (.thm (← tok? h) (← exprsOf args) (← listOf "proofs_more" "proofs_empty" proofOf ps))
  | .list [.atom "proof_conv", e, c, p] => do pure (.conv (← exprOf e) (← convOf c) (← proofOf p))
  | .list [.atom "proof_let", n, p, q] => do pure (.let_ (← tok? n) (← proofOf p) (← proofOf q))
  | _ => none

def flag (yes : String) : SX → Bool
  | .list [.atom l] => l == yes
  | _ => false

def visible? : SX → Bool
  | .list [.atom l] => l == "visibility_default" || l == "visibility_local" || l == "visibility_pub"
  | _ => false

def stmtOf : SX → Option Stmt
  | .list [.atom "statement_sort", n, p, s, pr, f] => do
      pure (.sort (← tok? n) ⟨flag "pure_yes" p, flag "strict_yes" s, flag "provable_yes" pr, flag "free_yes" f⟩)
  | .list [.atom "statement_term", n, args, ret, deps] => do
      pure (.term (← tok? n) (← bindersOf args) (← tok? ret) (← idsOf deps))
  | .list [.atom "statement_axiom", n, args, hyps, concl] => do
      pure (.axiom_ (← tok? n) (← bindersOf args) (← exprsOf hyps) (← exprOf concl))
  | .list [.atom "statement_def", v, n, args, ret, deps, ds, value] =>
      if visible? v then do
        pure (.def_ (← tok? n) (← bindersOf args) (← tok? ret) (← idsOf deps) (← dummiesOf ds) (← exprOf value))
      else none
  | .list [.atom "statement_theorem", v, n, args, hyps, concl, ds, pf] =>
      if visible? v then do
        pure (.theorem (← tok? n) (← bindersOf args) (← hypsOf exprOf hyps) (← exprOf concl)
          (← dummiesOf ds) (← proofOf pf))
      else none
  | .list [.atom "statement_input", k] => (tok? k).map .io
  | .list [.atom "statement_output", k] => (tok? k).map .io
  | _ => none

/-! ## The state of a load -/

def Binder.bound (b : Binder) : Bool := b.deps.isNone
def Binder.depList (b : Binder) : List String := b.deps.getD []

/-- A term or definition: its binders, sort, the bound binders its sort depends on, and for a
definition its dummies and value. -/
structure TermInfo where
  args : List Binder
  ret : String
  retDeps : List String
  isDef : Bool
  dummies : List (String × String)
  deriving Inhabited

/-- An axiom or theorem as a rule: binders, hypothesis count, dependency facts. -/
structure AssertInfo where
  args : List Binder
  nhyps : Nat
  nfPairs : List (Nat × Nat)
  deriving Inhabited

structure State where
  sorts : Std.HashMap String SortMods := {}
  sortOrder : Array String := #[]
  /-- the sorts with bound variables (not `strict`), in order -/
  boundSorts : Array String := #[]
  /-- the terms and definitions without arguments, in order -/
  nullary : Array String := #[]
  terms : Std.HashMap String TermInfo := {}
  asserts : Std.HashMap String AssertInfo := {}
  out : Array String := #[]
  admitted : Nat := 0
  claims : Nat := 0
  stopped : Option String := none
  skipped : Array String := #[]

def j (s : String) : String := "mm0." ++ s
def c (s : String) : String := "mm0:" ++ s

def admit (st : State) (msg : String) : State :=
  { st with out := st.out.push s!"!(transform &admit () (add-atom &admit {msg}))", admitted := st.admitted + 1 }

def prems (ps : List String) : String := ps.foldr (fun p acc => s!"(prem {p} {acc})") "no-prem"

/-- The dependency facts of a statement: (i, j) for a bound binder i and a binder j that does not
depend on it: a later bound binder (the two are different variables), or a regular binder without
i among its dependencies (i is not free in it). At a use, these are MM0's conditions on the
substitution; inside the proof, they are hypotheses. -/
def nfPairs (args : List Binder) : List (Nat × Nat) :=
  let ix := args.zip (List.range args.length)
  ix.flatMap fun (bi, i) =>
    if !bi.bound then []
    else ix.filterMap fun (bj, j) =>
      if j == i then none
      else if bj.bound then (if j > i then some (i, j) else none)
      else if bj.depList.contains bi.name then none
      else some (i, j)

/-! ## Typing -/

/-- A context: each variable with its sort and whether it is a bound variable. -/
abbrev Ctx := List (String × String × Bool)

def ctxOf (args : List Binder) (dummies : List (String × String)) : Ctx :=
  args.map (fun b => (b.name, b.sort, b.bound)) ++ dummies.map fun (n, s) => (n, s, true)

/-- The sort of an expression, or why it has none; a bound argument is a bound variable of the
binder's sort. -/
partial def typeOf (st : State) (ctx : Ctx) : Expr → Except String String
  | .var v => match ctx.find? (·.1 == v) with
      | some (_, s, _) => .ok s
      | none => .error s!"unknown variable {v}"
  | .app h args => do
      match st.terms.get? h with
      | none => .error s!"unknown term {h}"
      | some info =>
          if info.args.length != args.length then .error s!"{h}: {args.length} arguments for {info.args.length}"
          else
            for (b, a) in info.args.zip args do
              if b.bound then
                match a with
                | .var v => match ctx.find? (·.1 == v) with
                    | some (_, s, true) =>
                        if s != b.sort then throw s!"{h}: an argument of sort {s} where {b.sort} is wanted"
                    | _ => throw s!"{h}: {v} is not a bound variable"
                | .app _ _ => throw s!"{h}: an expression where a bound variable is wanted"
              else
                let s ← typeOf st ctx a
                if s != b.sort then throw s!"{h}: an argument of sort {s} where {b.sort} is wanted"
            pure info.ret

/-- The free variables of a definition's value, in order of first appearance (MM0's definition
checking): a bound variable is free in itself, a regular variable in its dependencies; a term's
regular argument loses the bound arguments it depends on, and the term's sort adds the bound
arguments it depends on. -/
partial def freeVars (st : State) (ctx : Ctx) (args : List Binder) : Expr → List String
  | .var v => match ctx.find? (·.1 == v) with
      | some (_, _, true) => [v]
      | some (_, _, false) => (args.find? (·.name == v)).map (·.depList) |>.getD []
      | none => []
  | .app h xs => match st.terms.get? h with
      | none => []
      | some info =>
          let slots := info.args.zip xs
          let boundVar := fun (d : String) => match (info.args.findIdx? (·.name == d)) with
            | some k => match xs[k]? with
                | some (.var v) => some v
                | _ => none
            | none => none
          let inner := slots.flatMap fun (b, a) =>
            if b.bound then []
            else
              let drop := b.depList.filterMap boundVar
              (freeVars st ctx args a).filter (!drop.contains ·)
          let outer := info.retDeps.filterMap boundVar
          (inner ++ outer).foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) []

/-- The binders of a statement: sorts declared, bound variables not of a strict sort, each
dependency an earlier bound binder, names not repeated. -/
def checkBinders (st : State) (args : List Binder) : Except String Unit := do
  let mut seen : List Binder := []
  for b in args do
    match st.sorts.get? b.sort with
    | none => throw "a binder of an unknown sort"
    | some m =>
        if b.bound && m.strict then throw s!"a bound variable of the strict sort {b.sort}"
    for d in b.depList do
      if !(seen.any fun e => e.name == d && e.bound) then throw s!"{d} is not an earlier bound variable"
    if b.name != "_" && seen.any (·.name == b.name) then throw s!"variable {b.name} declared twice"
    seen := seen ++ [b]

/-- Dummies: sorts declared and allowing dummies (not `strict`, not `free`), names new. -/
def checkDummies (st : State) (args : List Binder) (ds : List (String × String)) : Except String Unit := do
  let mut seen : List String := args.map (·.name)
  for (n, s) in ds do
    match st.sorts.get? s with
    | none => throw s!"a dummy of the unknown sort {s}"
    | some m => if m.strict || m.free then throw s!"a dummy of the sort {s}, which has no dummies"
    if seen.contains n then throw s!"variable {n} declared twice"
    seen := seen ++ [n]

/-- The printed form of an expression, its variables named by `vn`. -/
partial def exprMetta (vn : String → String) : Expr → String
  | .var v => vn v
  | .app h [] => s!"({c h})"
  | .app h args => s!"({c h} " ++ " ".intercalate (args.map (exprMetta vn)) ++ ")"

/-- Variable names in a claim or rule: binders `$v1 …`, dummies `$w1 …`. -/
def varNames (args : List Binder) (ds : List (String × String)) (v : String) : String :=
  match (args.map (·.name)).findIdx? (· == v) with
  | some i => s!"$v{i + 1}"
  | none => match (ds.map (·.1)).findIdx? (· == v) with
      | some k => s!"$w{k + 1}"
      | none => s!"$unbound"

/-- A binder's fact: `(mm0.bv.S x)` for a bound binder, `(mm0.S a)` for a regular one. -/
def binderFact (b : Binder) (v : String) : String :=
  if b.bound then s!"(mm0.bv.{b.sort} {v})" else s!"({j b.sort} {v})"

/-! ## Proofs as nodes -/

structure PState where
  n : Nat := 0
  nodes : Array String := #[]
  memo : Std.HashMap String String := {}

abbrev PM := StateT PState (Except String)

def push (rule : String) (kids : List String) : PM String := do
  let s ← get
  let k := s.n + 1
  set { s with n := k, nodes := s.nodes.push (s!"{k} {rule} (" ++ " ".intercalate kids ++ ")") }
  pure (toString k)

/-- A node made once per claim. -/
def memoNode (key : String) (mk : PM String) : PM String := do
  match (← get).memo.get? key with
  | some r => pure r
  | none => do
      let r ← mk
      modify fun s => { s with memo := s.memo.insert key r }
      pure r

/-- A child that cites no fact: the kernel cannot discharge a premise with it, so the claim is
not accepted. The loader writes it where the proof file asks for something that does not hold (a
non-variable in a bound position, a dependency violation). -/
def noneRef : String := "(hyp none)"

/-- An expression as a memo key. -/
partial def exprKey : Expr → String
  | .var v => "v:" ++ v
  | .app h args => "(" ++ h ++ String.join (args.map fun a => " " ++ exprKey a) ++ ")"

/-- A claim's context: binders, dummies, its dependency facts, its hypothesis names. -/
structure PCtx where
  args : List Binder
  dummies : List (String × String)
  nf : List (Nat × Nat)
  hyps : List String

def PCtx.ctx (k : PCtx) : Ctx := ctxOf k.args k.dummies

/-- `(mm0.bv.S v)`: a bound binder's hypothesis, or a dummy's local through `mm0:dbv.S`. -/
def bvNode (k : PCtx) (v : String) : PM String :=
  match k.args.findIdx? (·.name == v) with
  | some i => if (k.args[i]!).bound then pure s!"(hyp {i})" else pure noneRef
  | none => match k.dummies.findIdx? (·.1 == v) with
      | some d => memoNode s!"bv:{v}" (push (c s!"dbv.{(k.dummies[d]!).2}") [s!"(local {d})"])
      | none => pure noneRef

/-- The sort fact of an argument term: a regular binder's hypothesis; a bound variable through
`mm0:bv-wf.S`; an application by its constructor over its arguments (built once per claim). -/
partial def syntaxNode (st : State) (k : PCtx) (e : Expr) : PM String := do
  match e with
  | .var v => match k.args.findIdx? (·.name == v) with
      | some i =>
          let b := k.args[i]!
          if b.bound then memoNode s!"e:{exprKey e}" (do let kid ← bvNode k v; push (c s!"bv-wf.{b.sort}") [kid])
          else pure s!"(hyp {i})"
      | none => match k.dummies.find? (·.1 == v) with
          | some (_, s) => memoNode s!"e:{exprKey e}" (do let kid ← bvNode k v; push (c s!"bv-wf.{s}") [kid])
          | none => throw s!"unknown variable {v}"
  | .app h xs => memoNode s!"e:{exprKey e}" do
      match st.terms.get? h with
      | none => throw s!"unknown term {h}"
      | some info =>
          if info.args.length != xs.length then throw s!"{h}: {xs.length} arguments for {info.args.length}"
          let kids ← (info.args.zip xs).mapM fun (b, a) =>
            if b.bound then
              match a with
              | .var v => bvNode k v
              | .app _ _ => pure noneRef
            else syntaxNode st k a
          push (c h) kids

/-- `(mm0.nf x e)`: the bound variable x is not among the variables of e. No step decides a side
condition on the claim's formals (the kernel's F5 rule): a dummy is fresh, so it is not free
wherever it does not occur (`mm0:nf-fresh`; the kernel checks `absent-from` with the dummy first,
which is stable); for a bound binder, a regular binder or a later bound binder is the claim's
declared dependency fact, an earlier bound binder or a dummy is that fact turned around
(`mm0:nf-sym`, for two bound variables), an application goes through `mm0:nf.f`. -/
partial def nfNode (st : State) (k : PCtx) (x : String) (e : Expr) : PM String :=
  memoNode s!"nf:{x} {exprKey e}" do
    match k.dummies.findIdx? (·.1 == x) with
    | some d =>
        match typeOf st k.ctx e with
        | .ok t => do
            let se ← syntaxNode st k e
            push (c s!"nf-fresh.{(k.dummies[d]!).2}.{t}") [s!"(local {d})", se]
        | .error _ => pure noneRef
    | none =>
      match k.args.findIdx? (·.name == x) with
      | none => pure noneRef
      | some i =>
          let bx := k.args[i]!
          if !bx.bound then pure noneRef
          else match e with
            | .var v =>
                match k.args.findIdx? (·.name == v) with
                | some jv =>
                    let bv := k.args[jv]!
                    match k.nf.findIdx? (· == (i, jv)) with
                    | some p => pure s!"(hyp {k.args.length + p})"
                    | none =>
                        if !bv.bound then pure noneRef
                        else match k.nf.findIdx? (· == (jv, i)) with
                          | some p => do
                              let kx ← bvNode k x
                              let kv ← bvNode k v
                              push (c s!"nf-sym.{bx.sort}.{bv.sort}") [s!"(hyp {k.args.length + p})", kx, kv]
                          | none => pure noneRef
                | none => match k.dummies.find? (·.1 == v) with
                    | some (_, s) => do
                        let back ← nfNode st k v (.var x)
                        let kx ← bvNode k x
                        let kv ← bvNode k v
                        push (c s!"nf-sym.{bx.sort}.{s}") [back, kx, kv]
                    | none => throw s!"unknown variable {v}"
            | .app h xs =>
                if xs.isEmpty then do
                  let kx ← bvNode k x
                  push (c s!"nf.{h}.{bx.sort}") [kx]
                else do
                  let kids ← xs.mapM (nfNode st k x)
                  push (c s!"nf.{h}") kids

/-- The fact for an argument at a binder: a bound variable's, or the expression's sort. -/
def argFact (st : State) (k : PCtx) (b : Binder) (e : Expr) : PM String :=
  if b.bound then
    match e with
    | .var v => bvNode k v
    | .app _ _ => pure noneRef
  else syntaxNode st k e

/-- The children of a use of a rule with these binders and dependency facts. -/
def useKids (st : State) (k : PCtx) (args : List Binder) (nf : List (Nat × Nat)) (es : List Expr) :
    PM (List String) := do
  let bs ← (args.zip es).mapM fun (b, e) => argFact st k b e
  let nfs ← nf.mapM fun (i, jx) =>
    match es[i]? with
    | some (.var x) => nfNode st k x (es[jx]?.getD (.var ""))
    | _ => pure noneRef
  pure (bs ++ nfs)

/-- The two sides of a conversion (MM0's conversion checker computes the same). -/
partial def convSides : Conv → Except String (Expr × Expr)
  | .var v => .ok (.var v, .var v)
  | .app h cs => do
      let ss ← cs.mapM convSides
      pure (.app h (ss.map (·.1)), .app h (ss.map (·.2)))
  | .sym inner => do
      let (a, b) ← convSides inner
      pure (b, a)
  | .unfold h es _ inner => do
      let (_, b) ← convSides inner
      pure (.app h es, b)

partial def convNode (st : State) (k : PCtx) : Conv → PM String
  | .var v => do
      match k.ctx.find? (·.1 == v) with
      | some (_, s, _) => do
          let kid ← syntaxNode st k (.var v)
          push (c s!"cv-refl.{s}") [kid]
      | none => throw s!"conversion on unknown variable {v}"
  | .app h cs => do
      match st.terms.get? h with
      | none => throw s!"unknown term {h}"
      | some info =>
          if info.args.length != cs.length then throw s!"{h}: {cs.length} arguments for {info.args.length}"
          let kids ← cs.mapM (convNode st k)
          let sides ← match cs.mapM convSides with
            | .ok s => pure s
            | .error e => throw e
          let fa ← (info.args.zip sides).mapM fun (b, (l, _)) => argFact st k b l
          let fb ← (info.args.zip sides).mapM fun (b, (_, r)) => argFact st k b r
          push (c s!"cv-cong.{h}") (kids ++ fa ++ fb)
  | .sym inner => do
      let kid ← convNode st k inner
      push (c "cv-sym") [kid]
  | .unfold h es ds inner => do
      match st.terms.get? h with
      | none => throw s!"unknown definition {h}"
      | some info =>
          if !info.isDef then throw s!"{h} is not a definition"
          if info.args.length != es.length then throw s!"{h}: {es.length} arguments for {info.args.length}"
          if info.dummies.length != ds.length then throw s!"{h}: {ds.length} dummies for {info.dummies.length}"
          let as ← useKids st k info.args [] es
          let dv ← ds.mapM (bvNode k)
          let na ← ds.flatMap (fun d => es.map fun e => (d, e)) |>.mapM fun (d, e) => nfNode st k d e
          let pairs := (ds.zip (List.range ds.length)).flatMap fun (d, a) =>
            (ds.zip (List.range ds.length)).filterMap fun (d', b) => if a < b then some (d, d') else none
          let nd ← pairs.mapM fun (d, d') => nfNode st k d (.var d')
          let u ← push (c s!"cv-unfold.{h}") (as ++ dv ++ na ++ nd)
          let m ← convNode st k inner
          push (c "cv-trans") [u, m]

partial def proofNode (st : State) (k : PCtx) (heap : List (String × String)) : Proof → PM String
  | .hyp h => match heap.lookup h with
      | some r => pure r
      | none => match k.hyps.findIdx? (· == h) with
          | some i => pure s!"(hyp {k.args.length + k.nf.length + i})"
          | none => throw s!"unknown hypothesis {h}"
  | .thm h es ps => do
      match st.asserts.get? h with
      | none => throw s!"unknown theorem {h}"
      | some a =>
          if a.args.length != es.length then throw s!"{h}: {es.length} arguments for {a.args.length}"
          else if a.nhyps != ps.length then throw s!"{h}: {ps.length} subproofs for {a.nhyps}"
          else do
            let use ← useKids st k a.args a.nfPairs es
            let p ← ps.mapM (proofNode st k heap)
            push (c h) (use ++ p)
  | .conv _ cv inner => do
      let kc ← convNode st k cv
      let p ← proofNode st k heap inner
      push (c "conv") [kc, p]
  | .let_ h p q => do
      if (heap.lookup h).isSome || k.hyps.contains h then throw s!"subproof name shadowing at {h}"
      let r ← proofNode st k heap p
      proofNode st k ((h, r) :: heap) q

/-! ## The fold -/

def chunkNodes : Nat := 50

def proofCells (nodes : List String) (tail : String) : String :=
  String.join (nodes.map fun nd => "(node " ++ nd ++ " ") ++ tail ++
    String.ofList (List.replicate nodes.length ')')

def proofChunks (nodes : List String) : List String :=
  let parts := nodes.toChunks chunkNodes
  let parts := if parts.isEmpty then [[]] else parts
  parts.zipIdx.map fun (p, k) =>
    proofCells p (if k + 1 < parts.length then s!"(more {k + 1})" else "no-node")

def stop (st : State) (k : Nat) (label why : String) : State :=
  { st with stopped := some s!"statement {k} {label}: {why}" }

def checkStatementExprs (st : State) (args : List Binder) (es : List Expr) : Except String Unit := do
  let ctx := ctxOf args []
  for e in es do
    let s ← typeOf st ctx e
    match st.sorts.get? s with
    | some m => if !m.provable then throw s!"a statement of the unprovable sort {s}"
    | none => throw s!"unknown sort {s}"

/-- The premises of an axiom or theorem: binder facts, dependency facts, hypotheses. -/
def assertPrems (args : List Binder) (vn : String → String) (hyps : List Expr) : List String :=
  args.map (fun b => binderFact b (vn b.name)) ++
    (nfPairs args).map (fun (i, jx) => s!"(mm0.nf {vn (args[i]!).name} {vn (args[jx]!).name})") ++
    hyps.map fun h => s!"(mm0.pf {exprMetta vn h})"

/-- Rules for a new sort: its judgment and reflexivity; with bound variables (not `strict`), the
bound-variable judgment, `bv-wf`, the symmetry of independence between two bound variables
(`nf-sym`) with every earlier such sort, and `nf.c.S` for the nullary terms so far; with dummies
(also not `free`), the dummy judgment, which is the only sort the kernel is told of (only a
claim's local states it), `dbv` and `nf-fresh` with every sort so far; and `nf-fresh` from every
earlier sort with dummies into this one. -/
def sortRules (st : State) (n : String) (m : SortMods) : State := Id.run do
  let mut st := admit st s!"(admit-judgment {j n} 1)"
  st := admit st s!"(admit-rule {c s!"cv-refl.{n}"} ($e) {prems [s!"({j n} $e)"]} (mm0.cv $e $e))"
  let nfSym := fun (st : State) (a b : String) =>
    admit st s!"(admit-rule {c s!"nf-sym.{a}.{b}"} ($x $y) {prems ["(mm0.nf $y $x)", s!"(mm0.bv.{a} $x)", s!"(mm0.bv.{b} $y)"]} (mm0.nf $x $y))"
  let nfFresh := fun (st : State) (a b : String) =>
    admit st s!"(admit-rule {c s!"nf-fresh.{a}.{b}"} ($d $e) {prems [s!"(mm0.dbv.{a} $d)", s!"({j b} $e)", "(absent-from $d $e)"]} (mm0.nf $d $e))"
  if !m.strict then
    st := admit st s!"(admit-judgment mm0.bv.{n} 1)"
    st := admit st s!"(admit-rule {c s!"bv-wf.{n}"} ($x) {prems [s!"(mm0.bv.{n} $x)"]} ({j n} $x))"
    for t in st.boundSorts do
      st := nfSym st t n
      st := nfSym st n t
    st := nfSym st n n
    for f in st.nullary do
      st := admit st s!"(admit-rule {c s!"nf.{f}.{n}"} ($x) {prems [s!"(mm0.bv.{n} $x)"]} (mm0.nf $x ({c f})))"
    st := { st with boundSorts := st.boundSorts.push n }
  if !m.strict && !m.free then
    st := admit st s!"(admit-judgment mm0.dbv.{n} 1)"
    st := admit st s!"(admit-sort mm0.dbv.{n})"
    st := admit st s!"(admit-rule {c s!"dbv.{n}"} ($x) {prems [s!"(mm0.dbv.{n} $x)"]} (mm0.bv.{n} $x))"
    for t in st.sortOrder do
      st := nfFresh st n t
    st := nfFresh st n n
  for t in st.sortOrder do
    match st.sorts.get? t with
    | some mt => if !mt.strict && !mt.free then st := nfFresh st t n
    | none => pure ()
  return { st with sorts := st.sorts.insert n m, sortOrder := st.sortOrder.push n }

def step (st : State) (k : Nat) : Stmt → State
  | .sort n mods =>
      if st.sorts.contains n then stop st k n "sort declared twice"
      else sortRules st n mods
  | .term n args ret deps => termOrDef st k n args ret deps none
  | .def_ n args ret deps ds value => termOrDef st k n args ret deps (some (ds, value))
  | .axiom_ n args hyps concl =>
      if st.asserts.contains n then stop st k n "declared twice"
      else match checkBinders st args, checkStatementExprs st args (concl :: hyps) with
        | .error e, _ => stop st k n e
        | _, .error e => stop st k n e
        | .ok (), .ok () =>
          let vn := varNames args []
          let st := { st with asserts := st.asserts.insert n ⟨args, hyps.length, nfPairs args⟩ }
          admit st (s!"(admit-rule {c n} (" ++ " ".intercalate (args.map (vn ·.name)) ++ s!") " ++
            s!"{prems (assertPrems args vn hyps)} (mm0.pf {exprMetta vn concl}))")
  | .theorem n args hyps concl ds proof =>
      if st.asserts.contains n then stop st k n "declared twice"
      else match checkBinders st args, checkStatementExprs st args (concl :: hyps.map (·.2)), checkDummies st args ds with
        | .error e, _, _ => stop st k n e
        | _, .error e, _ => stop st k n e
        | _, _, .error e => stop st k n e
        | .ok (), .ok (), .ok () =>
          let vn := varNames args ds
          let pctx : PCtx := ⟨args, ds, nfPairs args, hyps.map (·.1)⟩
          match (proofNode st pctx [] proof).run {} with
          | .error e => stop st k n e
          | .ok (root, ps') =>
              let chains := proofChunks ps'.nodes.toList
              let dvars := (List.range ds.length).map fun i => s!"$w{i + 1}"
              let locals := ds.zip dvars |>.map fun ((_, s), w) => s!"(mm0.dbv.{s} {w})"
              let msg := s!"(claim {c n} {root} (" ++ " ".intercalate (args.map (vn ·.name)) ++ ") (" ++
                " ".intercalate dvars ++ ") " ++ prems (assertPrems args vn (hyps.map (·.2))) ++
                " (" ++ " ".intercalate locals ++ s!") () (mm0.pf {exprMetta vn concl}) () " ++
                chains.headD "no-node" ++ ")"
              let first := s!"!(transform &submit () (add-atom &submit {msg}))"
              let rest := (chains.drop 1).zipIdx.map fun (ch, i) =>
                s!"!(transform &submit () (add-atom &submit (chunk {c n} {i + 1} {ch})))"
              { st with out := (st.out.push first) ++ rest.toArray,
                        asserts := st.asserts.insert n ⟨args, hyps.length, nfPairs args⟩, claims := st.claims + 1 }
  | .io kind => { st with skipped := st.skipped.push s!"statement {k}: ({kind}) input/output is not checked" }
where
  termOrDef (st : State) (k : Nat) (n : String) (args : List Binder) (ret : String) (deps : List String)
      (dv : Option (List (String × String) × Expr)) : State :=
    if st.terms.contains n then stop st k n "term declared twice"
    else match checkBinders st args with
    | .error e => stop st k n e
    | .ok () =>
      match st.sorts.get? ret with
      | none => stop st k n s!"unknown sort {ret}"
      | some m =>
        if m.pure then stop st k n s!"a {if dv.isSome then "definition" else "term"} of the pure sort {ret}"
        else match deps.find? (fun d => !(args.any fun b => b.name == d && b.bound)) with
        | some d => stop st k n s!"{d} is not a bound argument"
        | none =>
          let check : Except String Unit := match dv with
            | none => .ok ()
            | some (ds, value) => do
                checkDummies st args ds
                let s ← typeOf st (ctxOf args ds) value
                if s != ret then throw s!"a value of sort {s} for {ret}"
                match (freeVars st (ctxOf args ds) args value).find? (!deps.contains ·) with
                | some v => throw s!"{v} is free in the value and not a dependency"
                | none => pure ()
          match check with
          | .error e => stop st k n e
          | .ok () =>
            let info : TermInfo := ⟨args, ret, deps, dv.isSome, (dv.map (·.1)).getD []⟩
            let st := { st with terms := st.terms.insert n info,
                                nullary := if args.isEmpty then st.nullary.push n else st.nullary }
            termRules st n args ret dv
  termRules (st : State) (n : String) (args : List Binder) (ret : String)
      (dv : Option (List (String × String) × Expr)) : State := Id.run do
    let xs := (List.range args.length).map fun i => s!"$a{i + 1}"
    let ys := (List.range args.length).map fun i => s!"$b{i + 1}"
    let app (vs : List String) := if vs.isEmpty then s!"({c n})" else s!"({c n} " ++ " ".intercalate vs ++ ")"
    let argPrems := (args.zip xs).map fun (b, x) => binderFact b x
    let mut st := admit st (s!"(admit-rule {c n} (" ++ " ".intercalate xs ++ s!") {prems argPrems} ({j ret} {app xs}))")
    -- typed congruence: each side's arguments have their binders' facts (MM0's conversion checker
    -- checks the same), so every conversion relates well-formed expressions
    let cong := (xs.zip ys).map fun (x, y) => s!"(mm0.cv {x} {y})"
    let factsA := (args.zip xs).map fun (b, x) => binderFact b x
    let factsB := (args.zip ys).map fun (b, y) => binderFact b y
    st := admit st (s!"(admit-rule {c s!"cv-cong.{n}"} (" ++ " ".intercalate (xs ++ ys) ++
      s!") {prems (cong ++ factsA ++ factsB)} (mm0.cv {app xs} {app ys}))")
    if args.isEmpty then
      for s in st.boundSorts do
        st := admit st s!"(admit-rule {c s!"nf.{n}.{s}"} ($x) {prems [s!"(mm0.bv.{s} $x)"]} (mm0.nf $x ({c n})))"
    else
      st := admit st (s!"(admit-rule {c s!"nf.{n}"} ($x " ++ " ".intercalate xs ++ s!") " ++
        s!"{prems (xs.map fun x => s!"(mm0.nf $x {x})")} (mm0.nf $x {app xs}))")
    match dv with
    | none => pure ()
    | some (ds, v) =>
        let dsv := (List.range ds.length).map fun i => s!"$d{i + 1}"
        let vn := fun name => match (args.map (·.name)).findIdx? (· == name) with
          | some i => s!"$a{i + 1}"
          | none => match (ds.map (·.1)).findIdx? (· == name) with
              | some i => s!"$d{i + 1}"
              | none => "$unbound"
        let dprems := (ds.zip dsv).map fun ((_, s), d) => s!"(mm0.bv.{s} {d})"
        let nfa := dsv.flatMap fun d => xs.map fun x => s!"(mm0.nf {d} {x})"
        let pairs := (dsv.zip (List.range dsv.length)).flatMap fun (d, a) =>
          (dsv.zip (List.range dsv.length)).filterMap fun (d', b) => if a < b then some s!"(mm0.nf {d} {d'})" else none
        st := admit st (s!"(admit-rule {c s!"cv-unfold.{n}"} (" ++ " ".intercalate (xs ++ dsv) ++ s!") " ++
          s!"{prems (argPrems ++ dprems ++ nfa ++ pairs)} (mm0.cv {app xs} {exprMetta vn v}))")
    return st

/-- The kernel program for the statements, until the first one the loader refuses. -/
def load (stmts : List Stmt) (maxClaims : Nat) : State := Id.run do
  let mut st : State := {}
  let mut k := 0
  for s in stmts do
    if st.claims ≥ maxClaims || st.stopped.isSome then break
    st := step st k s
    k := k + 1
  return st

/-- The judgments and rules every MM0 load shares. -/
def prelude : List String :=
  ["(admit-judgment mm0.pf 1)", "(admit-judgment mm0.cv 2)",
   "(admit-rule mm0:cv-sym ($a $b) (prem (mm0.cv $a $b) no-prem) (mm0.cv $b $a))",
   "(admit-rule mm0:cv-trans ($a $b $c) (prem (mm0.cv $a $b) (prem (mm0.cv $b $c) no-prem)) (mm0.cv $a $c))",
   "(admit-rule mm0:conv ($e $f) (prem (mm0.cv $e $f) (prem (mm0.pf $f) no-prem)) (mm0.pf $e))",
   "(admit-judgment mm0.nf 2)"]

/-! ## Matching the specification

`MM0.Expect` prints one canonical line per sort, term, definition, axiom and theorem of the `.mm0`
file. Here the same line is printed for each statement of the proof file; every statement that is
not `local` must print the next line of the specification (a definition whose specification has
no value matches by its header), and the proof file must reach the specification's end. -/

def bit (b : Bool) : String := if b then "1" else "0"

def sortedNats (xs : List Nat) : List Nat := xs.mergeSort (· ≤ ·)

/-- Dependencies as sorted positions. -/
def depsText (xs : List Nat) : String := "(" ++ " ".intercalate ((sortedNats xs).map toString) ++ ")"

def posIn (args : List Binder) (v : String) : Option Nat := (args.map (·.name)).findIdx? (· == v)

def boundPos (args : List Binder) (d : String) : Except String Nat :=
  match args.findIdx? (fun b => b.name == d && b.deps.isNone) with
  | some i => .ok i
  | none => .error s!"{d} is not a bound argument"

def binderText (args : List Binder) (b : Binder) : Except String String :=
  match b.deps with
  | none => .ok s!"(b {b.sort})"
  | some ds => do pure s!"(r {b.sort} {depsText (← ds.mapM (boundPos args))})"

def argsText (args : List Binder) : Except String String := do
  pure ("(" ++ " ".intercalate (← args.mapM (binderText args)) ++ ")")

/-- An expression with variables by position (`#i`). -/
partial def exprText (pos : String → Option Nat) : Expr → Except String String
  | .var x => match pos x with
      | some i => .ok s!"#{i}"
      | none => .error s!"variable {x} has no position"
  | .app f args => do pure ("(" ++ " ".intercalate (f :: (← args.mapM (exprText pos))) ++ ")")

/-- Dummies in order of first occurrence. -/
partial def dummyOrder (isDummy : String → Bool) : Expr → List String → List String
  | .var x, acc => if isDummy x && !acc.contains x then acc ++ [x] else acc
  | .app _ args, acc => args.foldl (fun acc e => dummyOrder isDummy e acc) acc

/-- The canonical line of a proof-file statement and, for a definition, its header alone. -/
def canon : Stmt → Except String (String × Option String)
  | .sort n m => .ok (s!"(sort {n} {bit m.pure} {bit m.strict} {bit m.provable} {bit m.free})", none)
  | .term n args ret deps => do
      let sig := s!"{← argsText args} (r {ret} {depsText (← deps.mapM (boundPos args))})"
      pure (s!"(term {n} {sig})", none)
  | .def_ n args ret deps ds value => do
      let sig := s!"{← argsText args} (r {ret} {depsText (← deps.mapM (boundPos args))})"
      let isDummy := fun x => ds.any (·.1 == x) && !(args.any (·.name == x))
      let order := dummyOrder isDummy value []
      let pos := fun x => match posIn args x with
        | some i => some i
        | none => (order.findIdx? (· == x)).map (args.length + ·)
      let sorts := order.filterMap fun x => ds.lookup x
      pure (s!"(def {n} {sig} ({" ".intercalate sorts}) {← exprText pos value})", some s!"(def {n} {sig})")
  | .axiom_ n args hyps concl => do
      let hs ← hyps.mapM (exprText (posIn args))
      pure (s!"(axiom {n} {← argsText args} ({" ".intercalate hs}) {← exprText (posIn args) concl})", none)
  | .theorem n args hyps concl _ _ => do
      let hs ← hyps.mapM fun (_, e) => exprText (posIn args) e
      pure (s!"(theorem {n} {← argsText args} ({" ".intercalate hs}) {← exprText (posIn args) concl})", none)
  | .io k => .error s!"{k}: input and output statements are not supported"

def stmtName : Stmt → String
  | .sort n _ | .term n _ _ _ | .def_ n _ _ _ _ _ | .axiom_ n _ _ _ | .theorem n _ _ _ _ _ => n
  | .io k => k

/-- Whether a statement item is `local` (a definition or theorem the specification does not list). -/
def localOf : SX → Bool
  | .list (.atom l :: v :: _) => (l == "statement_def" || l == "statement_theorem") && flag "visibility_local" v
  | _ => false

/-- The load checked against the specification's lines. -/
def loadSpec (spec : Array String) (stmts : List (Stmt × Bool)) (maxClaims : Nat) : State := Id.run do
  let mut st : State := {}
  let mut k := 0
  let mut e := 0
  for (s, isLocal) in stmts do
    if st.claims ≥ maxClaims || st.stopped.isSome then break
    if !isLocal then
      match canon s with
      | .error why => st := stop st k (stmtName s) why
      | .ok (full, header) =>
          match spec[e]? with
          | none => st := stop st k (stmtName s) "not in the specification"
          | some line =>
              if line == full || some line == header then e := e + 1
              else st := stop st k (stmtName s) s!"does not match the specification, which has {line}"
    if st.stopped.isNone then st := step st k s
    k := k + 1
  if st.stopped.isNone && st.claims < maxClaims && e < spec.size then
    st := { st with stopped := some s!"the specification has {spec.size - e} more statements, from {spec[e]!}" }
  return st

end Mettapedia.GSLT.Readers.MM0.Load
