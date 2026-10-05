import Mettapedia.Languages.MM0.Kernel.Context

/-!
# The MMB proof machine

The reference semantics of proof checking in the MMB format, at the level of
commands: the byte layout is decoded elsewhere. It follows the MMB format
description and the reference verifiers, `mm0-c` and the Rust importer.

* Expressions are allocated in a store and referred to by position. Equality of
  expressions, as used by `Refl`, `Ref` of a conversion and unification, is
  equality of positions, not of structure: two applications of the same term to
  the same arguments, allocated separately, are different.
* Each allocated expression has a type: a sort, whether it is a bound variable,
  and the bound variables it depends on, named by their rank among the bound
  variables of the statement.
* The stack holds expressions, proofs, conversion proofs and conversion
  obligations. The heap holds anything except obligations.
* A theorem application or a definition unfolding runs a unification machine on
  the declaration's unify stream.

The unify stream of a theorem lists the conclusion first and then, after each
`UHyp`, the hypotheses from the last to the first. Both reference verifiers read
it this way; the format description states the opposite order.

Bound variables are not limited to the 55 dependency bits of the byte format
here; that limit belongs to the byte decoder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Formats.MMB

open Mettapedia.Languages.MM0.Kernel (SortInfo)

/-- The type of an argument or an allocated expression. -/
structure ExprType where
  sort : Nat
  bound : Bool
  deps : Finset Nat
  deriving DecidableEq

/-- An expression of the source type may stand where the target type is
expected: the same sort, and bound if the target is bound. -/
def ExprType.fits (source target : ExprType) : Bool :=
  source.sort == target.sort && (!target.bound || source.bound)

inductive UnifyCmd where
  | term (term : Nat)
  | termSave (term : Nat)
  | ref (index : Nat)
  | dummy (sort : Nat)
  | hyp
  deriving DecidableEq

inductive ProofCmd where
  | term (term : Nat)
  | termSave (term : Nat)
  | ref (index : Nat)
  | dummy (sort : Nat)
  | thm (index : Nat)
  | thmSave (index : Nat)
  | hyp
  | conv
  | refl
  | symm
  | cong
  | unfold
  | convCut
  | convSave
  | save
  deriving DecidableEq

/-- An entry of the term table: the return sort recorded in the table,
argument types, the return type, and for a definition the unify stream of its
value. The table's return sort and the return type's sort must agree. -/
structure TermEntry where
  sort : Nat
  args : List ExprType
  ret : ExprType
  value : Option (List UnifyCmd)

/-- An entry of the theorem table: argument types and the unify stream of its
statement. -/
structure ThmEntry where
  args : List ExprType
  unify : List UnifyCmd

structure Tables where
  sorts : List SortInfo
  terms : List TermEntry
  thms : List ThmEntry

/-- An allocated expression: a variable, by its position among the statement's
arguments and dummies, or a term applied to allocated arguments. -/
inductive Node where
  | var (position : Nat)
  | app (term : Nat) (args : List Nat)
  deriving DecidableEq

structure Alloc where
  node : Node
  type : ExprType
  deriving DecidableEq

/-- Stack and heap elements. -/
inductive Elem where
  | expr (e : Nat)
  | proof (e : Nat)
  | conv (left right : Nat)
  | goal (left right : Nat)
  deriving DecidableEq

/-- A machine state. Stacks have their top first. Variables are numbered by
their position in the statement's context: the arguments, then the dummies in
the order they are introduced. -/
structure State where
  store : List Alloc
  stack : List Elem
  heap : List Elem
  hyps : List Nat
  nextBound : Nat
  varCount : Nat
  deriving DecidableEq

inductive Mode where
  | definition
  | assertion
  deriving DecidableEq

namespace State

def typeOf (state : State) (e : Nat) : Option ExprType := (state.store[e]?).map (·.type)

def alloc (state : State) (alloc : Alloc) : State × Nat :=
  ({ state with store := state.store ++ [alloc] }, state.store.length)

def push (state : State) (elem : Elem) : State := { state with stack := elem :: state.stack }

def pop (state : State) : Option (Elem × State) :=
  match state.stack with
  | [] => none
  | elem :: rest => some (elem, { state with stack := rest })

def popExpr (state : State) : Option (Nat × State) := do
  let (elem, state) ← state.pop
  match elem with
  | .expr e => some (e, state)
  | _ => none

/-- Pop `count` expressions; the result lists them from the deepest. -/
def popExprs (state : State) : Nat → Option (List Nat × State)
  | 0 => some ([], state)
  | count + 1 => do
      let (last, state) ← state.popExpr
      let (earlier, state) ← state.popExprs count
      pure (earlier ++ [last], state)

end State

/-! ## Dependencies of a new application -/

/-- The dependencies of `t e₁ … eₙ` from the argument types. In a definition,
a regular argument's dependencies on the term's own bound arguments are
removed, and the return type's dependencies on them are added; in a theorem
every variable counts. -/
def appDeps (mode : Mode) (targets : List ExprType) (ret : ExprType)
    (sources : List ExprType) : Finset Nat :=
  let rec go : List ExprType → List ExprType → List (Finset Nat) → Finset Nat
    | target :: targets, source :: sources, boundDeps =>
        if target.bound then go targets sources (boundDeps ++ [source.deps])
        else
          let own := if mode = .definition then
              (boundDeps.zipIdx.foldl (fun deps (bound, j) =>
                if j ∈ target.deps then deps \ bound else deps) source.deps)
            else source.deps
          own ∪ go targets sources boundDeps
    | _, _, boundDeps =>
        if mode = .definition then
          boundDeps.zipIdx.foldl (fun deps (bound, j) =>
            if j ∈ ret.deps then deps ∪ bound else deps) ∅
        else ∅
  go targets sources []

/-- The disjointness checks of a theorem application: a bound argument is
disjoint from every earlier argument; a regular argument is disjoint from each
earlier bound argument it is not declared to depend on. -/
def thmArgsDisjoint (targets : List ExprType) (sources : List ExprType) : Bool :=
  let rec go : List ExprType → List ExprType → List ExprType → List (Finset Nat) → Bool
    | target :: targets, source :: sources, earlier, boundDeps =>
        (if target.bound then
            earlier.all (fun previous => Disjoint previous.deps source.deps)
          else
            boundDeps.zipIdx.all (fun (bound, j) => j ∈ target.deps || Disjoint bound source.deps)) &&
          go targets sources (earlier ++ [source])
            (if target.bound then boundDeps ++ [source.deps] else boundDeps)
    | _, _, _, _ => true
  go targets sources [] []

/-! ## Unification -/

inductive UMode where
  | definition
  | apply
  | statement
  deriving DecidableEq

/-- A unification state: the unify stack, the unify heap (entries saved by
`UTermSave` are marked), the main stack and the hypothesis list. -/
structure Unifier where
  stack : List Nat
  heap : List (Nat × Bool)
  main : List Elem
  hyps : List Nat

/-- `UTerm t` and `UTermSave t`: the expression on top must be an application
of `t`; its arguments replace it, the first on top. -/
def unifyTerm (store : List Alloc) (u : Unifier) (t : Nat) (save : Bool) : Option Unifier :=
  match u.stack with
  | e :: rest => do
      let alloc ← store[e]?
      match alloc.node with
      | .app head args =>
          if head = t then
            some { u with
              stack := args ++ rest
              heap := if save then u.heap ++ [(e, true)] else u.heap }
          else none
      | .var _ => none
  | [] => none

def unifyStep (store : List Alloc) (mode : UMode) (u : Unifier) : UnifyCmd → Option Unifier
  | .ref index => do
      let (entry, _) ← u.heap[index]?
      match u.stack with
      | e :: rest => if e = entry then some { u with stack := rest } else none
      | [] => none
  | .term t => unifyTerm store u t false
  | .termSave t => unifyTerm store u t true
  | .dummy sort => do
      if mode ≠ .definition then none else
      match u.stack with
      | e :: rest => do
          let alloc ← store[e]?
          match alloc.node with
          | .var _ =>
              if alloc.type.bound ∧ alloc.type.sort = sort ∧
                  u.heap.all (fun (entry, saved) => saved ||
                    ((store[entry]?).map (fun a => decide (Disjoint a.type.deps alloc.type.deps))).getD false) then
                some { u with stack := rest, heap := u.heap ++ [(e, false)] }
              else none
          | .app _ _ => none
      | [] => none
  | .hyp =>
      match mode with
      | .apply =>
          match u.main with
          | .proof e :: rest => some { u with stack := e :: u.stack, main := rest }
          | _ => none
      | .statement =>
          if u.stack = [] then
            match u.hyps with
            | e :: rest => some { u with stack := [e], hyps := rest }
            | [] => none
          else none
      | .definition => none

/-- Run a unify stream. It must end with an empty unify stack, and when it
checks a statement, with every hypothesis consumed. -/
def unifyRun (store : List Alloc) (mode : UMode) : Unifier → List UnifyCmd → Option Unifier
  | u, [] => if u.stack = [] ∧ (mode ≠ .statement ∨ u.hyps = []) then some u else none
  | u, cmd :: cmds => do
      let u ← unifyStep store mode u cmd
      unifyRun store mode u cmds

/-! ## Proof commands -/

/-- `Term t` and `TermSave t`. -/
def stepTerm (tables : Tables) (mode : Mode) (state : State) (t : Nat) (save : Bool) :
    Option State := do
  let entry ← tables.terms[t]?
  let (args, state) ← state.popExprs entry.args.length
  let types ← args.mapM state.typeOf
  if (types.zip entry.args).all (fun (source, target) => source.fits target) then
    let type : ExprType := ⟨entry.sort, false, appDeps mode entry.args entry.ret types⟩
    let (state, e) := state.alloc ⟨.app t args, type⟩
    let state := state.push (.expr e)
    pure (if save then { state with heap := state.heap ++ [.expr e] } else state)
  else none

/-- `Thm T` and `ThmSave T`. -/
def stepThm (tables : Tables) (state : State) (T : Nat) (save : Bool) : Option State := do
  let entry ← tables.thms[T]?
  let (e, state) ← state.popExpr
  let (args, state) ← state.popExprs entry.args.length
  let types ← args.mapM state.typeOf
  if (types.zip entry.args).all (fun (source, target) => source.fits target) &&
      thmArgsDisjoint entry.args types then
    let u ← unifyRun state.store .apply
      ⟨[e], args.map (·, false), state.stack, state.hyps⟩ entry.unify
    let state := { state with stack := .proof e :: u.main }
    pure (if save then { state with heap := state.heap ++ [.proof e] } else state)
  else none

def step (tables : Tables) (mode : Mode) (state : State) : ProofCmd → Option State
  | .term t => stepTerm tables mode state t false
  | .termSave t => stepTerm tables mode state t true
  | .ref index =>
      match state.heap[index]? with
      | some (.conv left right) =>
          match state.stack with
          | .goal left' right' :: rest =>
              if left' = left ∧ right' = right then some { state with stack := rest } else none
          | _ => none
      | some elem => some (state.push elem)
      | none => none
  | .dummy sort =>
      match tables.sorts[sort]? with
      | some info =>
          if info.strict = false ∧ info.free = false then
            let (state', e) := state.alloc ⟨.var state.varCount, ⟨sort, true, {state.nextBound}⟩⟩
            some { state' with
              stack := .expr e :: state'.stack
              heap := state'.heap ++ [.expr e]
              nextBound := state'.nextBound + 1
              varCount := state'.varCount + 1 }
          else none
      | none => none
  | .thm T => if mode = .assertion then stepThm tables state T false else none
  | .thmSave T => if mode = .assertion then stepThm tables state T true else none
  | .hyp =>
      if mode = .assertion then do
        let (e, state) ← state.popExpr
        let type ← state.typeOf e
        let info ← tables.sorts[type.sort]?
        if info.provable then
          some { state with hyps := e :: state.hyps, heap := state.heap ++ [.proof e] }
        else none
      else none
  | .conv =>
      match state.stack with
      | .proof right :: .expr left :: rest => some { state with stack := .goal left right :: .proof left :: rest }
      | _ => none
  | .refl =>
      match state.stack with
      | .goal left right :: rest => if left = right then some { state with stack := rest } else none
      | _ => none
  | .symm =>
      match state.stack with
      | .goal left right :: rest => some { state with stack := .goal right left :: rest }
      | _ => none
  | .cong =>
      match state.stack with
      | .goal left right :: rest => do
          let leftAlloc ← state.store[left]?
          let rightAlloc ← state.store[right]?
          match leftAlloc.node, rightAlloc.node with
          | .app t leftArgs, .app t' rightArgs =>
              if t = t' then
                some { state with
                  stack := (leftArgs.zip rightArgs).map (fun (l, r) => Elem.goal l r) ++ rest }
              else none
          | _, _ => none
      | _ => none
  | .unfold =>
      match state.stack with
      | .expr e :: .goal left right :: rest => do
          let leftAlloc ← state.store[left]?
          match leftAlloc.node with
          | .app t args => do
              let entry ← tables.terms[t]?
              let value ← entry.value
              let u ← unifyRun state.store .definition
                ⟨[e], args.map (·, false), rest, state.hyps⟩ value
              some { state with stack := .goal e right :: u.main }
          | .var _ => none
      | _ => none
  | .convCut =>
      match state.stack with
      | .goal left right :: rest => some { state with stack := .goal left right :: .conv left right :: rest }
      | _ => none
  | .convSave =>
      match state.stack with
      | .conv left right :: rest => some { state with stack := rest, heap := state.heap ++ [.conv left right] }
      | _ => none
  | .save =>
      match state.stack with
      | .goal _ _ :: _ => none
      | elem :: _ => some { state with heap := state.heap ++ [elem] }
      | [] => none

def run (tables : Tables) (mode : Mode) : State → List ProofCmd → Option State
  | state, [] => some state
  | state, cmd :: cmds => do
      let state ← step tables mode state cmd
      run tables mode state cmds

/-! ## Statements -/

/-- Load a statement's arguments as variables on the heap. A bound argument
takes the next rank and must not have a strict sort; a regular argument may
depend only on earlier bound arguments. -/
def loadArgs (sorts : List SortInfo) (args : List ExprType) : Option State :=
  args.zipIdx.foldlM (fun state (type, position) => do
    let info ← sorts[type.sort]?
    if type.bound then
      if info.strict = false ∧ type.deps = {state.nextBound} then
        let (state, e) := state.alloc ⟨.var position, type⟩
        some { state with
          heap := state.heap ++ [.expr e], nextBound := state.nextBound + 1
          varCount := state.varCount + 1 }
      else none
    else if type.deps ⊆ Finset.range state.nextBound then
        let (state, e) := state.alloc ⟨.var position, type⟩
        some { state with heap := state.heap ++ [.expr e], varCount := state.varCount + 1 }
      else none) ⟨[], [], [], [], 0, 0⟩

/-- Check an axiom or theorem: its proof stream leaves exactly the statement
(an expression for an axiom, a proof for a theorem) of a provable sort, and
the statement's unify stream matches it and the recorded hypotheses. -/
def checkAssertion (tables : Tables) (entry : ThmEntry) (proof : List ProofCmd)
    (isAxiom : Bool) : Bool :=
  match (loadArgs tables.sorts entry.args).bind (fun state => run tables .assertion state proof) with
  | some state =>
      let conclusion : Option Nat := match state.stack, isAxiom with
        | [.expr e], true => some e
        | [.proof e], false => some e
        | _, _ => none
      match conclusion with
      | some e =>
          (((state.typeOf e).bind (fun type => tables.sorts[type.sort]?)).map (·.provable)).getD false &&
            (unifyRun state.store .statement
              ⟨[e], (List.range entry.args.length).map (·, false), [], state.hyps⟩ entry.unify).isSome
      | none => false
  | none => false

/-- Check a term or definition: its arguments and return type are loaded as
binders; a definition's proof stream builds its value, whose type fits the
return type without unaccounted dependencies, and whose unify stream matches
it. A plain term has no proof stream. -/
def checkTermDecl (tables : Tables) (entry : TermEntry) (proof : List ProofCmd) : Bool :=
  match tables.sorts[entry.sort]? with
  | none => false
  | some info =>
      !info.pure && entry.ret.sort == entry.sort && entry.ret.bound = false &&
      match loadArgs tables.sorts (entry.args ++ [entry.ret]) with
      | none => false
      | some loaded =>
          let state := { loaded with heap := loaded.heap.dropLast }
          match entry.value with
          | none => proof.isEmpty
          | some value =>
              match run tables .definition state proof with
              | some { stack := [.expr e], store, .. } =>
                  match (store[e]?).map (·.type) with
                  | some type =>
                      type.fits entry.ret && decide (type.deps ⊆ entry.ret.deps) &&
                        (unifyRun store .definition
                          ⟨[e], (List.range entry.args.length).map (·, false), [], []⟩ value).isSome
                  | none => false
              | _ => false

/-! ## Files -/

inductive StatementKind where
  | sort
  | term
  | axiomDecl
  | theoremDecl
  deriving DecidableEq

/-- A statement of the proof stream with its proof commands. Local and public
statements are verified alike; whether a statement must match the
specification is decided elsewhere. -/
structure Statement where
  kind : StatementKind
  proof : List ProofCmd

/-- Verify the statements in order against the tables. Each statement sees only
the sorts, terms and theorems declared before it, and the file must declare
every table entry. -/
def verifyFrom (tables : Tables) (sorts terms thms : Nat) : List Statement → Bool
  | [] => sorts == tables.sorts.length && terms == tables.terms.length &&
      thms == tables.thms.length
  | statement :: rest =>
      let declared : Tables := ⟨tables.sorts.take sorts, tables.terms.take terms, tables.thms.take thms⟩
      match statement.kind with
      | .sort => decide (sorts < tables.sorts.length) && statement.proof.isEmpty &&
          verifyFrom tables (sorts + 1) terms thms rest
      | .term =>
          match tables.terms[terms]? with
          | some entry => checkTermDecl declared entry statement.proof &&
              verifyFrom tables sorts (terms + 1) thms rest
          | none => false
      | .axiomDecl | .theoremDecl =>
          match tables.thms[thms]? with
          | some entry =>
              checkAssertion declared entry statement.proof (statement.kind == .axiomDecl) &&
                verifyFrom tables sorts terms (thms + 1) rest
          | none => false

def verify (tables : Tables) (statements : List Statement) : Bool :=
  verifyFrom tables 0 0 0 statements

end Mettapedia.Languages.MM0.Formats.MMB
