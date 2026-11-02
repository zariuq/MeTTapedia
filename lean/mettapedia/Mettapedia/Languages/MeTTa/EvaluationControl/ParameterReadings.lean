/-!
# Declared parameter types: which arguments are held, which run, and what a check sees

A small language for one question: when a function declares the type of a parameter, does the
parameter receive its argument as written, or the argument's value, and what does the declared
type check?

**The language.** Symbols, numbers, strings, variables and expressions (`Tm`). A space of rows
holds the equations `(= (f p1 .. pn) body)` of every function, and other rows of data. The space
is live: `(add-atom &self row)` adds a row during a run, and a call selects from the rows that are
in the space when it is made. Rewriting is nondeterministic: every row of a function whose head
unifies with the call gives answers, and `(superpose (a1 .. an))` answers each `ai`. The answers
of a request form a bag, kept here as a list in a fixed order (`answers`).

**Variables are logic variables, and every binder unifies two ways** (`unifyM`). Each branch of a
run keeps the bindings of its variables (`Store.binds`). A call unifies the parameters of each
row's head with its arguments, `(let pattern source body)` unifies the pattern with the source's
value, and `(match &self pattern template)` unifies the pattern with each row. A row's variables
are renamed apart at each use (`rename`); the variables of the request are shared by the whole
branch, so a call can bind the caller's variables. A pending argument met by a pattern that is not
a variable runs first, by need, and its value is checked then; a variable binds the argument
without running it. Unification goes by fuel, as the evaluator does: running out is `exhausted`,
never a failed unification. One-way matching is unification against a target without variables
(`ParameterReadingsMatching`).

**Declared parameter types** (`Ty`, `Decl`). A `Reading` says which parameters hold their
argument (`Reading.holds`) and how a running argument is demanded. A running argument becomes a
need cell (`Cell.pending`): it runs when a use first needs it, its value is checked against the
declared type then (`forceWith`), and with sharing every later use sees that one value, so a
choice inside the argument is made once per call. A held argument is checked as code at the call
and passed on in the data role (`Tm.held`). Values that a `let` binds or a `match` reads are in
the value role (`Tm.val`); when a value runs again is the reading's `Rerun`.

**Checks never bind.** A check is a function of the term it judges, with the branch's bindings
applied: it returns a verdict and adds no binding. An unbound variable is a value of unknown type
and passes every check.

**The one-marker rule** (`oneMarker`): only `Atom` and `(Data T)` hold; every other declared
type, and an undeclared parameter, runs. The check of a running parameter is applied to the value
the argument computes (`valueCheck`).

**Weakening a check changes only type errors** (`eval_refines`, `answers_refines`). If two
checks differ only in that the second accepts more, the runs under the two agree answer for
answer, except that an answer the first refuses with `badArg` may be replaced in the second run by
any list of answers (`Refines`). This holds for every reading: by need, shared or not, eager or
not, under every `Rerun`, as long as the reading itself does not depend on the check. Unification
consults no check, which is what keeps the law. Within one line of the one-marker rule, replacing
declared types by weaker ones changes only the check, so the guarantee holds
(`weakening_within_line`). A reading whose demand depends on the declared type, for example one
that runs a checked argument at the call, falls outside it; the companion module
`ParameterReadingsLaws` gives the programs where such readings change answers.

Not modelled: result types (a body always runs; a body that is held data returns it as data),
`collapse`, effects other than `add-atom`, declarations that change during a run, a call whose
rows all fail to unify (it has no answer here, as in PeTTa), and the consistency of a type variable
across parameters (a lone type variable accepts every value). `let` introduces no variables: its
pattern's variables are those of the row or request it is written in, so nested binders need
distinct names. A row added by `add-atom` is stored as written with its data and value roles
dropped; a need cell inside it is not forced (the examples add only closed rows).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EvaluationControl.ParameterReadings

/-! ## Terms, types, stores -/

/-- Terms. Programs write symbols, numbers, strings, variables and expressions. The other three
forms arise during a run: `held t` is syntax `t` that a parameter received as written, `val t` is
a value `t` that a `let` bound or a `match` read from a space, and `cell i` refers to the need
cell of an argument that has not run yet. -/
inductive Tm where
  | sym (name : String)
  | num (value : Int)
  | str (text : String)
  | var (name : String)
  | expr (items : List Tm)
  | held (payload : Tm)
  | val (payload : Tm)
  | cell (index : Nat)

/-- Boolean equality of terms, by structural recursion, so that the kernel evaluates it. -/
def Tm.beq : Tm → Tm → Bool
  | .sym x, .sym y => x == y
  | .num x, .num y => x == y
  | .str x, .str y => x == y
  | .var x, .var y => x == y
  | .expr xs, .expr ys => beqList xs ys
  | .held x, .held y => Tm.beq x y
  | .val x, .val y => Tm.beq x y
  | .cell i, .cell j => i == j
  | _, _ => false
where
  beqList : List Tm → List Tm → Bool
    | [], [] => true
    | x :: xs, y :: ys => Tm.beq x y && beqList xs ys
    | _, _ => false

theorem Tm.beqList_self (xs : List Tm) (ih : ∀ x ∈ xs, Tm.beq x x = true) :
    Tm.beq.beqList xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ihl =>
      simp only [Tm.beq.beqList, Bool.and_eq_true]
      exact ⟨ih x List.mem_cons_self, ihl fun y m => ih y (List.mem_cons_of_mem _ m)⟩

theorem Tm.beq_self : (a : Tm) → Tm.beq a a = true
  | .sym _ => by simp [Tm.beq]
  | .num _ => by simp [Tm.beq]
  | .str _ => by simp [Tm.beq]
  | .var _ => by simp [Tm.beq]
  | .expr xs => by
      simp only [Tm.beq]
      exact Tm.beqList_self xs fun x _ => Tm.beq_self x
  | .held x => by simp only [Tm.beq]; exact Tm.beq_self x
  | .val x => by simp only [Tm.beq]; exact Tm.beq_self x
  | .cell _ => by simp [Tm.beq]
termination_by a => sizeOf a

theorem Tm.eqList_of_beq (xs ys : List Tm) (h : Tm.beq.beqList xs ys = true)
    (ih : ∀ x ∈ xs, ∀ y, Tm.beq x y = true → x = y) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons => simp [Tm.beq.beqList] at h
  | cons x xs ihl =>
      cases ys with
      | nil => simp [Tm.beq.beqList] at h
      | cons y ys =>
          simp only [Tm.beq.beqList, Bool.and_eq_true] at h
          rw [ih x List.mem_cons_self y h.1,
            ihl ys h.2 fun z m => ih z (List.mem_cons_of_mem _ m)]

theorem Tm.eq_of_beq (a b : Tm) (h : Tm.beq a b = true) : a = b := by
  cases a <;> cases b <;> simp only [Tm.beq, beq_iff_eq, Bool.false_eq_true] at h
  all_goals first
    | (subst h; rfl)
    | exact congrArg Tm.held (Tm.eq_of_beq _ _ h)
    | exact congrArg Tm.val (Tm.eq_of_beq _ _ h)
    | exact congrArg Tm.expr (Tm.eqList_of_beq _ _ h fun x _ y hy => Tm.eq_of_beq x y hy)
termination_by sizeOf a

instance : DecidableEq Tm := fun a b =>
  if h : Tm.beq a b = true then isTrue (Tm.eq_of_beq a b h)
  else isFalse fun e => h (e ▸ Tm.beq_self a)

/-- Declared parameter types. `atom` is `Atom`, `data T` is `(Data T)`, `proc` is `Proc`,
`undeclared` is a parameter without a declaration (`%Undefined%`), `tvar t` is a type variable
`$t`; the others are the types of numbers, symbols, expressions and strings. -/
inductive Ty where
  | atom
  | proc
  | undeclared
  | number
  | symbol
  | expression
  | string
  | data (inner : Ty)
  | tvar (name : String)
  deriving DecidableEq

/-- A declaration `(: f (-> T1 .. Tn R))`. -/
structure Decl where
  name : String
  params : List Ty
  result : Ty
  deriving DecidableEq

/-- A parameter position: a function and the index of one of its parameters. -/
abbrev Site := String × Nat

/-- The declared types of a program: the type of each parameter (`undeclared` where nothing is
declared) and the result type of each declared function. -/
structure Decls where
  param : Site → Ty
  result : String → Option Ty

/-- The declared types of a list of declarations. -/
def Decls.ofList (ds : List Decl) : Decls where
  param site :=
    match ds.find? (fun d => d.name == site.1) with
    | some d => d.params.getD site.2 .undeclared
    | none => .undeclared
  result name := (ds.find? (fun d => d.name == name)).map (·.result)

/-- Declare the parameter at `site` with type `T` instead. -/
def Decls.set (D : Decls) (site : Site) (T : Ty) : Decls :=
  { D with param := fun s => if s = site then T else D.param s }

/-- A need cell: an argument waiting to run, with the parameter it was passed to, or the value it
computed. -/
inductive Cell where
  | pending (code : Tm) (site : Site)
  | done (value : Tm)
  deriving DecidableEq

/-- The state of one branch of a run: the rows of the space, the need cells, the bindings of the
branch's logic variables (each to a term in which no bound variable occurs), and the number of row
uses so far, which names the variables of the next use apart. -/
structure Store where
  space : List Tm
  cells : List Cell
  binds : List (String × Tm)
  fresh : Nat
  deriving DecidableEq

/-- The store of a request on a space: no cells, no bindings, no row used yet. -/
def Store.init (space : List Tm) : Store := ⟨space, [], [], 0⟩

/-- One outcome of a branch: a result with the branch's store; a parameter's check refusing a
value or a piece of code (`badArg`, the type error that weakening may remove); another fault; or
the end of the fuel. -/
inductive Out (α : Type) where
  | ok (value : α) (store : Store)
  | badArg (site : Site) (value : Tm)
  | fault (reason : String)
  | exhausted
  deriving DecidableEq

/-- A computation: from a store, the outcomes of all its branches, in order. -/
def M (α : Type) : Type := Store → List (Out α)

/-- Continue a successful outcome; pass every other outcome on. -/
def Out.next {α β : Type} (k : α → Store → List (Out β)) : Out α → List (Out β)
  | .ok a s => k a s
  | .badArg site v => [.badArg site v]
  | .fault r => [.fault r]
  | .exhausted => [.exhausted]

def M.pure {α : Type} (a : α) : M α := fun s => [.ok a s]

def M.bind {α β : Type} (m : M α) (k : α → M β) : M β := fun s => (m s).flatMap (Out.next k)

/-- Run computations on a list left to right, threading the store. -/
def seqM {α β : Type} (f : α → M β) : List α → M (List β)
  | [] => M.pure []
  | x :: xs => M.bind (f x) fun y => M.bind (seqM f xs) fun ys => M.pure (y :: ys)

/-! ## Syntax helpers -/

/-- A term with the data and value roles removed. -/
def payload : Tm → Tm
  | .held t => payload t
  | .val t => payload t
  | t => t

/-- Hold `t` as written; a term already in a data or value role keeps it. -/
def asHeld : Tm → Tm
  | .held t => .held t
  | .val t => .val t
  | t => .held t

/-- Mark `t` as a value; a term already in a data or value role keeps it. -/
def asVal : Tm → Tm
  | .held t => .held t
  | .val t => .val t
  | t => .val t

def lookupVar (σ : List (String × Tm)) (x : String) : Option Tm :=
  (σ.find? (fun p => p.1 == x)).map (·.2)

mutual
/-- Apply bindings: each bound variable is replaced by its term, inside held syntax and values
too. Cells are references and stay as they are. -/
def inst (θ : List (String × Tm)) : Tm → Tm
  | .var x => (lookupVar θ x).getD (.var x)
  | .expr items => .expr (instList θ items)
  | .held t => .held (inst θ t)
  | .val t => .val (inst θ t)
  | t => t

def instList (θ : List (String × Tm)) : List Tm → List Tm
  | [] => []
  | t :: ts => inst θ t :: instList θ ts
end

mutual
/-- Whether the variable `x` occurs in a term. -/
def occurs (x : String) : Tm → Bool
  | .var y => x == y
  | .expr items => occursList x items
  | .held t => occurs x t
  | .val t => occurs x t
  | _ => false

def occursList (x : String) : List Tm → Bool
  | [] => false
  | t :: ts => occurs x t || occursList x ts
end

/-- The name of the variable `x` in the `k`-th use of a row. Names written in programs contain no
`#`. -/
def freshName (x : String) (k : Nat) : String := x ++ "#" ++ toString k

mutual
/-- Rename every variable of a row for its `k`-th use. -/
def rename (k : Nat) : Tm → Tm
  | .var x => .var (freshName x k)
  | .expr items => .expr (renameList k items)
  | .held t => .held (rename k t)
  | .val t => .val (rename k t)
  | t => t

def renameList (k : Nat) : List Tm → List Tm
  | [] => []
  | t :: ts => rename k t :: renameList k ts
end

mutual
/-- **One-way matching** of a pattern against a term: only the pattern's variables are bound, and
the term's variables are constants; a repeated variable must match equal terms. -/
def matchTm : Tm → Tm → List (String × Tm) → Option (List (String × Tm))
  | .var x, t, σ =>
      match lookupVar σ x with
      | some u => if u == t then some σ else none
      | none => some ((x, t) :: σ)
  | .expr ps, .expr ts, σ => matchList ps ts σ
  | p, t, σ => if p == t then some σ else none

def matchList : List Tm → List Tm → List (String × Tm) → Option (List (String × Tm))
  | [], [], σ => some σ
  | p :: ps, t :: ts, σ =>
      match matchTm p t σ with
      | some σ' => matchList ps ts σ'
      | none => none
  | _, _, _ => none
end

/-- The equations of `f` with `arity` parameters live in `space`, in row order:
`(= (f p1 .. pn) body)` gives `([p1, .., pn], body)`. -/
def rowsOf (space : List Tm) (f : String) (arity : Nat) : List (List Tm × Tm) :=
  space.filterMap fun row =>
    match row with
    | .expr [.sym "=", .expr (.sym g :: params), body] =>
        if g == f && params.length == arity then some (params, body) else none
    | _ => none

/-- An equation renamed for its `k`-th use. -/
def renameRow (k : Nat) (row : List Tm × Tm) : List Tm × Tm :=
  (renameList k row.1, rename k row.2)

/-- The rows `(= s body)` that rewrite the bare symbol `s`. -/
def symbolRows (space : List Tm) (s : String) : List Tm :=
  space.filterMap fun row =>
    match row with
    | .expr [.sym "=", .sym g, body] => if g == s then some body else none
    | _ => none

/-! ## Unification -/

/-- The role a part of a term is in: plain code, held syntax, or a value. -/
inductive Role where
  | plain
  | held
  | val
  deriving DecidableEq

/-- Put a term in a role; a term already in a data or value role keeps it. -/
def Role.wrap : Role → Tm → Tm
  | .plain, t => t
  | .held, t => asHeld t
  | .val, t => asVal t

/-- Bind the variable `x` to `u`. The bindings already made are updated, so that no bound
variable occurs in a bound term. -/
def Store.bindVar (s : Store) (x : String) (u : Tm) : Store :=
  { s with binds := (x, u) :: s.binds.map fun p => (p.1, inst [(x, u)] p.2) }

/-- What unification does next with two terms. -/
inductive UStep where
  /-- The two terms are unified. -/
  | done
  /-- No binding unifies them. -/
  | fail
  /-- Unify these two instead. -/
  | again (ra : Role) (a : Tm) (rb : Role) (b : Tm)
  /-- Bind the unbound variable `x` to `t`, in role `r`. -/
  | bind (x : String) (r : Role) (t : Tm)
  /-- Run the pending cell `i` on the left, then unify its value with `b`. -/
  | forceLeft (i : Nat) (ra : Role) (rb : Role) (b : Tm)
  /-- Run the pending cell `j` on the right, then unify `a` with its value. -/
  | forceRight (ra : Role) (a : Tm) (j : Nat) (rb : Role)
  /-- Unify the pairs of items, in order. -/
  | items (ra : Role) (rb : Role) (pairs : List (Tm × Tm))

/-- **One step of unification** of `a` (in role `ra`) with `b` (in role `rb`), decided by their
outer forms and the bindings `θ`. A role marker is entered; a bound variable is replaced by its
term; an unbound variable is bound to the other side, cell or not, without running it; a cell met
by anything but a variable or the same cell is run; expressions of one length are unified item by
item; atoms unify when equal. -/
def ustep (θ : List (String × Tm)) (ra : Role) (a : Tm) (rb : Role) (b : Tm) : UStep :=
  match a, b with
  | .held a', _ => .again .held a' rb b
  | .val a', _ => .again .val a' rb b
  | _, .held b' => .again ra a .held b'
  | _, .val b' => .again ra a .val b'
  | .var x, _ =>
      match lookupVar θ x with
      | some u => .again ra u rb b
      | none =>
          match b with
          | .var y =>
              if x = y then .done
              else
                match lookupVar θ y with
                | some w => .again ra a rb w
                | none => .bind x rb b
          | _ => .bind x rb b
  | _, .var y =>
      match lookupVar θ y with
      | some w => .again ra a rb w
      | none => .bind y ra a
  | .cell i, .cell j => if i = j then .done else .forceLeft i ra rb b
  | .cell i, _ => .forceLeft i ra rb b
  | _, .cell j => .forceRight ra a j rb
  | .expr xs, .expr ys => if xs.length = ys.length then .items ra rb (xs.zip ys) else .fail
  | p, q => if p = q then .done else .fail

/-- Bind the unbound variable `x` to `t` in role `r`, with the bindings applied to `t`; when `x`
occurs in it, nothing unifies. -/
def bindTo (x : String) (r : Role) (t : Tm) : M Unit := fun st =>
  if occurs x (inst st.binds t) then [] else [.ok () (st.bindVar x (r.wrap (inst st.binds t)))]

/-- Unify the pairs of a list in order, threading the bindings. -/
def unifyPairs (u : Tm → Tm → M Unit) : List (Tm × Tm) → M Unit
  | [] => M.pure ()
  | (a, b) :: rest => M.bind (u a b) fun _ => unifyPairs u rest

/-- Carry out one step of unification, with `force` running a cell and `rec` unifying further. -/
def runUStep (force : Nat → M Tm) (rec : Role → Tm → Role → Tm → M Unit) : UStep → M Unit
  | .done => M.pure ()
  | .fail => fun _ => []
  | .again ra a rb b => rec ra a rb b
  | .bind x r t => bindTo x r t
  | .forceLeft i ra rb b => M.bind (force i) fun v => rec ra v rb b
  | .forceRight ra a j rb => M.bind (force j) fun v => rec ra a rb v
  | .items ra rb pairs => unifyPairs (fun x y => rec ra x rb y) pairs

/-- **Two-way unification**, by fuel. Its outcomes: one success with the bindings extended, no
outcome when nothing unifies, `exhausted` when the fuel ends, and whatever running a cell gives. -/
def unifyM (force : Nat → M Tm) : Nat → Role → Tm → Role → Tm → M Unit
  | 0, _, _, _, _ => fun _ => [.exhausted]
  | n + 1, ra, a, rb, b => fun st =>
      runUStep force (unifyM force n) (ustep st.binds ra a rb b) st

/-! ## Readings -/

/-- When a value runs again. -/
inductive Rerun where
  /-- Values stay values: a `let` binds and a `match` reads in the value role, held syntax keeps
  its data role wherever it is passed, and only `eval` runs data. -/
  | stay
  /-- As `stay`, except that syntax held by a parameter runs when it is passed to a running
  parameter. -/
  | forward
  /-- Nothing is marked: a value bound by `let` or read by `match` is bound as plain code, and
  runs again wherever it lands in a running position; held syntax runs when passed to a running
  parameter. -/
  | substitute
  deriving DecidableEq

/-- How a dialect or candidate reads declared parameters. -/
structure Reading where
  /-- Whether the parameter at a site receives its argument as written (the written argument is
  given, for rules that look at it). -/
  holds : Site → Tm → Bool
  /-- Whether a running argument runs when the call is made rather than when first needed. -/
  eagerAt : Site → Bool := fun _ => false
  /-- Whether the check of a running argument runs its own copy of the argument at the call; the
  body then runs the argument again when it needs it. -/
  copyAt : Site → Bool := fun _ => false
  /-- Whether a cell keeps the value it computed, so every use sees one choice. -/
  shares : Bool := true
  /-- When a value runs again. -/
  rerun : Rerun := .stay
  /-- Whether a bare symbol is rewritten by rows `(= s body)`. -/
  symbolsRewrite : Bool := false

/-- The code a running parameter's cell runs: held syntax runs as code unless values stay. -/
def Reading.cellCode (R : Reading) (a : Tm) : Tm :=
  match R.rerun, a with
  | .stay, _ => a
  | _, .held t => t
  | _, _ => a

/-- The role in which `let` binds a value and `match` reads a row. -/
def Reading.bindRole (R : Reading) : Role :=
  match R.rerun with
  | .substitute => .plain
  | _ => .val

/-- **The verdicts of declared types.** `onValue` judges the value a running argument computes,
when it is computed, and the code a held parameter receives, at the call. `onCode` judges the
written argument of a running parameter at the call, before it runs: a static check. A verdict
is a truth value; it binds nothing. -/
structure Verdicts where
  onValue : Site → Tm → Bool
  onCode : Site → Tm → Bool

/-- `c'` accepts everything `c` accepts. -/
structure Verdicts.Le (c c' : Verdicts) : Prop where
  onValue : ∀ site t, c.onValue site t = true → c'.onValue site t = true
  onCode : ∀ site t, c.onCode site t = true → c'.onCode site t = true

/-! ## The evaluator -/

/-- Replace cell `i`. -/
def Store.setCell (s : Store) (i : Nat) (c : Cell) : Store := { s with cells := s.cells.set i c }

/-- **Force a cell.** A pending cell runs its code; each value it computes, with the branch's
bindings applied, is checked against the parameter's declared type. A value the check accepts is
the cell's value, kept for later uses when the reading shares; a value it refuses is a
`badArg`. -/
def forceWith (R : Reading) (check : Verdicts) (run : Tm → M Tm) (i : Nat) : M Tm :=
  fun s =>
    match s.cells[i]? with
    | some (.done v) => [.ok v s]
    | some (.pending code site) =>
        (run code s).flatMap (Out.next fun v s' =>
          if check.onValue site (inst s'.binds v) then
            [.ok v (if R.shares then s'.setCell i (.done v) else s')]
          else [.badArg site (inst s'.binds v)])
    | none => [.fault "no such cell"]

/-- What happens at the call to a running argument placed in cell `i`: run it now (eager), run
and check a copy of it (unshared check), or nothing (by need). -/
def prepare (R : Reading) (check : Verdicts) (run : Tm → M Tm) (site : Site)
    (code : Tm) (i : Nat) : M Unit :=
  if R.eagerAt site then M.bind (forceWith R check run i) fun _ => M.pure ()
  else if R.copyAt site then
    M.bind (run code) fun v s =>
      if check.onValue site (inst s.binds v) then [.ok () s] else [.badArg site (inst s.binds v)]
  else M.pure ()

/-- **Pass one argument.** A held parameter checks the code as written and receives it in the
data role. A running parameter checks the written argument statically, then receives a new cell
holding the argument. -/
def bindOne (R : Reading) (check : Verdicts) (run : Tm → M Tm) (site : Site)
    (a : Tm) : M Tm :=
  if R.holds site a then
    fun s => if check.onValue site a then [.ok (asHeld a) s] else [.badArg site a]
  else
    fun s =>
      if check.onCode site a then
        M.bind (prepare R check run site (R.cellCode a) s.cells.length)
          (fun _ => M.pure (.cell s.cells.length))
          { s with cells := s.cells ++ [.pending (R.cellCode a) site] }
      else [.badArg site a]

/-- Pass the arguments of a call of `f`, from parameter `i` on. -/
def bindArgs (R : Reading) (check : Verdicts) (run : Tm → M Tm) (f : String) :
    Nat → List Tm → M (List Tm)
  | _, [] => M.pure []
  | i, a :: rest =>
      M.bind (bindOne R check run (f, i) a) fun t =>
        M.bind (bindArgs R check run f (i + 1) rest) fun ts => M.pure (t :: ts)

/-- Give the next use of a row its number. -/
def withFresh {α : Type} (k : Nat → M α) : M α := fun s => k s.fresh { s with fresh := s.fresh + 1 }

/-- **Run one equation** `(params, body)` of `f` on the arguments of a call: pass the arguments,
unify the head's parameters with what they received, then run the body. -/
def callRow (R : Reading) (check : Verdicts) (run : Tm → M Tm) (n : Nat) (f : String)
    (args : List Tm) (row : List Tm × Tm) : M Tm :=
  M.bind (bindArgs R check run f 0 args) fun received =>
    M.bind (unifyPairs (fun p a => unifyM (forceWith R check run) n .plain p .plain a)
      (row.1.zip received)) fun _ => run row.2

/-- The forms the evaluator tells apart. -/
inductive Form where
  | value (t : Tm)
  | force (index : Nat)
  | name (s : String)
  | superpose (alternatives : List Tm)
  | letIn (pattern source body : Tm)
  | matchSelf (pattern template : Tm)
  | addSelf (row : Tm)
  | evalCode (code : Tm)
  | plus (left right : Tm)
  | applyCell (index : Nat) (args : List Tm)
  | callOrBuild (f : String) (args : List Tm)
  | build (items : List Tm)

def classify : Tm → Form
  | .cell i => .force i
  | .sym s => .name s
  | .expr [.sym "superpose", .expr alternatives] => .superpose alternatives
  | .expr [.sym "let", pattern, source, body] => .letIn pattern source body
  | .expr [.sym "match", .sym "&self", pattern, template] => .matchSelf pattern template
  | .expr [.sym "add-atom", .sym "&self", row] => .addSelf row
  | .expr [.sym "eval", code] => .evalCode code
  | .expr [.sym "+", left, right] => .plus left right
  | .expr (.cell i :: args) => .applyCell i args
  | .expr (.sym f :: args) => .callOrBuild f args
  | .expr items => .build items
  | t => .value t

/-- The sites of the built-in `+`, whose two parameters are numbers. -/
def plusSite (i : Nat) : Site := ("+", i)

/-- Add two checked values. -/
def addValues (u v : Tm) : M Tm := fun s =>
  match payload (inst s.binds u), payload (inst s.binds v) with
  | .num a, .num b => [.ok (.num (a + b)) s]
  | _, _ => [.fault "+ needs numbers"]

/-- Run a built-in argument at once and check it. -/
def strictArg (check : Verdicts) (run : Tm → M Tm) (site : Site) (a : Tm) : M Tm :=
  M.bind (run a) fun v s =>
    if check.onValue site (inst s.binds v) then [.ok v s] else [.badArg site (inst s.binds v)]

/-- Rows of a space are plain syntax: data and value roles are dropped when a row is stored. -/
def plain : Tm → Tm
  | .held t => plain t
  | .val t => plain t
  | .expr items => .expr (plainList items)
  | t => t
where
  plainList : List Tm → List Tm
    | [] => []
    | t :: ts => plain t :: plainList ts

/-- **One level of evaluation of a form**, with `run` evaluating the parts and `n` the fuel of
unification. -/
def stepForm (R : Reading) (check : Verdicts) (run : Tm → M Tm) (n : Nat) : Form → M Tm
  | .value t => M.pure t
  | .force i => forceWith R check run i
  | .name s => fun st =>
      if R.symbolsRewrite && !(symbolRows st.space s).isEmpty then
        (symbolRows st.space s).flatMap fun body => run body st
      else [.ok (.sym s) st]
  | .superpose alternatives => fun st => alternatives.flatMap fun a => run a st
  | .letIn pattern source body =>
      M.bind (run source) fun v =>
        M.bind (unifyM (forceWith R check run) n .plain pattern R.bindRole v) fun _ => run body
  | .matchSelf pattern template => fun st =>
      st.space.flatMap fun row =>
        withFresh (fun k =>
          M.bind (unifyM (forceWith R check run) n .plain pattern R.bindRole (rename k row))
            fun _ => run template) st
  | .addSelf row => fun st => [.ok (.sym "True") { st with space := st.space ++ [plain row] }]
  | .evalCode code => M.bind (run code) fun v => run (payload v)
  | .plus left right =>
      M.bind (strictArg check run (plusSite 0) left) fun u =>
        M.bind (strictArg check run (plusSite 1) right) fun v => addValues u v
  | .applyCell i args => M.bind (forceWith R check run i) fun h => run (.expr (payload h :: args))
  | .callOrBuild f args => fun st =>
      if (rowsOf st.space f args.length).isEmpty then
        M.bind (seqM run (.sym f :: args)) (fun vs => M.pure (.expr vs)) st
      else (rowsOf st.space f args.length).flatMap fun row =>
        withFresh (fun k => callRow R check run n f args (renameRow k row)) st
  | .build items => M.bind (seqM run items) fun vs => M.pure (.expr vs)

/-- **One level of evaluation**: the term, with the branch's bindings applied, is classified and
evaluated. -/
def step (R : Reading) (check : Verdicts) (run : Tm → M Tm) (n : Nat) (t : Tm) : M Tm :=
  fun st => stepForm R check run n (classify (inst st.binds t)) st

/-- **The evaluator**, by fuel. -/
def eval (R : Reading) (check : Verdicts) : Nat → Tm → M Tm
  | 0, _ => fun _ => [.exhausted]
  | n + 1, t => step R check (eval R check n) n t

/-- One level of reading out an answer: the observer applies the bindings, needs every cell in
the answer, and sees held syntax and values as plain terms. -/
def readStep (forceAt : Nat → M Tm) (rec : Tm → M Tm) (t : Tm) : M Tm := fun st =>
  match inst st.binds t with
  | .cell i => M.bind (forceAt i) rec st
  | .held p => rec p st
  | .val p => rec p st
  | .expr items => M.bind (seqM rec items) (fun vs => M.pure (.expr vs)) st
  | t' => [.ok t' st]

/-- Read out an answer, by fuel. -/
def deep (R : Reading) (check : Verdicts) : Nat → Tm → M Tm
  | 0, _ => fun _ => [.exhausted]
  | n + 1, t => readStep (forceWith R check (eval R check n)) (deep R check n) t

/-- What a request shows: an answer, a refused argument, another fault, or the end of the fuel. -/
inductive Obs where
  | value (t : Tm)
  | badArg (site : Site) (value : Tm)
  | fault (reason : String)
  | exhausted
  deriving DecidableEq

def Out.obs : Out Tm → Obs
  | .ok v _ => .value v
  | .badArg site v => .badArg site (plain v)
  | .fault r => .fault r
  | .exhausted => .exhausted

/-- The outcomes of a request on a store: run it, then read out each answer. -/
def outcomes (R : Reading) (check : Verdicts) (fuel : Nat) (t : Tm) : M Tm :=
  M.bind (eval R check fuel t) (deep R check fuel)

/-- **The answers of a request** on a space, as a bag kept in order. -/
def answers (R : Reading) (check : Verdicts) (fuel : Nat) (space : List Tm) (t : Tm) :
    List Obs :=
  (outcomes R check fuel t (Store.init space)).map Out.obs

/-! ## The one-marker rule -/

/-- **Which declared types hold**: only `Atom` and `(Data T)`. -/
def holdsTy : Ty → Bool
  | .atom => true
  | .data _ => true
  | _ => false

/-- The type a piece of code computes, as far as declarations tell; `none` when they do not. -/
def inferCode (D : Decls) : Tm → Option Ty
  | .num _ => some .number
  | .str _ => some .string
  | .expr (.sym "+" :: _) => some .number
  | .expr (.sym f :: _) => D.result f
  | _ => none

/-- Whether a value has a type, for the types that constrain values. An unbound variable is a
value of unknown type: it has every type, and the check binds nothing. -/
def valueHas (t : Tm) : Ty → Bool
  | .number => match payload t with | .num _ | .var _ => true | _ => false
  | .symbol => match payload t with | .sym _ | .var _ => true | _ => false
  | .expression => match payload t with | .expr _ | .var _ => true | _ => false
  | .string => match payload t with | .str _ | .var _ => true | _ => false
  | _ => true

/-- `(Data T)` checks the code it holds: code whose type the declarations tell must have type
`T` (or `T` must accept every value); code they say nothing about passes, as in gradual typing. -/
def codeHas (D : Decls) (inner : Ty) (code : Tm) : Bool :=
  match inferCode D code with
  | none => true
  | some ty => ty == inner || inner == .atom || inner == .proc || inner == .undeclared

/-- **The check of a declared type** `T`: a holding type checks the code it receives, a running
type checks the value the argument computes. `Atom`, `Proc`, an undeclared parameter and a type
variable accept everything. -/
def verdictTy (D : Decls) (T : Ty) (t : Tm) : Bool :=
  match T with
  | .data inner => codeHas D inner t
  | ty => valueHas t ty

/-- **The static check of a running parameter** of type `T`: a number or string literal is its own
and only value, so a literal the declared type refuses is refused at the call. Every other
argument waits for its value. -/
def literalTy (T : Ty) (a : Tm) : Bool :=
  match a with
  | .num _ | .str _ => valueHas a T
  | _ => true

/-- The verdicts of the declared types `D`. -/
def valueCheck (D : Decls) : Verdicts :=
  ⟨fun site t => verdictTy D (D.param site) t, fun site a => literalTy (D.param site) a⟩

/-- **The one-marker rule**, by need with shared choice, values staying values. -/
def oneMarker (D : Decls) : Reading where
  holds site _ := holdsTy (D.param site)

/-! ## Refinement: the same answers up to removed type errors -/

/-- `Refines xs ys`: the outcomes `ys` are `xs` with each refused argument (`badArg`) replaced by
some list of outcomes, and every other outcome kept, in order. -/
inductive Refines {α : Type} : List (Out α) → List (Out α) → Prop where
  | nil : Refines [] []
  | keep (o : Out α) {xs ys : List (Out α)} : Refines xs ys → Refines (o :: xs) (o :: ys)
  | relax (site : Site) (v : Tm) (zs : List (Out α)) {xs ys : List (Out α)} :
      Refines xs ys → Refines (.badArg site v :: xs) (zs ++ ys)

namespace Refines

variable {α β : Type}

theorem refl : ∀ xs : List (Out α), Refines xs xs
  | [] => .nil
  | o :: xs => .keep o (refl xs)

theorem append {a b c d : List (Out α)} (h : Refines a b) (h' : Refines c d) :
    Refines (a ++ c) (b ++ d) := by
  induction h with
  | nil => exact h'
  | keep o _ ih => exact .keep o ih
  | relax site v zs _ ih =>
      rw [List.cons_append, List.append_assoc]
      exact .relax site v zs ih

/-- A refused argument may become anything. -/
theorem badArg_any (site : Site) (v : Tm) (zs : List (Out α)) :
    Refines [.badArg site v] zs := by
  have h := Refines.relax (α := α) site v zs Refines.nil
  rwa [List.append_nil] at h

theorem flatMap {l : List β} {f g : β → List (Out α)} (h : ∀ b ∈ l, Refines (f b) (g b)) :
    Refines (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => exact .nil
  | cons b l ih =>
      simp only [List.flatMap_cons]
      exact append (h b (by simp)) (ih fun b' m => h b' (by simp [m]))

/-- Continuing related outcomes with related continuations gives related outcomes. -/
theorem next {xs ys : List (Out α)} {k k' : α → Store → List (Out β)} (h : Refines xs ys)
    (hk : ∀ a s, Refines (k a s) (k' a s)) :
    Refines (xs.flatMap (Out.next k)) (ys.flatMap (Out.next k')) := by
  induction h with
  | nil => exact .nil
  | keep o _ ih =>
      simp only [List.flatMap_cons]
      refine append ?_ ih
      cases o with
      | ok a s => exact hk a s
      | badArg site v => exact refl _
      | fault r => exact refl _
      | exhausted => exact refl _
  | relax site v zs _ ih =>
      simp only [List.flatMap_cons, List.flatMap_append, Out.next]
      exact .relax site v _ ih

end Refines

/-- `m` refines to `m'` from every store. -/
def MRef {α : Type} (m m' : M α) : Prop := ∀ s, Refines (m s) (m' s)

namespace MRef

variable {α β : Type}

theorem refl (m : M α) : MRef m m := fun _ => Refines.refl _

theorem pure (a : α) : MRef (M.pure a) (M.pure a) := refl _

theorem bind {m m' : M α} {k k' : α → M β} (h : MRef m m') (hk : ∀ a, MRef (k a) (k' a)) :
    MRef (M.bind m k) (M.bind m' k') := fun s => Refines.next (h s) (fun a s' => hk a s')

theorem seqM {f f' : β → M α} (h : ∀ x, MRef (f x) (f' x)) :
    ∀ xs, MRef (ParameterReadings.seqM f xs) (ParameterReadings.seqM f' xs)
  | [] => pure _
  | x :: xs => bind (h x) fun _ => bind (seqM h xs) fun _ => pure _

theorem ite {c : Prop} [Decidable c] {a a' b b' : M α} (ha : c → MRef a a')
    (hb : ¬c → MRef b b') : MRef (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact ha hc
  · rw [if_neg hc, if_neg hc]; exact hb hc

end MRef

theorem Refines.ite {α : Type} {c : Prop} [Decidable c] {a a' b b' : List (Out α)}
    (ha : c → Refines a a') (hb : ¬c → Refines b b') :
    Refines (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact ha hc
  · rw [if_neg hc, if_neg hc]; exact hb hc

/-! ## Weakening a check -/

/-- A verdict and a weaker verdict on one value or one piece of code, with related
continuations. -/
theorem verdict_refines {α : Type} {f f' : Site → Tm → Bool}
    (le : ∀ site t, f site t = true → f' site t = true) (site : Site) (v : Tm)
    {yes yes' : List (Out α)} (h : Refines yes yes') :
    Refines (if f site v then yes else [.badArg site v])
      (if f' site v then yes' else [.badArg site v]) := by
  cases hv : f site v
  · exact Refines.badArg_any site v _
  · rw [le site v hv]
    exact h

theorem unifyPairs_refines {u u' : Tm → Tm → M Unit} (h : ∀ a b, MRef (u a b) (u' a b)) :
    ∀ l, MRef (unifyPairs u l) (unifyPairs u' l)
  | [] => MRef.pure _
  | (a, b) :: rest => MRef.bind (h a b) fun _ => unifyPairs_refines h rest

theorem runUStep_refines {force force' : Nat → M Tm} (hf : ∀ i, MRef (force i) (force' i))
    {rec rec' : Role → Tm → Role → Tm → M Unit}
    (hr : ∀ ra a rb b, MRef (rec ra a rb b) (rec' ra a rb b)) :
    ∀ u, MRef (runUStep force rec u) (runUStep force' rec' u)
  | .done => MRef.pure _
  | .fail => MRef.refl _
  | .again ra a rb b => hr ra a rb b
  | .bind _ _ _ => MRef.refl _
  | .forceLeft i ra rb b => MRef.bind (hf i) fun v => hr ra v rb b
  | .forceRight ra a j rb => MRef.bind (hf j) fun v => hr ra a rb v
  | .items ra rb pairs => unifyPairs_refines (fun x y => hr ra x rb y) pairs

/-- **Unification consults no check**: run with related ways of forcing cells, it gives related
outcomes. -/
theorem unifyM_refines {force force' : Nat → M Tm} (hf : ∀ i, MRef (force i) (force' i)) :
    ∀ n ra a rb b, MRef (unifyM force n ra a rb b) (unifyM force' n ra a rb b)
  | 0, _, _, _, _ => MRef.refl _
  | n + 1, ra, a, rb, b => fun st =>
      runUStep_refines hf (unifyM_refines hf n) (ustep st.binds ra a rb b) st

theorem withFresh_refines {α : Type} {k k' : Nat → M α} (h : ∀ i, MRef (k i) (k' i)) :
    MRef (withFresh k) (withFresh k') := fun _ => h _ _

section Weakening

variable (R : Reading) {check check' : Verdicts} (le : check.Le check')
  {run run' : Tm → M Tm} (hrun : ∀ t, MRef (run t) (run' t))
include le hrun

theorem forceWith_refines (i : Nat) : MRef (forceWith R check run i) (forceWith R check' run' i) := by
  intro s
  simp only [forceWith]
  cases s.cells[i]? with
  | none => exact Refines.refl _
  | some c =>
      cases c with
      | done v => exact Refines.refl _
      | pending code site =>
          exact Refines.next (hrun _ s) fun v s' =>
            verdict_refines le.onValue _ (inst s'.binds v) (Refines.refl _)

theorem prepare_refines (site : Site) (code : Tm) (i : Nat) :
    MRef (prepare R check run site code i) (prepare R check' run' site code i) := by
  unfold prepare
  exact MRef.ite (fun _ => MRef.bind (forceWith_refines R le hrun i) fun _ => MRef.pure _)
    fun _ => MRef.ite (fun _ => MRef.bind (hrun code) fun v s =>
        verdict_refines le.onValue site (inst s.binds v) (Refines.refl _))
      fun _ => MRef.pure _

theorem bindOne_refines (site : Site) (a : Tm) :
    MRef (bindOne R check run site a) (bindOne R check' run' site a) := by
  unfold bindOne
  exact MRef.ite (fun _ _ => verdict_refines le.onValue site a (Refines.refl _))
    fun _ s => verdict_refines le.onCode site a
      (MRef.bind (prepare_refines R le hrun site _ _) (fun _ => MRef.pure _) _)

theorem bindArgs_refines (f : String) :
    ∀ i l, MRef (bindArgs R check run f i l) (bindArgs R check' run' f i l)
  | _, [] => MRef.pure _
  | i, a :: rest =>
      MRef.bind (bindOne_refines R le hrun (f, i) a) fun _ =>
        MRef.bind (bindArgs_refines f (i + 1) rest) fun _ => MRef.pure _

theorem callRow_refines (n : Nat) (f : String) (args : List Tm) (row : List Tm × Tm) :
    MRef (callRow R check run n f args row) (callRow R check' run' n f args row) :=
  MRef.bind (bindArgs_refines R le hrun f 0 args) fun _ =>
    MRef.bind (unifyPairs_refines
      (fun _ _ => unifyM_refines (forceWith_refines R le hrun) n _ _ _ _) _) fun _ => hrun _

theorem stepForm_refines (n : Nat) :
    ∀ form, MRef (stepForm R check run n form) (stepForm R check' run' n form)
  | .value _ => MRef.pure _
  | .force i => forceWith_refines R le hrun i
  | .name _ => fun st =>
      Refines.ite (fun _ => Refines.flatMap fun b _ => hrun b st) fun _ => Refines.refl _
  | .superpose _ => fun st => Refines.flatMap fun a _ => hrun a st
  | .letIn _ _ _ =>
      MRef.bind (hrun _) fun _ =>
        MRef.bind (unifyM_refines (forceWith_refines R le hrun) n _ _ _ _) fun _ => hrun _
  | .matchSelf _ _ => fun st =>
      Refines.flatMap fun _ _ =>
        withFresh_refines (fun _ =>
          MRef.bind (unifyM_refines (forceWith_refines R le hrun) n _ _ _ _) fun _ => hrun _) st
  | .addSelf _ => MRef.refl _
  | .evalCode _ => MRef.bind (hrun _) fun _ => hrun _
  | .plus _ _ =>
      MRef.bind (MRef.bind (hrun _) fun v s =>
          verdict_refines le.onValue _ (inst s.binds v) (Refines.refl _)) fun _ =>
        MRef.bind (MRef.bind (hrun _) fun v s =>
          verdict_refines le.onValue _ (inst s.binds v) (Refines.refl _)) fun _ => MRef.refl _
  | .applyCell i _ => MRef.bind (forceWith_refines R le hrun i) fun _ => hrun _
  | .callOrBuild f args => fun st =>
      Refines.ite (fun _ => MRef.bind (MRef.seqM hrun _) (fun _ => MRef.pure _) st)
        fun _ => Refines.flatMap fun _ _ =>
          withFresh_refines (fun _ => callRow_refines R le hrun n f args _) st
  | .build _ => MRef.bind (MRef.seqM hrun _) fun _ => MRef.pure _

theorem step_refines (n : Nat) (t : Tm) : MRef (step R check run n t) (step R check' run' n t) :=
  fun st => stepForm_refines R le hrun n (classify (inst st.binds t)) st

end Weakening

/-- **Weakening a check changes only type errors.** For any reading, if the verdicts `check'`
accept everything `check` accepts, every run under `check'` is the run under `check` with
refused arguments replaced. -/
theorem eval_refines (R : Reading) {check check' : Verdicts} (le : check.Le check') :
    ∀ n t, MRef (eval R check n t) (eval R check' n t)
  | 0, _ => MRef.refl _
  | n + 1, t => step_refines R le (fun t' => eval_refines R le n t') n t

theorem deep_refines (R : Reading) {check check' : Verdicts} (le : check.Le check') :
    ∀ n t, MRef (deep R check n t) (deep R check' n t)
  | 0, _ => MRef.refl _
  | n + 1, t => fun st => by
      show Refines (readStep _ _ t st) (readStep _ _ t st)
      unfold readStep
      cases inst st.binds t with
      | cell i =>
          exact MRef.bind (forceWith_refines R le (eval_refines R le n) i)
            (fun _ => deep_refines R le n _) st
      | held p => exact deep_refines R le n p st
      | val p => exact deep_refines R le n p st
      | expr items =>
          exact MRef.bind (MRef.seqM (deep_refines R le n) _) (fun _ => MRef.pure _) st
      | sym _ => exact Refines.refl _
      | num _ => exact Refines.refl _
      | str _ => exact Refines.refl _
      | var _ => exact Refines.refl _

theorem outcomes_refines (R : Reading) {check check' : Verdicts} (le : check.Le check')
    (n : Nat) (t : Tm) : MRef (outcomes R check n t) (outcomes R check' n t) :=
  MRef.bind (eval_refines R le n t) fun v => deep_refines R le n v

/-- With no refused argument on the left, the two sides of a refinement are equal. -/
theorem Refines.eq_of_no_badArg {α : Type} {xs ys : List (Out α)} (h : Refines xs ys)
    (none : ∀ site v, Out.badArg site v ∉ xs) : xs = ys := by
  induction h with
  | nil => rfl
  | keep o _ ih => rw [ih fun site v m => none site v (List.mem_cons_of_mem _ m)]
  | relax site v _ _ _ => exact absurd List.mem_cons_self (none site v)

/-! ## The same, on observed answers -/

/-- `ObsRefines xs ys`: the answers `ys` are `xs` with each refused argument replaced by some
list of answers, and every other answer kept, in order. -/
inductive ObsRefines : List Obs → List Obs → Prop where
  | nil : ObsRefines [] []
  | keep (o : Obs) {xs ys : List Obs} : ObsRefines xs ys → ObsRefines (o :: xs) (o :: ys)
  | relax (site : Site) (v : Tm) (zs : List Obs) {xs ys : List Obs} :
      ObsRefines xs ys → ObsRefines (.badArg site v :: xs) (zs ++ ys)

theorem Refines.obs {xs ys : List (Out Tm)} (h : Refines xs ys) :
    ObsRefines (xs.map Out.obs) (ys.map Out.obs) := by
  induction h with
  | nil => exact .nil
  | keep o _ ih => exact .keep _ ih
  | relax site v zs _ ih =>
      rw [List.map_cons, List.map_append]
      exact .relax site (plain v) _ ih

/-- With no refused argument on the left, the two sides are the same answers. -/
theorem ObsRefines.eq_of_no_badArg {xs ys : List Obs} (h : ObsRefines xs ys)
    (none : ∀ site v, Obs.badArg site v ∉ xs) : xs = ys := by
  induction h with
  | nil => rfl
  | keep o _ ih => rw [ih fun site v m => none site v (List.mem_cons_of_mem _ m)]
  | relax site v _ _ _ => exact absurd List.mem_cons_self (none site v)

/-- **Weakening a check changes only type errors**, on the answers of a request. -/
theorem answers_refines (R : Reading) {check check' : Verdicts} (le : check.Le check')
    (n : Nat) (space : List Tm) (t : Tm) :
    ObsRefines (answers R check n space t) (answers R check' n space t) :=
  (outcomes_refines R le n t _).obs

/-! ## Weakening within one line of the one-marker rule -/

/-- `D'` declares weaker types than `D` **on the same line**: every parameter holds under one
exactly when it holds under the other, and the verdicts of `D'` accept every value and every piece
of code that those of `D` accept. -/
structure WeakerOnLine (D D' : Decls) : Prop where
  sameLine : ∀ site, holdsTy (D.param site) = holdsTy (D'.param site)
  accepts : (valueCheck D).Le (valueCheck D')

theorem oneMarker_eq_of_sameLine {D D' : Decls}
    (same : ∀ site, holdsTy (D.param site) = holdsTy (D'.param site)) :
    oneMarker D = oneMarker D' := by
  unfold oneMarker
  congr 1
  funext site _
  exact same site

/-- **Law 2 for the one-marker rule.** Replacing declared parameter types by weaker ones on the
same line changes no answer except to remove type errors. -/
theorem weakening_within_line {D D' : Decls} (weaker : WeakerOnLine D D') (n : Nat)
    (space : List Tm) (t : Tm) :
    ObsRefines (answers (oneMarker D) (valueCheck D) n space t)
      (answers (oneMarker D') (valueCheck D') n space t) := by
  rw [oneMarker_eq_of_sameLine weaker.sameLine]
  exact answers_refines _ weaker.accepts n space t

/-- `T'` is weaker than `T` on the same line: it holds exactly when `T` does, and its checks
accept everything those of `T` accept, whatever the declared result types. -/
structure TyWeaker (T T' : Ty) : Prop where
  sameLine : holdsTy T = holdsTy T'
  onValue : ∀ (D : Decls) t, verdictTy D T t = true → verdictTy D T' t = true
  onCode : ∀ t, literalTy T t = true → literalTy T' t = true

/-- Changing a parameter's type leaves the checks of every type as they were: they read only the
declared result types. -/
@[simp] theorem verdictTy_set (D : Decls) (site : Site) (T : Ty) :
    verdictTy (D.set site T) = verdictTy D := rfl

/-- Declaring one parameter with a weaker type on its line is weaker on the line. -/
theorem weakerOnLine_set (D : Decls) (site : Site) {T' : Ty} (h : TyWeaker (D.param site) T') :
    WeakerOnLine D (D.set site T') where
  sameLine s := by
    simp only [Decls.set]
    by_cases hs : s = site
    · subst hs; simp [h.sameLine]
    · simp [hs]
  accepts := by
    constructor
    · intro s t ht
      simp only [valueCheck, verdictTy_set] at ht ⊢
      simp only [Decls.set] at ht ⊢
      by_cases hs : s = site
      · subst hs; simpa using h.onValue D t ht
      · simpa [hs] using ht
    · intro s t ht
      simp only [valueCheck, verdictTy_set] at ht ⊢
      simp only [Decls.set] at ht ⊢
      by_cases hs : s = site
      · subst hs; simpa using h.onCode t ht
      · simpa [hs] using ht

/-- The checks of the types read only the declared result types. -/
theorem verdictTy_congr {D D' : Decls} (h : D.result = D'.result) : verdictTy D = verdictTy D' := by
  have e : inferCode D = inferCode D' := by
    funext a
    unfold inferCode
    rw [h]
  funext ty t
  simp only [verdictTy, codeHas, e]

/-- Declared types that agree on results, and at each parameter are equal or weaker on the same
line, are weaker on the line. -/
theorem weakerOnLine_of_pointwise {D D' : Decls} (hres : D.result = D'.result)
    (h : ∀ site, D.param site = D'.param site ∨ TyWeaker (D.param site) (D'.param site)) :
    WeakerOnLine D D' where
  sameLine site := by
    rcases h site with e | w
    · rw [e]
    · exact w.sameLine
  accepts := by
    constructor
    · intro site v hv
      simp only [valueCheck] at hv ⊢
      rw [← verdictTy_congr hres]
      rcases h site with e | w
      · rw [← e]; exact hv
      · exact w.onValue D v hv
    · intro site v hv
      simp only [valueCheck] at hv ⊢
      rcases h site with e | w
      · rw [← e]; exact hv
      · exact w.onCode v hv

/-- A type that accepts everything is weaker than every type on its line. -/
theorem tyWeaker_of_top {T T' : Ty} (same : holdsTy T = holdsTy T')
    (top : ∀ (D : Decls) t, verdictTy D T' t = true) (topCode : ∀ t, literalTy T' t = true) :
    TyWeaker T T' :=
  ⟨same, fun D t _ => top D t, fun t _ => topCode t⟩

/-- `Proc` is weaker than every running type, and an undeclared parameter weaker still. -/
theorem tyWeaker_proc {T : Ty} (runs : holdsTy T = false) : TyWeaker T .proc :=
  tyWeaker_of_top (by rw [runs]; rfl) (fun _ _ => rfl) fun t => by
    cases t <;> rfl

theorem tyWeaker_undeclared {T : Ty} (runs : holdsTy T = false) : TyWeaker T .undeclared :=
  tyWeaker_of_top (by rw [runs]; rfl) (fun _ _ => rfl) fun t => by
    cases t <;> rfl

/-- `Atom` is weaker than every holding type. -/
theorem tyWeaker_atom {T : Ty} (holds : holdsTy T = true) : TyWeaker T .atom :=
  tyWeaker_of_top (by rw [holds]; rfl) (fun _ _ => rfl) fun t => by
    cases t <;> rfl

end Mettapedia.Languages.MeTTa.EvaluationControl.ParameterReadings
