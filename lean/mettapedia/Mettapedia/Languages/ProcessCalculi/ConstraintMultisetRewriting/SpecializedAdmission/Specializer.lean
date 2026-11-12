import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Reference

/-!
# The specializer: rule schemas to decision programs

`compile R` folds the rule into straight-line code; `specialize R` returns it for a rule of the
specialized class and nothing otherwise; `dispatch` sends a decision to the program or to the
generic route.

**How.** Registers `0 .. nparams - 1` hold the parameters, the next `uses` registers the labels the
decision selects, and temporaries follow. A static environment `Env` records which register holds
each bound local, as a WAM compiler's mode analysis does:

* `cm E n src t` matches the run-time term in register `src` against the pattern `t`: a bound
  local is compared (`eqReg`), an unbound one is bound to `src`, a closed subterm is compared
  whole (`eqConst`), a fresh name against the name the firing mints (`eqFresh`), an application
  is taken apart (`getApp`) into new registers from `n` on;
* `cb E n t` builds the value of a term whose locals are bound (`loadConst`, `loadFresh`,
  `mkApp`);
* a tell builds its determined side and matches the other side against it;
* a guard whose pattern is determined is decided on its value (`eqReg`, `countEq`); an absence
  (or a count of `0`) whose pattern has guard-only locals refuses when some present label
  matches the pattern (`scanNone`); a count of a nonzero number whose pattern has guard-only
  locals fails at every state (a solution can give those locals a value no label contains), and
  its code scans first only so that the C wrapper meets any stored schema of the bucket.

The checks come in the order of admission's conjuncts (shapes, fits, the uses and the tells,
the guards in order) and change no state; the commit builds the makes, mints, takes, and makes.

**The specialized class** (`InClass`): no frame variables in the rule, no told disequations, no
host guards; each tell, in order, has a side whose locals the parameters, the patterns and the
earlier tells determine; the makes and the asks are determined. A state is in the fragment when
its frame has no variables and no live disequations; parameters must be closed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission

/-- The register that holds each bound local. -/
abbrev Env := Nat → Option Nat

def Env.bind (E : Env) (x r : Nat) : Env := fun y => if y = x then some r else E y

/-- The locals of a term, in order (with repetition). -/
def Tm.locals (t : Tm) : List Nat := t.atoms.filterMap fun a => match a with
  | .loc k => some k
  | _ => none

/-- Every local of `t` is bound in `E`. -/
def determinedB (E : Env) (t : Tm) : Bool := t.locals.all fun k => (E k).isSome

mutual
/-- Match register `src` against the pattern; new registers from `n` on. Returns the
instructions, the environment after, and the next free register. -/
def cm (E : Env) (n src : Nat) : Tm → List MInstr × Env × Nat
  | .app f args =>
      if (Tm.app f args).closed then ([.eqConst src (.app f args)], E, n)
      else
        let r := cmList E (n + args.length) n args
        (.getApp src f args.length n :: r.1, r.2.1, r.2.2)
  | .code c => ([.eqConst src (.code c)], E, n)
  | .name m => ([.eqConst src (.name m)], E, n)
  | .var i => ([.eqConst src (.var i)], E, n)
  | .loc x => match E x with
      | some r => ([.eqReg src r], E, n)
      | none => ([], E.bind x src, n)
  | .fresh j => ([.eqFresh src j], E, n)
/-- Match registers `src`, `src + 1`, ... against the patterns. -/
def cmList (E : Env) (n src : Nat) : List Tm → List MInstr × Env × Nat
  | [] => ([], E, n)
  | t :: ts =>
      let a := cm E n src t
      let b := cmList a.2.1 a.2.2 (src + 1) ts
      (a.1 ++ b.1, b.2.1, b.2.2)
end

mutual
/-- Build the value of `t` into a register; new registers from `n` on. Returns the
instructions, the next free register, and the register that holds the value. -/
def cb (E : Env) (n : Nat) : Tm → List Instr × Nat × Nat
  | .app f args =>
      if (Tm.app f args).closed then ([.loadConst n (.app f args)], n + 1, n)
      else
        let r := cbList E n args
        (r.1 ++ [.mkApp r.2.1 f r.2.2], r.2.1 + 1, r.2.1)
  | .code c => ([.loadConst n (.code c)], n + 1, n)
  | .name m => ([.loadConst n (.name m)], n + 1, n)
  | .var i => ([.loadConst n (.var i)], n + 1, n)
  | .loc x => match E x with
      | some r => ([], n, r)
      | none => ([.loadConst n default], n + 1, n)
  | .fresh j => ([.loadFresh n j], n + 1, n)
/-- Build the values of the terms; the registers that hold them. -/
def cbList (E : Env) (n : Nat) : List Tm → List Instr × Nat × List Nat
  | [] => ([], n, [])
  | t :: ts =>
      let a := cb E n t
      let b := cbList E a.2.1 ts
      (a.1 ++ b.1, b.2.1, a.2.2 :: b.2.2)
end

/-- A tell with its determined side second. -/
def orient (E : Env) (e : Tm × Tm) : Tm × Tm := if determinedB E e.2 then e else (e.2, e.1)

/-- One tell `l = r` with `r` determined: build `r`, match `l` against it. -/
def compileTell (E : Env) (n : Nat) (lr : Tm × Tm) : List Instr × Env × Nat :=
  let b := cb E n lr.2
  let mm := cm E b.2.1 b.2.2 lr.1
  (b.1 ++ mm.1.map (fun i => Instr.test i .unsolvable), mm.2.1, mm.2.2)

/-- The tells, in order. -/
def compileTells : Env → Nat → List (Tm × Tm) → List Instr × Env × Nat
  | E, n, [] => ([], E, n)
  | E, n, e :: es =>
      let a := compileTell E n (orient E e)
      let rest := compileTells a.2.1 a.2.2 es
      (a.1 ++ rest.1, rest.2.1, rest.2.2)

/-- An absence or a count of guard `i`. -/
def countGuard (E : Env) (n i : Nat) (q : Tm) (k : Nat) : List Instr × Nat :=
  if determinedB E q then
    let x := cb E n q
    (x.1 ++ [.countEq x.2.2 k (.guard i)], x.2.1)
  else
    (.scanNone n (cm E (n + 1) n q).1 (.guard i) :: (if k = 0 then [] else [.fail (.guard i)]), n + 1)

def compileGuard (E : Env) (n i : Nat) : Guard → List Instr × Nat
  | .ask a b =>
      let x := cb E n a
      let y := cb E x.2.1 b
      (x.1 ++ y.1 ++ [.test (.eqReg x.2.2 y.2.2) (.guard i)], y.2.1)
  | .absent q => countGuard E n i q 0
  | .count q k => countGuard E n i q k
  | .host _ _ => ([.fail (.guard i)], n)

def compileGuards (E : Env) : Nat → Nat → List Guard → List Instr × Nat
  | n, _, [] => ([], n)
  | n, i, g :: gs =>
      let x := compileGuard E n i g
      let y := compileGuards E x.2 (i + 1) gs
      (x.1 ++ y.1, y.2)

/-! ### Shapes and fits -/

namespace Rule

/-- The atoms of every opened term. -/
def atomsAll (R : Rule) : List Tm := R.opened.flatMap Tm.atoms

/-- The names the rule writes. -/
def nameList (R : Rule) : List Nat := R.atomsAll.filterMap fun a => match a with
  | .name m => some m
  | _ => none

/-- The fresh names the rule writes. -/
def freshList (R : Rule) : List Nat := R.atomsAll.filterMap fun a => match a with
  | .fresh j => some j
  | _ => none

/-- The parameters that occur in an opened term. -/
def paramsUsed (R : Rule) : List Nat :=
  (List.range R.nparams).filter fun k => decide (Tm.loc k ∈ R.atomsAll)

end Rule

/-- Shapes: a fresh name beyond the firing's own refuses; every written name and every name of a
parameter that occurs must be minted; the takes' identities are not `0` and are distinct. -/
def shapeChecks (R : Rule) : List Instr :=
  (R.freshList.filter fun j => decide (R.fresh ≤ j)).map (fun _ => Instr.fail .shapes) ++
  R.nameList.map Instr.needName ++
  R.paramsUsed.map Instr.paramMinted ++
  (List.range R.takes.length).map Instr.occNonzero ++
  (List.range R.takes.length).flatMap fun u => (List.range u).map fun v => Instr.occDistinct u v .shapes

/-- Fits: every use's occurrence is present (its label goes to register `nparams + u`). -/
def lookups (R : Rule) : List Instr :=
  (List.range R.uses.length).map (fun u => Instr.lookup u (R.nparams + u))

/-- Fits: nothing is both read and taken. -/
def fitDistinct (R : Rule) : List Instr :=
  ((List.range R.uses.length).filter fun u => decide (R.takes.length ≤ u)).flatMap fun u =>
    (List.range R.takes.length).map fun v => Instr.occDistinct u v .fits

def fitChecks (R : Rule) : List Instr := lookups R ++ fitDistinct R

/-- The parameters are bound to their registers. -/
def paramEnv (np : Nat) : Env := fun x => if x < np then some x else none

/-- The program of a rule. -/
def compile (R : Rule) : Prog :=
  let np := R.nparams
  let nu := R.uses.length
  let m := cmList (paramEnv np) (np + nu) np R.uses
  let t := compileTells m.2.1 m.2.2 R.tells
  let gs := compileGuards t.2.1 t.2.2 0 R.guards
  let mk := cbList t.2.1 gs.2 R.makes
  { checks := (List.range np).map (fun k => Instr.loadParam k k) ++ shapeChecks R ++ fitChecks R ++
      m.1.map (fun i => Instr.test i .unsolvable) ++ t.1 ++ gs.1
    commit := mk.1 ++ [Instr.mint R.fresh] ++ (List.range R.takes.length).map Instr.remove ++
      mk.2.2.map Instr.add }

/-! ### The specialized class -/

def Guard.isHost : Guard → Bool
  | .host _ _ => true
  | _ => false

/-- The locals determined by the parameters and the patterns of the uses. -/
def Rule.boundUses (R : Rule) : List Nat := List.range R.nparams ++ R.uses.flatMap Tm.locals

/-- The tells, in order, each with a side whose locals are already determined. -/
def TellsInOrder : List Nat → List (Tm × Tm) → Prop
  | _, [] => True
  | b, e :: es => ((∀ k ∈ e.1.locals, k ∈ b) ∨ (∀ k ∈ e.2.locals, k ∈ b)) ∧
      TellsInOrder (b ++ e.1.locals ++ e.2.locals) es

/-- What is determined after the tells. -/
def boundAfter : List Nat → List (Tm × Tm) → List Nat
  | b, [] => b
  | b, e :: es => boundAfter (b ++ e.1.locals ++ e.2.locals) es

/-- **The specialized class.** -/
structure InClass (R : Rule) : Prop where
  noFrameVariables : ∀ t ∈ R.opened, ∀ i, Tm.var i ∉ t.atoms
  noToldDisequations : R.aparts = []
  noHostGuards : ∀ g ∈ R.guards, g.isHost = false
  tells : TellsInOrder R.boundUses R.tells
  makes : ∀ t ∈ R.makes, ∀ k ∈ t.locals, k ∈ boundAfter R.boundUses R.tells
  asks : ∀ a b, Guard.ask a b ∈ R.guards → ∀ k ∈ a.locals ++ b.locals,
    k ∈ boundAfter R.boundUses R.tells

/-- `TellsInOrder`, decided. -/
def tellsInOrderB : List Nat → List (Tm × Tm) → Bool
  | _, [] => true
  | b, e :: es => (e.1.locals.all (· ∈ b) || e.2.locals.all (· ∈ b)) &&
      tellsInOrderB (b ++ e.1.locals ++ e.2.locals) es

def Guard.inClassB (b : List Nat) : Guard → Bool
  | .ask x y => (x.locals ++ y.locals).all (· ∈ b)
  | .absent _ => true
  | .count _ _ => true
  | .host _ _ => false

/-- `InClass`, decided. -/
def Rule.inClassB (R : Rule) : Bool :=
  (R.opened.all fun t => t.atoms.all fun a => match a with | .var _ => false | _ => true) &&
  R.aparts.isEmpty &&
  tellsInOrderB R.boundUses R.tells &&
  (R.makes.all fun t => t.locals.all (· ∈ boundAfter R.boundUses R.tells)) &&
  (R.guards.all (Guard.inClassB (boundAfter R.boundUses R.tells)))

/-- The specializer: a program for a rule of the class, nothing otherwise. -/
def specialize (R : Rule) : Option Prog := if R.inClassB then some (compile R) else none

inductive Route where
  | specialized (P : Prog)
  | generic

/-- Where a decision goes. -/
def dispatch (R : Rule) (s : St) (p : List Tm) : Route :=
  match specialize R with
  | some P => if s.vars = 0 ∧ s.diseqs = 0 ∧ p.all Tm.closed = true then .specialized P else .generic
  | none => .generic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission
