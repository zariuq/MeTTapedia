import Lean
import Mettapedia.Languages.Lean.CodeEquations.Erased
import Mettapedia.Languages.Lean.Declarations.Reader
import Mettapedia.Languages.Lean.Declarations.ConstructorInventory

/-!
# Erasing Lean definitions to code equations

For each constant a program needs, this module produces the PeTTa function
that computes it, from the theorems Lean proves about it:

* a definition by its equation theorems (`getEqnsFor?`); a definition without
  them by its body, which is the theorem `c = body` of definitional unfolding;
* a matcher by its matcher equations, with the alternatives passed as
  closures;
* a structure projection by the projection of its constructor;
* a constructor is data and needs no code.

Erasure follows Lean's compiler: a parameter whose type is a type, a type
former or a proposition is dropped from a constant's signature, and a type or
a proof passed in a kept position is the value `erased`. Constructors drop the
inductive's parameters. Decidability is a Boolean (`isTrue` is `true`), `ite`,
`dite` and `cond` are lazy conditionals, and `&&`, `||`, `!` are inlined so
that their second operand stays lazy, as Lean's `macro_inline` keeps it. A
class method applied to a closed instance is unfolded at export time to the
instance's field (`unfoldProjInst?`), so `a + b` on naturals is `Nat.add a b`.
Quotients run on representatives: `Quot.mk` is its argument and `Quot.lift f`
applies `f`; every observation of a quotient goes through Lean code that
respects it.

Some naturals operations are pinned: the target computes them directly with
Lean's conventions (truncated subtraction, division and remainder by zero),
as Lean's own kernel does with GMP. Their rules come from the prelude.

A constant the target cannot run is refused with its reason: noncomputable
definitions, opaque and unsafe constants, axioms, and direct uses of
recursors. Anything that depends on a refused constant is refused with it.
-/

open Lean Meta

namespace Mettapedia.Languages.Lean.CodeEquations

/- Erasure is decided once, by the declaration reader: `erasedType` for
every constant.  The fields of a constructor come from the declaration
analysis: for a family the profile admits, from its `Description` inventory
with guards or a tagged block (`ConstructorInventory.constructorFields`);
otherwise from the source Reader without a model-admission claim. -/
open Mettapedia.Languages.Lean.Declarations (erasedType)
open Mettapedia.Languages.Lean.Declarations.ConstructorInventory (constructorFields)

/-- For each parameter of a constant's type, whether it is kept by erasure.
The telescope is read through definitions (`DecidableRel r` has two binders),
the same way the equations are eta-expanded and call sites are read. -/
def keptParams (c : Name) : MetaM (Array Bool) := do
  let info ← getConstInfo c
  forallTelescopeReducing info.type fun xs _ => xs.mapM fun x => do
    return !(← erasedType (← inferType x))

/-- Operations the target computes directly. Their rules are in the prelude. -/
def pinnedConsts : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pow,
   ``Nat.beq, ``Nat.ble, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe,
   ``Nat.succ, ``Nat.pred, ``Nat.rec]

/-- The state of an export: the constants found so far, readable names for
local variables, and the refusals. -/
structure EraseState where
  needed : Array Name := #[]
  seen : NameSet := {}
  names : Std.HashMap FVarId String := {}
  fresh : Nat := 0
  refusals : Array (Name × String) := #[]

abbrev EraseM := StateRefT EraseState MetaM

/-- Something the eraser cannot express. -/
def unsupported (what : String) : EraseM α :=
  throwError "code equations: unsupported {what}"

def noteConst (c : Name) : EraseM Unit := do
  let s ← get
  unless s.seen.contains c do
    set { s with seen := s.seen.insert c, needed := s.needed.push c }

/-- A fresh variable name based on a local's user name. -/
def freshName (base : Name) : EraseM String := do
  let s ← get
  let stem := String.ofList (base.eraseMacroScopes.toString.toList.filter fun c => c.isAlphanum || c == '_')
  let stem := if stem.isEmpty then "x" else stem
  set { s with fresh := s.fresh + 1 }
  return s!"{stem}_{s.fresh}"

def nameOf (x : FVarId) : EraseM String := do
  if let some n := (← get).names[x]? then return n
  let n ← freshName (← x.getUserName)
  modify fun s => { s with names := s.names.insert x n }
  return n

/-- Whether an expression is erased at runtime: a proof, a type or a type former. -/
def isErasedTerm (e : Expr) : MetaM Bool := do
  try
    let t ← inferType e
    if ← isProp t then return true
    if (← whnfD t).isSort then return true
    isTypeFormerType t
  catch _ => return false

/-- A natural number literal, as Lean writes it in terms. -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if let .lit (.natVal n) := e then return some n
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let ty := e.getArg! 0
    if (← whnfR ty).isConstOf ``Nat then
      if let .lit (.natVal n) := (e.getArg! 1).consumeMData then return some n
  if e.isConstOf ``Nat.zero then return some 0
  return none

mutual

/-- Erase a term. -/
partial def erase (e : Expr) : EraseM ETerm := do
  let e := (← instantiateMVars e).consumeMData
  if ← isErasedTerm e then return .erased
  if let some n ← natLit? e then return .nat n
  match e with
  | .fvar x => return .var (← nameOf x)
  | .lit (.natVal n) => return .nat n
  | .lit (.strVal s) => return .str s
  | .lam .. =>
      lambdaTelescope e fun xs body => do
        let ps ← xs.toList.mapM fun x => nameOf x.fvarId!
        return .lam ps (← erase body)
  | .letE _ _ v b _ =>
      if ← isErasedTerm v then erase (b.instantiate1 v)
      else
        withLetDecl `x (← inferType v) v fun x => do
          let n ← nameOf x.fvarId!
          return .letE n (← erase v) (← erase (b.instantiate1 x))
  | .proj s i x => eraseProj s i x #[]
  | .mdata _ b => erase b
  | .const .. | .app .. => eraseApp e
  | _ => unsupported s!"term {← ppExpr e}"

/-- Erase the arguments of a value applied as a function: every argument is
passed, a type or proof as `erased`. -/
partial def eraseArgs (args : Array Expr) : EraseM (List ETerm) :=
  args.toList.mapM erase

/-- Apply an erased function value to further erased arguments. -/
partial def applyMore (f : ETerm) (rest : List ETerm) : ETerm :=
  if rest.isEmpty then f else .apv f rest

/-- A structure projection `x.i` (`Expr.proj`), with extra arguments. -/
partial def eraseProj (s : Name) (i : Nat) (x : Expr) (more : Array Expr) : EraseM ETerm := do
  let some info := getStructureInfo? (← getEnv) s | unsupported s!"projection of {s}"
  let some field := info.fieldNames[i]? | unsupported s!"projection {i} of {s}"
  let projFn := s ++ field
  noteConst projFn
  let base ← erase x
  return applyMore (.app projFn false [base]) (← eraseArgs more)

/-- Erase an application or a constant. -/
partial def eraseApp (e : Expr) : EraseM ETerm := do
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isLambda then return ← erase (e.headBeta)
  match fn with
  | .const c _ => eraseConstApp e c args
  | .proj s i x => eraseProj s i x args
  | .fvar x => return applyMore (.var (← nameOf x)) (← eraseArgs args)
  | _ => return applyMore (← erase fn) (← eraseArgs args)

/-- Erase a constant applied to arguments. -/
partial def eraseConstApp (e : Expr) (c : Name) (args : Array Expr) : EraseM ETerm := do
  let env ← getEnv
  let rest (k : Nat) : EraseM (List ETerm) := eraseArgs (args.extract k args.size)
  -- Conditionals and Booleans, kept lazy.
  -- `ite {α} c [h : Decidable c] t e`: the condition is the instance `h`.
  if c == ``ite && args.size ≥ 5 then
    return applyMore (.ite (← erase args[2]!) (← erase args[3]!) (← erase args[4]!)) (← rest 5)
  if c == ``dite && args.size ≥ 5 then
    let branch (b : Expr) : EraseM ETerm := do
      lambdaTelescope b fun _ body => erase body
    return applyMore (.ite (← erase args[2]!) (← branch args[3]!) (← branch args[4]!)) (← rest 5)
  -- Casts along equalities are the identity at runtime.
  if (c == ``Eq.mpr || c == ``Eq.mp || c == ``cast) && args.size ≥ 4 then
    return applyMore (← erase args[3]!) (← rest 4)
  if (c == ``Eq.rec || c == ``Eq.ndrec) && args.size ≥ 6 then
    return applyMore (← erase args[3]!) (← rest 6)
  if (c == ``Eq.recOn || c == ``Eq.casesOn) && args.size ≥ 6 then
    return applyMore (← erase args[5]!) (← rest 6)
  if c == ``cond && args.size ≥ 4 then
    return applyMore (.ite (← erase args[1]!) (← erase args[2]!) (← erase args[3]!)) (← rest 4)
  if (c == ``and || c == ``Bool.and) && args.size ≥ 2 then
    return applyMore (.ite (← erase args[0]!) (← erase args[1]!) (.app ``Bool.false true [])) (← rest 2)
  if (c == ``or || c == ``Bool.or) && args.size ≥ 2 then
    return applyMore (.ite (← erase args[0]!) (.app ``Bool.true true []) (← erase args[1]!)) (← rest 2)
  if (c == ``not || c == ``Bool.not) && args.size ≥ 1 then
    return applyMore (.ite (← erase args[0]!) (.app ``Bool.false true []) (.app ``Bool.true true [])) (← rest 1)
  if c == ``Decidable.decide && args.size ≥ 2 then
    return applyMore (← erase args[1]!) (← rest 2)
  if c == ``Decidable.isTrue && args.size ≥ 2 then
    return applyMore (.app ``Bool.true true []) (← rest 2)
  if c == ``Decidable.isFalse && args.size ≥ 2 then
    return applyMore (.app ``Bool.false true []) (← rest 2)
  -- Quotients on representatives.
  if c == ``Quot.mk && args.size ≥ 3 then
    return applyMore (← erase args[2]!) (← rest 3)
  if c == ``Quot.lift && args.size ≥ 6 then
    return applyMore (.apv (← erase args[3]!) [← erase args[5]!]) (← rest 6)
  -- A class method of a closed instance: its field.
  if (← getProjectionFnInfo? c).isSome then
    if let some e' ← unfoldProjInst? e then
      if e'.getAppFn.constName? != some c then return ← erase e'
  -- Pinned operations are called by name; the prelude computes them.
  if pinnedConsts.contains c then
    let kept ← keptParams c
    let mut as : List ETerm := []
    for i in [0:min kept.size args.size] do
      if kept[i]! then as := as ++ [← erase args[i]!]
    return applyMore (← saturate c false kept.size (kept.toList.count true) as)
      (← rest (min kept.size args.size))
  if let some ctor := env.find? c |>.bind (fun | .ctorInfo v => some v | _ => none) then
    let fieldsKept := (← constructorFields c).toArray
    let total := ctor.numParams + fieldsKept.size
    let mut as : List ETerm := []
    for i in [ctor.numParams:min total args.size] do
      if fieldsKept[i - ctor.numParams]! then as := as ++ [← erase args[i]!]
    return applyMore (← saturate c true total (fieldsKept.toList.count true) as)
      (← rest (min total args.size))
  -- A function: kept arguments by its signature.
  noteConst c
  let kept ← keptParams c
  let mut as : List ETerm := []
  for i in [0:min kept.size args.size] do
    if kept[i]! then as := as ++ [← erase args[i]!]
  return applyMore (← saturate c false kept.size (kept.toList.count true) as)
    (← rest (min kept.size args.size))

/-- A named function or constructor applied to its kept arguments; when fewer
than its kept arity are given, a closure over the rest. `_total` is the full
parameter count (unused beyond documentation of the call site). -/
partial def saturate (c : Name) (isCtor : Bool) (_total arity : Nat) (as : List ETerm) :
    EraseM ETerm := do
  if as.length ≥ arity then return .app c isCtor as
  let missing := arity - as.length
  let mut ps : List String := []
  for _ in [0:missing] do ps := ps ++ [← freshName `p]
  return .lam ps (.app c isCtor (as ++ ps.map ETerm.var))

end

/-! ## Patterns -/

/-- Erase a left-side argument as a pattern. `seen` holds the pattern
variables already bound; a repeated variable is a forced position and
becomes a wildcard. -/
partial def erasePat (e : Expr) : StateRefT (Std.HashSet FVarId) EraseM EPat := do
  let e := (← instantiateMVars e).consumeMData
  if let some n ← natLit? e then return .nat n
  match e with
  | .fvar x =>
      if (← get).contains x then return .wild
      modify (·.insert x)
      return .var (← nameOf x)
  | _ => pure ()
  -- `p + k` and `Nat.succ p` on naturals.
  if e.isAppOfArity ``Nat.succ 1 then
    match ← erasePat (e.getArg! 0) with
    | .succ k p => return .succ (k + 1) p
    | .nat n => return .nat (n + 1)
    | p => return .succ 1 p
  if e.isAppOfArity ``HAdd.hAdd 6 then
    if (← whnfR (e.getArg! 0)).isConstOf ``Nat then
      if let some k ← natLit? (e.getArg! 5) then
        if k > 0 then
          match ← erasePat (e.getArg! 4) with
          | .succ j p => return .succ (j + k) p
          | .nat n => return .nat (n + k)
          | p => return .succ k p
  let fn := e.getAppFn
  let args := e.getAppArgs
  if let .const c _ := fn then
    if let some (.ctorInfo ctor) := (← getEnv).find? c then
      let fieldsKept := (← constructorFields c).toArray
      let mut ps : List EPat := []
      for i in [ctor.numParams:args.size] do
        if fieldsKept[i - ctor.numParams]?.getD true then ps := ps ++ [← erasePat args[i]!]
      let name := if c == ``Decidable.isTrue then ``Bool.true
        else if c == ``Decidable.isFalse then ``Bool.false else c
      return .ctor name ps
  if ← isErasedTerm e then return .wild
  -- A literal of another type (`0 : ℤ`) is its instance's constructor value.
  if e.isAppOf ``OfNat.ofNat then
    if let some e' ← unfoldProjInst? e then return ← erasePat e'
  throwError "code equations: unsupported pattern {← ppExpr e}"

/-! ## Equations -/

/-- One equation theorem `∀ xs, hyps → lhs = rhs` as a branch of `fn`, with
`lhs` eta-expanded to `fn`'s full parameter list. -/
def branchOf (_fn : Name) (thm : Name) (kept : Array Bool) : EraseM EBranch := do
  let ty := (← getConstInfo thm).type
  forallTelescope ty fun _ body => do
    let some (_, lhs, rhs) := body.eq? | throwError "code equations: {thm} is not an equation"
    let lhsArgs := lhs.getAppArgs
    -- Eta-expand to the full parameter list.
    let lhsTy ← inferType lhs
    forallBoundedTelescope lhsTy (some (kept.size - lhsArgs.size)) fun ys _ => do
      let args := lhsArgs ++ ys
      let rhs := (mkAppN rhs ys).headBeta
      let (pats, _) ← (do
        let mut ps : List EPat := []
        for i in [0:args.size] do
          if kept[i]?.getD true then ps := ps ++ [← erasePat args[i]!]
        return ps : StateRefT (Std.HashSet FVarId) EraseM (List EPat)).run {}
      return { pats, rhs := ← erase rhs, theorem_ := thm }

/-- `c xs = body xs`: definitional unfolding, for a definition without
equation theorems. -/
def deltaBranch (c : Name) (kept : Array Bool) : EraseM EBranch := do
  let some (.defnInfo d) := (← getEnv).find? c | throwError "code equations: {c} has no body"
  forallTelescopeReducing d.type fun xs _ => do
    let lhsArgs := xs
    let rhs := (mkAppN (d.value.instantiateLevelParams d.levelParams
      (d.levelParams.map Level.param)) xs).headBeta
    let (pats, _) ← (do
      let mut ps : List EPat := []
      for i in [0:lhsArgs.size] do
        if kept[i]?.getD true then ps := ps ++ [← erasePat lhsArgs[i]!]
      return ps : StateRefT (Std.HashSet FVarId) EraseM (List EPat)).run {}
    return { pats, rhs := ← erase rhs, theorem_ := c }

/-- The projection rule of a structure projection function. It takes the
function's full kept arity: kept structure parameters (wildcards), the
structure value (its constructor over its kept fields), and the arguments of a
function-valued field, which the field is applied to. -/
def projectionFunction (c : Name) : EraseM EFunction := do
  let some pinfo ← getProjectionFnInfo? c | throwError "code equations: {c} is not a projection"
  let some (.ctorInfo ctor) := (← getEnv).find? pinfo.ctorName
    | throwError "code equations: {pinfo.ctorName} is not a constructor"
  let kept ← keptParams c
  let ctorKept := (← constructorFields pinfo.ctorName).toArray
  let mut pats : List EPat := []
  for i in [0:pinfo.numParams] do
    if kept[i]?.getD false then pats := pats ++ [.wild]
  let mut fields : List EPat := []
  let mut target : Option String := none
  for j in [0:ctor.numFields] do
    if ctorKept[j]?.getD false then
      let v := s!"field_{j}"
      fields := fields ++ [.var v]
      if j == pinfo.i then target := some v
  pats := pats ++ [.ctor pinfo.ctorName fields]
  let mut extras : List String := []
  for i in [pinfo.numParams + 1:kept.size] do
    if kept[i]?.getD false then extras := extras ++ [s!"arg_{i}"]
  pats := pats ++ extras.map EPat.var
  let rhs := match target with
    | some v => if extras.isEmpty then ETerm.var v else ETerm.apv (.var v) (extras.map ETerm.var)
    | none => ETerm.erased
  return { name := c, arity := pats.length, branches := [{ pats, rhs, theorem_ := c }] }

/-- Why a constant cannot be run, if it cannot. -/
def refusalReason (c : Name) : MetaM (Option String) := do
  let env ← getEnv
  match env.find? c with
  | none => return some "unknown constant"
  | some (.axiomInfo _) => return some "axiom"
  | some (.opaqueInfo _) => return some "opaque"
  | some (.recInfo _) => return some "recursor used directly"
  | some (.quotInfo _) => return some "quotient primitive used unapplied"
  | some (.thmInfo _) => return some "theorem in a computational position"
  | some (.inductInfo _) => return some "type in a computational position"
  | some info =>
      if info.isUnsafe then return some "unsafe"
      if (← isMatcher c) then return none
      if c.isStr && (c.getString! == "casesOn" || c.getString! == "recOn" ||
          c.getString! == "brecOn" || c.getString! == "binductionOn") then
        return some "recursor used directly"
      return none

/-- The code of one constant: its function, or nothing for a constructor. -/
def codeOf (c : Name) : EraseM (Option EFunction) := do
  let env ← getEnv
  if pinnedConsts.contains c then return none
  if let some (.ctorInfo _) := env.find? c then return none
  if let some reason ← refusalReason c then
    modify fun s => { s with refusals := s.refusals.push (c, reason) }
    return none
  if (← getProjectionFnInfo? c).isSome then return some (← projectionFunction c)
  let kept ← keptParams c
  let arity := kept.toList.count true
  if ← isMatcher c then
    let eqns ← Match.getEquationsFor c
    let branches ← eqns.eqnNames.toList.mapM fun thm => branchOf c thm kept
    return some { name := c, arity, branches }
  match ← getEqnsFor? c with
  | some eqns =>
      let branches ← eqns.toList.mapM fun thm => branchOf c thm kept
      return some { name := c, arity, branches }
  | none => return some { name := c, arity, branches := [← deltaBranch c kept] }

/-- The functions a set of root constants needs, following every constant their
code calls. Constants that cannot be run are listed as refusals; the export
records them so that a program reaching one is known not to run. -/
def exportClosure (roots : List Name) : MetaM (Array EFunction × Array (Name × String)) := do
  let go : EraseM (Array EFunction) := do
    for r in roots do noteConst r
    let mut done : NameSet := {}
    let mut out : Array EFunction := #[]
    let mut i := 0
    while i < (← get).needed.size do
      let c := (← get).needed[i]!
      i := i + 1
      if done.contains c then continue
      done := done.insert c
      try
        if let some f ← codeOf c then out := out.push f
      catch err =>
        let msg ← err.toMessageData.toString
        modify fun s => { s with refusals := s.refusals.push (c, msg) }
    return out
  let (fns, st) ← go.run {}
  return (fns, st.refusals)

end Mettapedia.Languages.Lean.CodeEquations
