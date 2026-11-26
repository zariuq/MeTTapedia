import Lean

/-!
# The least general generalization of Lean terms

Terms that occur in several proofs are generalized to one term with variables, and that term,
abstracted over its variables, is a lemma each occurrence cites.  The generalization is the least
general one (Plotkin 1970) extended to dependent types, where a variable's type is generalized with
the same variables as the terms (Pfenning 1991):

* a position where every occurrence has the same term, mentioning nothing bound outside the
  fragment, keeps it;
* applications with the same arity, binders, projections, sorts and constants (up to their
  universe levels) are generalized part by part; a numeral is a value, as Lean writes it;
* any other position is a variable.  The same tuple of terms is the same variable.  A variable
  whose terms use the fragment's own binders is a function of them, applied to them (a pattern in
  Miller's sense); its type is the generalization of the terms' types, abstracted the same way;
* universe levels are generalized alike, the same tuple of levels being the same level parameter.

The variables are made in an order in which each one's type mentions only earlier ones, so that the
lemma is the abstraction over them in that order.  The kernel judges the lemma; nothing here is
trusted.
-/

open Lean Meta

namespace Mettapedia.Languages.Lean.Transport.Generalize

/-- A variable of the generalization: the metavariable standing for it, the fragment binders it is
applied to, and its value in each occurrence (a function of that occurrence's own binders). -/
structure Var where
  mvar : MVarId
  values : Array Expr

structure State where
  vars : Array Var := #[]
  /-- the variable made for a tuple of terms written over the common binders, and its arguments -/
  memo : Std.HashMap (Array Expr) (Expr) := {}
  /-- a level variable for a tuple of levels, and its levels in each occurrence -/
  levelVars : Array (LMVarId × Array Level) := #[]
  levelMemo : Std.HashMap (Array Level) Level := {}

abbrev GenM := StateRefT State MetaM

/-- The fragment's binders opened so far: the common ones of the generalization, and each
occurrence's own, position by position. -/
structure Binders where
  common : Array Expr := #[]
  own : Array (Array Expr)

/-- A term of an occurrence, its own binders replaced by the common ones. -/
def Binders.toCommon (bs : Binders) (j : Nat) (e : Expr) : Expr :=
  e.replaceFVars bs.own[j]! bs.common

/-- Whether `e` mentions nothing bound outside the fragment: only the common binders. -/
def closedOver (common : Array Expr) (e : Expr) : Bool :=
  !e.hasAnyFVar (fun id => !common.any (·.fvarId! == id))

/-- The level for a tuple of levels: the level when they agree; successors, maxima and impredicative
maxima generalized part by part; else a level variable. -/
partial def genLevel (ls : Array Level) : GenM Level := do
  let ls ← ls.mapM instantiateLevelMVars
  if ls.all (· == ls[0]!) then return ls[0]!
  match ls[0]! with
  | .succ _ =>
    if ls.all (·.isSucc) then
      return .succ (← genLevel (ls.map fun l => match l with | .succ a => a | a => a))
  | .max .. =>
    if ls.all (·.isMax) then
      return .max (← genLevel (ls.map fun l => match l with | .max a _ => a | a => a))
                  (← genLevel (ls.map fun l => match l with | .max _ b => b | b => b))
  | .imax .. =>
    if ls.all (·.isIMax) then
      return .imax (← genLevel (ls.map fun l => match l with | .imax a _ => a | a => a))
                   (← genLevel (ls.map fun l => match l with | .imax _ b => b | b => b))
  | _ => pure ()
  if let some l := (← get).levelMemo[ls]? then return l
  let l ← mkFreshLevelMVar
  modify fun s => { s with levelVars := s.levelVars.push (l.mvarId!, ls),
                           levelMemo := s.levelMemo.insert ls l }
  return l

/-- The common binders `xs` uses, closed under the binders their types mention, in binder order. -/
def usedBinders (common : Array Expr) (es : Array Expr) : MetaM (Array Expr) := do
  let mut used : Array Bool := common.map fun x => es.any (·.containsFVar x.fvarId!)
  -- a used binder's type may mention an earlier one: that one is used as well
  for i' in [0:common.size] do
    let i := common.size - 1 - i'
    if used[i]! then
      let ty ← inferType common[i]!
      for k in [0:i] do
        if ty.containsFVar common[k]!.fvarId! then used := used.set! k true
  return (common.zip used).filterMap fun (x, u) => if u then some x else none

/-- A numeral: `OfNat.ofNat T n inst` with `n` a literal. -/
def isNumeral (e : Expr) : Bool :=
  e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).isRawNatLit

mutual

/-- The generalization of the occurrences' terms `es` at one position, written over the common
binders.  `outer` is the local context before any of the fragment's binders were opened. -/
partial def gen (outer : LocalContext × LocalInstances) (bs : Binders) (es : Array Expr) : GenM Expr := do
  let es ← es.mapM fun e => return (← instantiateMVars e).consumeMData
  let cs := (Array.range es.size).map fun j => bs.toCommon j es[j]!
  if cs.all (· == cs[0]!) && closedOver bs.common cs[0]! then return cs[0]!
  let e0 := es[0]!
  -- a numeral is a value, as Lean writes it, not the application it elaborates to
  if es.any isNumeral then return ← newVar outer bs es
  match e0 with
  | .app .. =>
    let n := e0.getAppNumArgs
    if es.all (·.getAppNumArgs == n) then
      let heads := es.map (·.getAppFn)
      let sameHead ← match heads[0]! with
        | .const c _ => pure (heads.all fun h => h.isConstOf c)
        | .fvar _ =>
          let hs := (Array.range es.size).map fun j => bs.toCommon j heads[j]!
          pure (hs.all (· == hs[0]!) && closedOver bs.common hs[0]!)
        | _ => pure false
      if sameHead then
        let f ← gen outer bs heads
        let mut args := #[]
        for i in [0:n] do
          args := args.push (← gen outer bs (es.map (·.getArg! i)))
        return mkAppN f args
    newVar outer bs es
  | .const c _ =>
    if es.all (·.isConstOf c) then
      let n := e0.constLevels!.length
      let mut levels := #[]
      for i in [0:n] do
        levels := levels.push (← genLevel (es.map (·.constLevels![i]!)))
      return .const c levels.toList
    newVar outer bs es
  | .sort _ =>
    if es.all (·.isSort) then
      return .sort (← genLevel (es.map (·.sortLevel!)))
    newVar outer bs es
  | .lam n _ _ bi =>
    if es.all (·.isLambda) then genBinder outer bs es n bi true else newVar outer bs es
  | .forallE n _ _ bi =>
    if es.all (·.isForall) then genBinder outer bs es n bi false else newVar outer bs es
  | .proj S i _ =>
    if es.all (fun e => match e with | .proj S' i' _ => S' == S && i' == i | _ => false) then
      return .proj S i (← gen outer bs (es.map (·.projExpr!)))
    newVar outer bs es
  | _ => newVar outer bs es

/-- Binders at the same position: the types generalized, one common binder opened for the
generalization and one for each occurrence, the bodies generalized under them. -/
partial def genBinder (outer : LocalContext × LocalInstances) (bs : Binders) (es : Array Expr) (n : Name)
    (bi : BinderInfo) (isLambda : Bool) : GenM Expr := do
  let ty ← gen outer bs (es.map (·.bindingDomain!))
  withLocalDecl n bi ty fun x => do
    withLocalDeclsD (es.map fun e => (n, fun _ => pure e.bindingDomain!)) fun own => do
      let bs' : Binders := { common := bs.common.push x,
                             own := (Array.range es.size).map fun k => bs.own[k]!.push own[k]! }
      let body ← gen outer bs' ((Array.range es.size).map fun k => es[k]!.bindingBody!.instantiate1 own[k]!)
      if isLambda then mkLambdaFVars #[x] body else mkForallFVars #[x] body

/-- A variable for the tuple `es`: a function of the common binders the terms and their types
use, made outside the fragment's binders. -/
partial def newVar (outer : LocalContext × LocalInstances) (bs : Binders) (es : Array Expr) : GenM Expr := do
  let cs := (Array.range es.size).map fun j => bs.toCommon j es[j]!
  if let some v := (← get).memo[cs]? then return v
  -- its type: the generalization of the terms' types, at the same binders
  let ty ← gen outer bs (← es.mapM fun e => (inferType e : MetaM Expr))
  let ty ← instantiateMVars ty
  let used ← usedBinders bs.common (cs.push ty)
  let fty ← mkForallFVars used ty
  let m ← withLCtx outer.1 outer.2 (mkFreshExprMVar fty)
  let values ← (Array.range es.size).mapM fun j => do
    let ownUsed := used.map fun x => bs.own[j]![(bs.common.findIdx? (· == x)).getD 0]!
    mkLambdaFVars ownUsed es[j]!
  let v := mkAppN m used
  modify fun s => { s with vars := s.vars.push { mvar := m.mvarId!, values },
                           memo := s.memo.insert cs v }
  return v

end

/-- A lemma generalizing terms: its level parameters, statement and proof, and for each
occurrence the levels and arguments that make it that occurrence. -/
structure Lemma where
  /-- whether the generalization kept no structure: the whole term is one variable -/
  trivial : Bool
  levelParams : List Name
  type : Expr
  value : Expr
  levels : Array (List Level)
  args : Array (Array Expr)

/-- The least general generalization of `es`, abstracted over its variables (in the order they were
made) and its level variables (named `u_1`, ...). -/
def generalize (es : Array Expr) : MetaM Lemma := do
  let outer := (← getLCtx, ← getLocalInstances)
  let (body, st) ← (gen outer { own := es.map fun _ => #[] } es).run {}
  let vars := st.vars.map (Expr.mvar ·.mvar)
  let trivial := (← instantiateMVars body).isMVar
  let value ← instantiateMVars (← mkLambdaFVars vars body (binderInfoForMVars := .default))
  -- the level variables become parameters, in the order they were made
  let mut params : List Name := []
  let mut value := value
  let mut i := 1
  for (l, _) in st.levelVars do
    let u := Name.mkSimple s!"u_{i}"
    i := i + 1
    params := params ++ [u]
    assignLevelMVar l (.param u)
  value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  let levels := (Array.range es.size).map fun j => st.levelVars.toList.map fun (_, ls) => ls[j]!
  let args := (Array.range es.size).map fun j => st.vars.map fun v => v.values[j]!
  return { trivial, levelParams := params, type, value, levels, args }

/-- Add the lemma under `name`, judged by the kernel now (not in the background, where a
refusal would only be logged). -/
def addLemma (name : Name) (l : Lemma) : MetaM Unit := do
  if l.value.hasMVar || l.type.hasMVar then throwError "the generalization left a metavariable"
  let decl := Declaration.thmDecl { name, levelParams := l.levelParams, type := l.type, value := l.value }
  match (← getEnv).addDeclCore 0 10000 decl none with
  | .ok env => setEnv env
  | .error ex => throwError "kernel: {(ex.toMessageData (← getOptions))}"

end Mettapedia.Languages.Lean.Transport.Generalize
