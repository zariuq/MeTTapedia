import Lean
import Mettapedia.Languages.Lean.Recursion.AccessibleNatBrec

/-!
# Reading the recursion implementation of Lean 4.33.1 declarations

The reader follows actual definition applications, including the compiler's
packed unary wrapper. It stops at the recursion operator rather than unfolding
the operator's implementation. All expressions in a returned reading remain
in the continuation's local context.
-/

namespace Mettapedia.Languages.Lean.Recursion.Inspect4331

open _root_.Lean Meta

inductive Method where
  | measure
  | natBrec
  | generalRelation
  deriving DecidableEq, Inhabited

structure Measured where
  implementation : Name
  parameters : Array Expr
  domain : Expr
  motive : Expr
  measure : Option Expr
  relation : Expr
  wellFounded : Expr
  recipe : Expr
  application : Expr
  method : Method := .measure

/-- Read through only the head of a definition application. This exposes
compiler wrappers without searching unrelated library declarations. -/
partial def head (owner : Name) (parameters : Array Expr) (expression : Expr)
    (fuel : Nat) (next : Measured → MetaM α) : MetaM (Option α) := do
  if fuel == 0 then throwError "recursion wrapper depth exhausted at {owner}"
  let expression := expression.consumeMData.headBeta
  if expression.isAppOf ``WellFounded.Nat.fix then
    let args := expression.getAppArgs
    unless args.size ≥ 4 do throwError "partially applied recursion operator at {owner}"
    let relation ← mkAppM ``InvImage #[mkConst ``Nat.lt, args[2]!]
    let founded ← mkAppM ``AccessibleRecipe.measure_wellFounded #[args[2]!]
    return some (← next ⟨owner, parameters, args[0]!, args[1]!, some args[2]!, relation, founded,
      args[3]!, expression, .measure⟩)
  if expression.isAppOf ``Nat.brecOn then
    let args := expression.getAppArgs
    unless args.size ≥ 3 do throwError "partially applied Nat.brecOn at {owner}"
    let measure := Expr.lam `n (mkConst ``Nat) (.bvar 0) .default
    let recipe ← mkAppM ``AccessibleNatBrec.recipe #[args[2]!]
    let relation ← mkAppM ``InvImage #[mkConst ``Nat.lt, measure]
    let founded ← mkAppM ``AccessibleRecipe.measure_wellFounded #[measure]
    return some (← next ⟨owner, parameters, mkConst ``Nat, args[0]!, some measure, relation, founded,
      recipe, expression, .natBrec⟩)
  if expression.isAppOf ``WellFounded.fix then
    let args := expression.getAppArgs
    unless args.size ≥ 5 do throwError "partially applied WellFounded.fix at {owner}"
    return some (← next ⟨owner, parameters, args[0]!, args[1]!, none, args[2]!, args[3]!,
      args[4]!, expression, .generalRelation⟩)
  match expression with
  | .lam .. =>
      lambdaTelescope expression fun more body => head owner (parameters ++ more) body (fuel - 1) next
  | .letE _ _ value body _ => head owner parameters (body.instantiate1 value) (fuel - 1) next
  | _ =>
      let .const name levels := expression.getAppFn | return none
      if name == ``dite || name == ``ite || (← isMatcher name) then return none
      let some (.defnInfo definition) := (← getEnv).find? name | return none
      let value := definition.value.instantiateLevelParams definition.levelParams levels
      head name parameters (mkAppN value expression.getAppArgs) (fuel - 1) next

def measured (name : Name) (next : Measured → MetaM α) : MetaM (Option α) := do
  let info ← getConstInfo name
  let .defnInfo definition := info | return none
  head name #[] definition.value 32 next

structure Call where
  locals : Array Expr
  capability : Expr
  argument : Expr
  proof : Expr
  obligation : Expr
  sourceCall : Option Expr := none
  sourceEquation : Option Name := none

/-- Computational calls to a local lower-value capability. The proof argument
is kept and checked, rather than erased with the executable computation.
Traversal enters the actual branch binders and lets, so conditions and
constructor-specialized states remain available when closing the statement. -/
partial def calls (expression : Expr) (locals : Array Expr)
    (visit : Call → MetaM Unit) : MetaM Unit := do
  let expression := expression.consumeMData
  if ← isProof expression then return
  match expression with
  | .lam name type body binder =>
      withLocalDecl name binder type fun x =>
        calls (body.instantiate1 x) (locals.push x) visit
  | .letE name type value body _ =>
      calls value locals visit
      withLetDecl name type value fun x =>
        calls (body.instantiate1 x) (locals.push x) visit
  | .app .. =>
      let function := expression.getAppFn
      let arguments := expression.getAppArgs
      if function.isFVar && arguments.size ≥ 2 then
        let afterFirst ← whnf (← inferType (mkApp function arguments[0]!))
        if let .forallE _ proposition _ _ := afterFirst then
          if ← isProp proposition then
            if ← isProof arguments[1]! then
              check arguments[1]!
              unless ← isDefEq (← inferType arguments[1]!) proposition do
                throwError "recursive call proof does not establish its obligation"
              visit ⟨locals, function, arguments[0]!, arguments[1]!, proposition, none, none⟩
      if function.isLambda then calls expression.headBeta locals visit
      else for argument in arguments do calls argument locals visit
  | .mdata _ body => calls body locals visit
  | .proj _ _ value => calls value locals visit
  | _ => pure ()

end Mettapedia.Languages.Lean.Recursion.Inspect4331
