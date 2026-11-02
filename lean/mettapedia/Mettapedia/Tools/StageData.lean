import Lean
import Lean.Meta.Transform

/-!
# Selective definitional staging of data

Unfold only the caller-selected namespaces, leaving ordinary executable
operations intact. This can expose finite data whose generic construction
mentions a noncomputable semantic interface. Both type and value are checked
by definitional equality. `stagedHEq%` produces a reflexivity proof that the
kernel checks against the two original values; the elaborator adds no axiom.
-/

set_option autoImplicit false
namespace Mettapedia.Tools.StageData
open Lean Meta Elab Term

private def selected (namespaces : Array Name) (name : Name) : Bool :=
  let publicName := (privateToUserName? name).getD name
  namespaces.any fun leading => leading.isPrefixOf publicName

partial def stage (namespaces : Array Name) (expression : Expr) : MetaM Expr := do
  let rec visit (expression : Expr) : MonadCacheT Expr Expr MetaM Expr :=
    checkCache expression fun _ => Core.withIncRecDepth do
      if (← isType expression) || (← isProof expression) then return expression
      if let .const name _ := expression.getAppFn then
        if selected namespaces name then
          let next ← withTransparency .all (whnf expression)
          if next != expression then return ← visit next
      if expression.getAppFn.isLambda || expression.getAppFn.isProj || expression.getAppFn.isLet then
        let next ← withTransparency .all (whnf expression)
        if next != expression then return ← visit next
      match expression with
      | .app .. =>
          let rebuilt := mkAppN (← visit expression.getAppFn) (← expression.getAppArgs.mapM visit)
          let reduced := rebuilt.headBeta
          if reduced != rebuilt then visit reduced else return rebuilt
      | .proj .. =>
          let next ← withTransparency .all (whnf expression)
          if next != expression then visit next else return expression
      | .lam .. => lambdaTelescope expression fun variables body => do
          mkLambdaFVars variables (← visit body)
      | .letE .. => visit (← zetaReduce expression)
      | _ => return expression
  visit expression |>.run

syntax "stageValue% " "[" ident,* "]" term : term
elab_rules : term
  | `(stageValue% [$namespaces,*] $value) => do
      let original ← elabTerm value none
      let result ← stage (namespaces.getElems.map fun name => name.getId.eraseMacroScopes) original
      unless ← withTransparency .all (isDefEq (← inferType result) (← inferType original)) do
        throwError "staging changed the data type"
      unless ← withTransparency .all (isDefEq result original) do
        throwError "staging changed the data value"
      return result

syntax "stagedHEq% " term "," term : term
elab_rules : term
  | `(stagedHEq% $first, $second) => do
      let first ← elabTerm first none
      let second ← elabTerm second none
      unless ← withTransparency .all (isDefEq first second) do
        throwError "the staged and source values are not definitionally equal"
      let expected ← mkHEq first second
      let proof ← mkHEqRefl first
      return Expr.letE `_stagedEquality expected proof (.bvar 0) true

elab "stagedProof% " value:term : term <= expectedType => do
  let expected := expectedType
  unless ← isProp expected do throwError "stagedProof% expects a proposition"
  let proof ← elabTerm value none
  unless ← withTransparency .all (isDefEq (← inferType proof) expected) do
    throwError "the source proof establishes a different proposition"
  return Expr.letE `_stagedProof expected proof (.bvar 0) true

/-- Retain a compact explicit data type after checking the original inferred
type by full definitional equality. The kernel checks the ascription too. -/
elab "stagedData% " value:term : term <= expectedType => do
  let data ← elabTerm value none
  unless ← withTransparency .all (isDefEq (← inferType data) expectedType) do
    throwError "the staged data has a different type"
  return Expr.letE `_stagedData expectedType data (.bvar 0) true

end Mettapedia.Tools.StageData
