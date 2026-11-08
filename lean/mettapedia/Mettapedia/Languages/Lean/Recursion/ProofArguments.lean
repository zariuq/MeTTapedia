import Mettapedia.Languages.Lean.Recursion.Export

/-!
# Proof-argument interfaces without an invented recursion model

Some source functions only transport a proof to another function or to a
quotient eliminator. Their input propositions and syntactic use paths are
exported directly. They are not labelled as fixed points and receive no
fabricated recursion or interpretation theorem.
-/

namespace Mettapedia.Languages.Lean.Recursion.ProofArguments

open _root_.Lean Meta
open Export

def uses (parameter : FVarId) (expression : Expr) (path : List String := []) : List (List String) :=
  match expression with
  | .fvar name => if name == parameter then [path] else []
  | .app function argument =>
      uses parameter function (path ++ ["application-function"]) ++
      uses parameter argument (path ++ ["application-argument"])
  | .lam name type body _ =>
      uses parameter type (path ++ ["lambda-type:" ++ name.toString]) ++
      uses parameter body (path ++ ["lambda-body:" ++ name.toString])
  | .forallE name type body _ =>
      uses parameter type (path ++ ["forall-type:" ++ name.toString]) ++
      uses parameter body (path ++ ["forall-body:" ++ name.toString])
  | .letE name type value body _ =>
      uses parameter type (path ++ ["let-type:" ++ name.toString]) ++
      uses parameter value (path ++ ["let-value:" ++ name.toString]) ++
      uses parameter body (path ++ ["let-body:" ++ name.toString])
  | .proj name index value => uses parameter value (path ++ [s!"projection:{name}:{index}"])
  | .mdata _ body => uses parameter body path
  | _ => []

def render (source : Name) : MetaM String := do
  let .defnInfo info ← getConstInfo source | throwError "proof-argument source is not a definition: {source}"
  let value ← etaExpand info.value
  let arguments ← lambdaTelescope value fun parameters body => do
    let mut arguments := []
    for index in [:parameters.size] do
      let parameter := parameters[index]!
      let type ← inferType parameter
      if ← isProp type then
        let proposition ← mkLambdaFVars (parameters.extract 0 index) type (usedOnly := true)
        let locations := uses parameter.fvarId! body
        arguments := arguments ++ [form [word "argument", word (toString index),
          form [word "Proposition", term (← read source proposition)],
          form [word "Uses", form (locations.map fun path =>
            form (path.map fun step => word (Json.str step).compress))]]]
    return arguments
  if arguments.isEmpty then throwError "source has no explicit proof arguments: {source}"
  return (form [word "LeanProofArgumentFunction", named source,
    form [word "SourceType", term (← read source info.type)],
    form [word "Body", term (← read source info.value)],
    form [word "Arguments", form arguments]]).pretty 120 ++ "\n\n"

end Mettapedia.Languages.Lean.Recursion.ProofArguments
