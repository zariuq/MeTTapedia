import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionBranchControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchControls

/-! # Dependencies of ordered HE branch and selected-expression composition

The scope is the existing checked plain-Atom worker and contextual source
judgments. Native callbacks and stateful-host adequacy are separate.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionBranchComposition
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEInvocationBranchComposition
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchComposition
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchDerivation
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionBranchControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchControls ]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total : Nat := 0
  for root in roots do
    let mut checked : Nat := 0
    for (name, info) in env.constants.toList do
      if root.isPrefixOf name then
        match info with
        | .thmInfo _ =>
            checked := checked + 1
            let axioms ← liftCoreM (collectAxioms name)
            let bad := axioms.filter (· ∉ allowed)
            unless bad.isEmpty do throwError "{name}: unapproved axioms {bad.toList}"
        | _ => pure ()
    if checked == 0 then throwError "no HE branch-composition theorem declarations found under {root}"
    total := total + checked
  logInfo m!"HE ordered branches and selected-expression composition: {total} theorem declarations; standard axioms only"
