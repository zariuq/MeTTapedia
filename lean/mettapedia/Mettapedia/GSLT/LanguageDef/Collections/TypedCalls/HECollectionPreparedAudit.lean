import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCompositionAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionPreparedControls

/-! # Private checked-sum region dependency audit -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Machines.FoldNativeCompletion
  , `Mettapedia.Machines.PrivateScalarFold
  , `Mettapedia.Machines.PrivateScalarCompletion
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionPreparedSum
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionPreparedControls ]

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
    if checked == 0 then throwError "no private-fold theorem declarations found under {root}"
    total := total + checked
  logInfo m!"Private checked-sum source region: {total} theorem declarations; standard axioms only"
