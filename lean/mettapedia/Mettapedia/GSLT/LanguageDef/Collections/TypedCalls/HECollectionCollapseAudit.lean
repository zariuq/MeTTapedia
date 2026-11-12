import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseControls

/-! # Authored collapse, source capture and retained execution dependencies -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseFunction
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseFrontier
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseSource
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseControls ]

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
    if checked == 0 then throwError "no authored-collapse theorem declarations found under {root}"
    total := total + checked
  logInfo m!"Authored collapse and retained execution: {total} theorem declarations; standard axioms only"
