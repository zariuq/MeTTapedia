import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyControls

/-! # Selected literal-family body scheduling and execution dependencies

This qualifies source readout, the complete selected frontier and its held
execution component. It does not certify native driver installation or the
explicit-function escape policy.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Languages.MeTTa.PeTTa.SelectedBodyPolicy
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyDeclarations
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyFrontier
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyExecution
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyControls ]

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
    if checked == 0 then throwError "no selected-body theorem declarations found under {root}"
    total := total + checked
  logInfo m!"Selected body readout, frontier and execution: {total} theorem declarations; standard axioms only"
