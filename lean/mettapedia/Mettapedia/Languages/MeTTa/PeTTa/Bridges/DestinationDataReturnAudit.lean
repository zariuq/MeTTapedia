import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnControls

/-!
# Dependency audit for compound source-return components

This covers local transitions, the complete owned source dispatcher, actual
fresh entry, all-budget packet and retained-state laws, and the effectful
controls. Native control-plan authority and typed-host composition remain
separate obligations.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnState
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnDispatch
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnEntry
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRaw
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnScopes
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnInvocation
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnActive
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnOwned
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRun
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnControls ]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if roots.any (·.isPrefixOf name) then
      match info with
      | .thmInfo _ =>
          checked := checked + 1
          let axioms ← liftCoreM (collectAxioms name)
          let bad := axioms.filter (· ∉ allowed)
          unless bad.isEmpty do throwError "{name}: unapproved axioms {bad.toList}"
      | _ => pure ()
  if checked == 0 then throwError "no compound source-return theorem declarations found"
  logInfo m!"Compound source-return components: {checked} theorem declarations; standard axioms only"
