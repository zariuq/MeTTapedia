import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataControls

/-!
# Dependency audit for source constructor-leaf regions

The actual preparer, local steps, bounded checkpoint runner and fresh clause
entry are covered. Native control-plan classification and complete compound
return-body integration are separate obligations.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Machines.Checkpoint
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataRecipe
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataDebt
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataCheckpoint
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataEntry
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataControls ]

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
  if checked == 0 then throwError "no constructor-region theorem declarations found"
  logInfo m!"Source constructor-leaf regions: {checked} theorem declarations; standard axioms only"
