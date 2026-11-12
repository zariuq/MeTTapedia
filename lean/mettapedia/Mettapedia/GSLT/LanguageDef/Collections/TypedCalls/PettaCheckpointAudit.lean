import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyRegionAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSeedEntryControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointBoundaryControls

/-! # Dependency audit for source-earned checkpoints and actual return dispatch -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyCheckpoint
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointReturn
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointFixtures
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSeededRegionEntry
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSeedEntryControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointBoundaryControls ]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut failures : Array String := #[]
  for (name, info) in env.constants.toList do
    if roots.any (·.isPrefixOf name) then
      match info with
      | .thmInfo _ =>
          checked := checked + 1
          let axioms ← liftCoreM (collectAxioms name)
          let bad := axioms.filter (· ∉ allowed)
          unless bad.isEmpty do failures := failures.push s!"{name}: {bad.toList}"
      | _ => pure ()
  if checked == 0 then throwError "no source-earned checkpoint or return-dispatch theorems found"
  for failure in failures do logError failure
  unless failures.isEmpty do throwError "checkpoint and actual return-dispatch axiom audit failed"
  logInfo m!"Source-earned checkpoint and return dispatch: {checked} theorem declarations; standard axioms only"
