import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyRegionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextControls

/-! # Dependency audit for actual owned-source and typed body-region transport -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodySourceEmbedding
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyRegionTransport
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyRegionControls ]

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
  if checked == 0 then throwError "no source or typed body-region transport theorems found"
  for failure in failures do logError failure
  unless failures.isEmpty do throwError "source and typed body-region transport axiom audit failed"
  logInfo m!"Source and typed body-region transport: {checked} theorem declarations; standard axioms only"
