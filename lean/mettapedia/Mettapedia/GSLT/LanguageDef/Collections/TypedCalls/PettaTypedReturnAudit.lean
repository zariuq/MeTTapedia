import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyFrameControls

/-! # Dependency audit for typed return delivery and saved-frame embedding -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnDelivery
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyFrameEmbedding
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyFrameControls ]

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
  if checked == 0 then throwError "no typed return-delivery or frame-embedding theorems found"
  for failure in failures do logError failure
  unless failures.isEmpty do throwError "typed return-delivery axiom audit failed"
  logInfo m!"Typed return-delivery and frame-embedding namespaces: {checked} theorem declarations; standard axioms only"
