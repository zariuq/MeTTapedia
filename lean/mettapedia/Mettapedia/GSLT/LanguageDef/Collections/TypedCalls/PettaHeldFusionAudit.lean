import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldFusionControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldFusionWorldControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBoundMarkerControls

/-! # Ordinary held-return fusion and selected-frontier dependency audit -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyFusion
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldFusionControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldFusionWorldControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBoundMarkerControls ]

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
    if checked == 0 then throwError "no held-return fusion theorem declarations found under {root}"
    total := total + checked
  logInfo m!"Ordinary held-return fusion: {total} theorem declarations; standard axioms only"
