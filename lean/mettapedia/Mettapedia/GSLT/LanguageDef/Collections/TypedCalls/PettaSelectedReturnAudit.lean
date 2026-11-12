import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopeBoundary

/-!
# Dependency audit for selected-frame and scope return obligations

The audit includes actual source and typed operation laws, source-produced
mark installation, collection push/pop, terminal guard dispatch and controls.
It does not infer the still-separate all-step annotation-evolution theorem or
a native optimized-body realization from these checked constituents.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnBoundary
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnControls ]

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
  if checked == 0 then throwError "no selected-frame theorem declarations found"
  logInfo m!"Selected frame and scope obligations: {checked} theorem declarations; standard axioms only"
