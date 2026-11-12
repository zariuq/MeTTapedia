import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSymbolicAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyControls

/-! # Dependency audit for scope-bounded typed body publication -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopes
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopeSource
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopeMachine
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyRun
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyControls ]

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
  if checked == 0 then throwError "no scope-bounded typed body theorems found"
  for failure in failures do logError failure
  unless failures.isEmpty do throwError "scope-bounded typed body axiom audit failed"
  logInfo m!"Scope-bounded typed body namespaces: {checked} theorem declarations; standard axioms only"
