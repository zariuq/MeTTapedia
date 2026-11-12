import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemoControls

/-! # Kernel dependency audit for scoped cache publication and query histories -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSourceProjection
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemo
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemoHistory
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemoControls ]

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
  if checked == 0 then throwError "no scoped cache theorems found"
  for failure in failures do logError failure
  unless failures.isEmpty do throwError "scoped cache axiom audit failed"
  logInfo m!"Scoped cache namespaces: {checked} theorem declarations; standard axioms only"
