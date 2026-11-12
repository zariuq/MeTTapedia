import Mettapedia.Languages.Micromath.ModuleControls

/-! # Dependency audit for the authored Micromath read-premise controls -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Languages.Micromath.ModuleControls
  , `Mettapedia.GSLT.LanguageDef.CollectionReadRelation ]

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
  if checked == 0 then throwError "no Micromath module/read theorems found"
  for failure in failures do logError failure
  unless failures.isEmpty do throwError "Micromath module/read axiom audit failed"
  logInfo m!"Micromath module/read namespaces: {checked} theorem declarations; standard axioms only"
