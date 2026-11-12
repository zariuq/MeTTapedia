import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryControls

/-! # Kernel dependency audit for native type-entry field/source correspondence -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryCodec
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntrySource
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryScope
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryControls ]

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
  if checked == 0 then throwError "no native type-entry theorems found"
  for failure in failures do logError failure
  unless failures.isEmpty do throwError "native type-entry axiom audit failed"
  logInfo m!"Native type-entry namespaces: {checked} theorem declarations; standard axioms only"
