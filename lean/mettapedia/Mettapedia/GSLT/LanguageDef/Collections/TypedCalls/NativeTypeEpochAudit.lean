import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEpochControls
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRetainedFrames

/-! # Dependency audit for chronological source-scope compression -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Machines.IssuedEpochDirectory
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeEpochs
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEpochCache
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEpochControls
  , ``Mettapedia.Languages.MeTTa.PeTTa.Unifying.Transition.append_frames ]

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
  if checked == 0 then throwError "no scope-epoch theorems found"
  for failure in failures do logError failure
  unless failures.isEmpty do throwError "scope-epoch axiom audit failed"
  logInfo m!"Scope-epoch namespaces: {checked} theorem declarations; standard axioms only"
