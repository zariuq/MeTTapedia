import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnPublication

/-! # Dependency audit for the symbolic retained-return and qualified publication development -/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnFrames
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnPhases
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnView
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnTransitions
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceChoices
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceInvocation
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceActive
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnOwned
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnMachine
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnEntry
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnPublication ]

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
  if checked == 0 then throwError "no typed caller-return theorems found"
  for failure in failures do logError failure
  unless failures.isEmpty do throwError "typed caller-return axiom audit failed"
  logInfo m!"Typed caller-return namespaces: {checked} theorem declarations; standard axioms only"

