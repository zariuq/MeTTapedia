import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentReturnEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentHostControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaProducedFrameEntry

/-!
# Dependency audit for source-produced argument alignment

This checks the phase invariant, the actual operation and finite-run
preservation laws, the source controls, and the producer-to-checkpoint join.
Ready positions are operand recipes, not permanently established typings.
Neither successful body evaluation nor native compiler adequacy follows from
the alignment invariant or this dependency audit.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentHostControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaProducedFrameEntry
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnReadRecipe ]

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
  if checked == 0 then throwError "no argument-production theorem declarations found"
  logInfo m!"Source-produced argument alignment: {checked} theorem declarations; standard axioms only"
