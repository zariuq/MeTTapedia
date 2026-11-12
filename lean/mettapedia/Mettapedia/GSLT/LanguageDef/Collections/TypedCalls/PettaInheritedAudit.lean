import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedMachine
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedFixtures
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedResumptionControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedMixedControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationScalarReduction

/-!
# Dependency audit for inherited-context execution and caller handoff

This audits the general operation, execution and boundary theorems together
with the source fixture's formation facts, the composed resumption controls and
the independently checked mixed-host controls. The remaining root-frontier
reductions have their own qualification and are not inferred from this audit.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedMachine
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedFixtures
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedResumptionControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationScalarReduction ]

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
  if checked == 0 then throwError "no inherited-context theorem declarations found"
  logInfo m!"Inherited context and host handoff: {checked} theorem declarations; standard axioms only"
