import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkControls

/-!
# Dependency audit for source-earned finite-run return lineage

This covers actual call-order preservation, deterministic annotation updates,
owned source and typed dispatch, finite runs, source-produced entry and
positive/negative controls. Native optimized-body realization is a separate
obligation and is not established by this audit.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaContextFacts
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrder
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkDepth
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkControls ]

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
  if checked == 0 then throwError "no finite-run return-lineage theorem declarations found"
  logInfo m!"Actual finite-run return lineage: {checked} theorem declarations; standard axioms only"
