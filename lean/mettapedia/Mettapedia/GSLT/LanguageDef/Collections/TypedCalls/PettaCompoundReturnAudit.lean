import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyEntryPolicy
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundScopeControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSourceControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundRunControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnAudit

/-!
# Dependency audit for compound source entry, typed frames and result guards

This includes executable source certificates, actual producer entry, caller
capture, complete eager-profile mixed-host transport and retained runs up to
the existing host guard. Native body-mode/lowering authority is not asserted.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnState
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnFunction
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnFrames
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnBoundary
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundProducedEntry
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyEntryPolicy
  , `Mettapedia.Languages.MeTTa.PeTTa.Bridges.FormedBodyReturnAdmission
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyReturn
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyEntry
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedFrameTransport
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedWork
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaScopeMarks
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTransitions
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundScopeControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSourceControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTyped
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedRuns
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundRunControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrder
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkDepth ]

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
  if checked == 0 then throwError "no compound host-boundary theorem declarations found"
  logInfo m!"Compound source entry and typed host boundary: {checked} theorem declarations; standard axioms only"
