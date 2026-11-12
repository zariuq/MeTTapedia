import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplayControls
import Mettapedia.Tools.CbvPositiveUnificationControls
import Mettapedia.Machines.ReplaySlices
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTerminalReplayControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnGuardEntry
import Mettapedia.Tools.CbvDestinationSupportControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedRootRuns.Bad

/-!
# Dependency audit for checked finite execution certificates

The scope is the certificate machinery, its trust-boundary controls and the
checked short source prefix. Whole caller-return fixture execution remains
a separate qualification target.
-/

open Lean Elab Command

private def roots : List Name :=
  [ `Mettapedia.Logic.LP.PositiveUnificationEvaluation
  , `Mettapedia.Tools.CbvPositiveUnification.Controls
  , `Mettapedia.Machines.ReplaySlices
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplayControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedClassGuardReduction
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceClassGuardReduction
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTerminalReadout
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTerminalReplayControls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnReplayPrefix
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnGuardEntry
  , `Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.encode_variable_support
  , `Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.VariableSupportControls
  , `Mettapedia.Tools.CbvDestinationSupport.Controls
  , `Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedRootRuns.Bad ]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total : Nat := 0
  for root in roots do
    let mut checked : Nat := 0
    for (name, info) in env.constants.toList do
      if root.isPrefixOf name then
        match info with
        | .thmInfo _ =>
            checked := checked + 1
            let axioms ← liftCoreM (collectAxioms name)
            let bad := axioms.filter (· ∉ allowed)
            unless bad.isEmpty do throwError "{name}: unapproved axioms {bad.toList}"
        | _ => pure ()
    if checked == 0 then throwError "no checked replay theorem declarations under {root}"
    total := total + checked
  logInfo m!"Checked replay certificates: {total} theorem declarations; standard axioms only"
