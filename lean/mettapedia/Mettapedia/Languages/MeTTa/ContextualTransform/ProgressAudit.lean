import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContexts
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaActivation
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaBindingContexts
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCallCache
import Mettapedia.Languages.MeTTa.ContextualTransform.AdaptiveCallCache
import Mettapedia.Languages.MeTTa.ContextualTransform.HEChainContexts
import Mettapedia.Languages.MeTTa.ContextualTransform.HEStatefulContexts
import Mettapedia.Languages.MeTTa.ContextualTransform.HEReturnAndSpaces
import Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls
import Mettapedia.Languages.MeTTa.ContextualTransform.HEInertBindings
import Mettapedia.Languages.MeTTa.ContextualTransform.StoreOperations
import Mettapedia.Languages.MeTTa.ContextualTransform.StoreSelectionPolicies
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaQueryInterpretation
import Mettapedia.Languages.MeTTa.ContextualTransform.AdaptiveStorePrograms
import Mettapedia.Languages.MeTTa.ContextualTransform.ConcreteStorePrograms
import Mettapedia.Languages.MeTTa.ContextualTransform.StoreProgramPrefixes
import Mettapedia.Languages.MeTTa.ContextualTransform.CountedStoreInterpretation
import Mettapedia.Machines.PreparedStoreProtocolControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PublicationProtocol
import Mettapedia.Machines.OperatorChoice.EncodedQueryBounds
import Mettapedia.Machines.OperatorChoice.WorldProfiles
import Lean.Util.CollectAxioms

/-! Audit the current tranche. The coverage ledger retains the larger goal's open obligations. -/

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let prefixes := [`Mettapedia.Languages.MeTTa.ContextualTransform,
    `Mettapedia.Machines.OperatorChoice,
    `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore,
    `Mettapedia.Data.List.FreshOccurrenceAllocation,
    `Mettapedia.Data.List.CountedErase,
    `Mettapedia.Machines.PreparedStoreProtocol,
    `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.PublicationProtocol]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, information) in environment.constants.toList do
    if prefixes.any (fun prefixName => prefixName.isPrefixOf name) then
      let dependencies ← collectAxioms name
      unless (dependencies.filter (fun dependency => !allowed.contains dependency)).isEmpty do
        throwError "Unexpected axiom dependencies in {name}: {dependencies}"
      declarations := declarations + 1
      if information.isTheorem then
        theorems := theorems + 1
        logInfo m!"CONTEXT_CONTRACT {name}: {dependencies}"
  unless theorems > 0 do throwError "No contextual or operator-choice theorems loaded"
  logInfo m!"CONTEXT_AUDIT declarations={declarations} theorems={theorems}"
