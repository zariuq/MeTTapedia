import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContexts
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaActivation
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaBindingContexts
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaApplicationControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContinuationContexts
import Mettapedia.Languages.MeTTa.ContextualTransform.HEArgumentContexts
import Mettapedia.Languages.MeTTa.ContextualTransform.HEPriorityControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaTransformDemand
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaDynamicContexts
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLambdaControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaScopeControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaRuntimeMatchControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaScopePreservationControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaReadoutControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStagingControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstructorControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstructorFaultControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingContexts
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOutputPlanControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOutputPlanFormationControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstraintPresentationControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstraintReadoutControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingBindingControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingScopeControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingRegionControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCollectionReadoutControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOutputPlanListHeadControls
import Mettapedia.Languages.MeTTa.PeTTa.ConstructorContinuations
import Mettapedia.Languages.MeTTa.PeTTa.ConstructorFaults
import Mettapedia.Languages.MeTTa.PeTTa.LambdaStagingDepth
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingFrontierScopes
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingContinuationScopes
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPrimitiveScopes
import Mettapedia.Languages.MeTTa.PeTTa.DynamicCallControls
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPrefixes
import Mettapedia.Languages.MeTTa.PeTTa.DynamicRecovery
import Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.ContextualExpansion
import Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.BudgetCycle
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
import Mettapedia.Languages.MeTTa.ContextualTransform.ImmediateRemoval
import Mettapedia.Languages.MeTTa.ContextualTransform.HybridImmediateRemoval
import Mettapedia.Machines.ImmediateStoreCost
import Mettapedia.Machines.SymbolHeadMemo
import Mettapedia.Machines.SymbolHeadService
import Mettapedia.Machines.EffectfulRowSelection
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaSelectionCursor
import Mettapedia.Languages.MeTTa.ContextualTransform.RetainedStorePrograms
import Mettapedia.Machines.PreparedReceiptOwnership
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OrderedStoreStability
import Mettapedia.Languages.MeTTa.ContextualTransform.TransformHeadRecognition
import Mettapedia.Languages.MeTTa.ContextualTransform.SpecializedPublicationWork
import Mettapedia.Machines.ImmediateStorePrefixes
import Mettapedia.Machines.PreparedStoreProtocolControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PublicationProtocol
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ImmediatePublication
import Mettapedia.Machines.OperatorChoice.EncodedQueryBounds
import Mettapedia.Machines.OperatorChoice.WorldProfiles
import Lean.Util.CollectAxioms

/-! Audit the current tranche. The coverage ledger retains the larger goal's open obligations. -/

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let prefixes := [`Mettapedia.Languages.MeTTa.ContextualTransform,
    `Mettapedia.Languages.MeTTa.PeTTa.Unifying,
    `Mettapedia.Languages.MeTTa.PeTTa.StdLib,
    `Mettapedia.Machines.BoundedDeterministicRun,
    `Mettapedia.Machines.OrderedPriorityTraversal,
    `Mettapedia.Machines.OrderedPriorityDemand,
    `Mettapedia.Languages.MeTTa.HE.StatefulPriorityTraversal,
    `Mettapedia.FirstFreshName,
    `Mettapedia.ScopedString,
    `List.FirstOccurrence,
    `Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming,
    `Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection,
    `Mettapedia.Languages.MeTTa.PeTTa.CollectionCopyReadout,
    `Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout,
    `Mettapedia.Languages.MeTTa.PeTTa.AnswerReadout,
    `Mettapedia.Languages.MeTTa.PeTTa.ScopedSource,
    `Mettapedia.Languages.MeTTa.PeTTa.LambdaLifting,
    `Mettapedia.Languages.MeTTa.PeTTa.LambdaStaging,
    `Mettapedia.Languages.MeTTa.PeTTa.ConstructorDataHeads,
    `Mettapedia.Languages.MeTTa.PeTTa.ConstructorSpine,
    `Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation,
    `Mettapedia.Languages.MeTTa.PeTTa.Streaming,
    `Mettapedia.Languages.MeTTa.PeTTa.OutputPlan,
    `Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation,
    `Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination,
    `Mettapedia.Logic.LP.MutualInstantiation,
    `List.FirstSelection,
    `Mettapedia.Languages.MeTTa.PeTTa.UnifyingComputation,
    `Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms,
    `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ConsumableBudget,
    `Mettapedia.Machines.OperatorChoice,
    `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore,
    `Mettapedia.Data.List.FreshOccurrenceAllocation,
    `Mettapedia.Data.List.CountedErase,
    `Mettapedia.Machines.PreparedStoreProtocol,
    `Mettapedia.Machines.ImmediateStorePublication,
    `Mettapedia.Machines.ImmediateStorePrefixes,
    `Mettapedia.Data.List.PublicationWork,
    `Mettapedia.Machines.ImmediateStoreCost,
    `Mettapedia.Machines.HybridStorePublication,
    `Mettapedia.Data.List.PublicationSpecializationWork,
    `Mettapedia.Machines.SymbolTableHeadCache,
    `Mettapedia.Machines.SymbolHeadMemo,
    `Mettapedia.Machines.SymbolHeadService,
    `Mettapedia.Machines.EffectfulRowSelection,
    `Mettapedia.Machines.Cursor.StatefulQueryRun,
    `Mettapedia.Machines.PreparedStoreStability,
    `Mettapedia.Machines.PreparedReceiptOwnership,
    `Mettapedia.Data.List.RetainedOccurrenceAllocation,
    `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStoreStability,
    `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ImmediatePublication,
    `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.PublicationProtocol]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let owners := prefixes ++
    [`Mettapedia.Data.List.FirstOccurrence,
     `Mettapedia.Data.List.FirstSelection,
     `Mettapedia.Languages.MeTTa.PeTTa.Streaming,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingPhases,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingReturns,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingSpec,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingPrefixes,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingDemand,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlan,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanCompiler,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanGate,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanNames,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanPolicy,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanBranchRules,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanFormation,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanFormationCorrect,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanFormationDepth,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanProgramFormation,
     `Mettapedia.Data.List.OptionMapM,
     `Mettapedia.Data.List.OptionMapMReflection,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPreservation,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintRefusal,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanConstraintAdmission,
     `Mettapedia.Languages.MeTTa.PeTTa.EagerDFS,
     `Mettapedia.Logic.LP.UnificationOccurs,
     `Mettapedia.Logic.LP.MutualInstantiation,
     `Mettapedia.Logic.LP.UnificationIdempotence,
     `Mettapedia.Logic.LP.UnificationRenaming,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintReadout,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingAnswerTransport,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingBindingInvariant,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingBindingPreservation,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingBindingReachability,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingScopeInvariant,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingScopePreservation,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingScopeReachability,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingRegions,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionSelections,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionPreservation,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionReachability,
     `Mettapedia.Languages.MeTTa.PeTTa.CollectionCopyReadout,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingCollectionCopies,
     `Mettapedia.Languages.MeTTa.PeTTa.StreamingCollectionReadout,
     `Mettapedia.Languages.MeTTa.PeTTa.OutputPlanDataHeads,
     `Mettapedia.Languages.ProcessCalculi.MORK.AtomRenamingApart,
     `Mettapedia.Languages.ProcessCalculi.MORK.SubstitutionSupport,
     `Mettapedia.Data.List.FirstSelectionInvariant,
     `Mettapedia.Languages.MeTTa.PeTTa.LambdaStagingDepth,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingCompilerLocals,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingLocalProjection,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingSequence,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingRecoveryFrames,
     `Mettapedia.Languages.MeTTa.PeTTa.ConstructorSpine,
     `Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation,
     `Mettapedia.Languages.MeTTa.PeTTa.ConstructorDirect,
     `Mettapedia.Languages.MeTTa.PeTTa.ConstructorAssembly,
     `Mettapedia.Languages.MeTTa.PeTTa.ConstructorRealization,
     `Mettapedia.Languages.MeTTa.PeTTa.ConstructorFaults,
     `Mettapedia.Languages.MeTTa.PeTTa.ConstructorContinuations,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingSound,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingGround,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingRename,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingRefinement,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingReturns,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingRetainedFrames,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingPrefixes,
     `Mettapedia.Languages.MeTTa.PeTTa.UnifyingControls,
     `Mettapedia.Languages.MeTTa.PeTTa.DynamicCallControls,
     `Mettapedia.Languages.MeTTa.PeTTa.DynamicRecovery,
     `Mettapedia.Languages.MeTTa.PeTTa.PrivateCode,
     `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OrderedStore,
     `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ConsumableBudget,
     `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PublicationProtocol,
     `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OrderedStoreStability,
     `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ImmediatePublication]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut implementationEntries : Nat := 0
  let mut selected : Std.HashSet Name := {}
  let mut moduleIndices : Std.HashSet Nat := {}
  for index in [:environment.header.moduleNames.size] do
    if owners.any (fun owner => owner.isPrefixOf environment.header.moduleNames[index]!) then
      moduleIndices := moduleIndices.insert index
  for (name, _) in environment.constants.toList do
    if prefixes.any (fun prefixName => prefixName.isPrefixOf name) then
      selected := selected.insert name
  for (name, index) in environment.const2ModIdx do
    if moduleIndices.contains index.toNat then
      if (environment.find? name).isSome then
        selected := selected.insert name
      else
        implementationEntries := implementationEntries + 1
        logInfo m!"CONTEXT_IMPLEMENTATION_ENTRY {name}"
  for name in selected.toList do
    let some information := environment.find? name
      | throwError "Selected declaration missing: {name}"
    let dependencies ← collectAxioms name
    unless (dependencies.filter (fun dependency => !allowed.contains dependency)).isEmpty do
      throwError "Unexpected axiom dependencies in {name}: {dependencies}"
    declarations := declarations + 1
    if information.isTheorem then
      theorems := theorems + 1
      logInfo m!"CONTEXT_CONTRACT {name}: {dependencies}"
  unless theorems > 0 do throwError "No contextual or operator-choice theorems loaded"
  logInfo m!"CONTEXT_AUDIT declarations={declarations} theorems={theorems}"
  logInfo m!"CONTEXT_IMPLEMENTATION_ENTRIES count={implementationEntries}"
