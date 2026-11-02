import Mettapedia.Machines.HEProducerCompletion
import Mettapedia.Machines.NestedQueryEffects
import Mettapedia.Machines.BufferedResidualReturn
import Mettapedia.Machines.ConditionalRegistration
import Mettapedia.Machines.NativeAliasDispatch
import Mettapedia.Machines.CallbackSourceEntry
import Mettapedia.Machines.ForeignCallbackInterruption
import Mettapedia.Machines.CallbackCompletion
import Mettapedia.Machines.PatternBranchFusion
import Mettapedia.Machines.PreparedPauseEntry
import Mettapedia.Machines.ActivationBranchEntry
import Mettapedia.Machines.ActivationBudgetAdmission
import Mettapedia.Machines.GraphInspection
import Mettapedia.Machines.ParameterSpanOpening
import Mettapedia.Machines.CallablePreparation
import Mettapedia.Machines.IntegerPageCost
import Mettapedia.Machines.DeepTermCost
import Mettapedia.Machines.CallableArityCache
import Mettapedia.Machines.CaseFirstObservation
import Mettapedia.Machines.BackoffRetryCost
import Mettapedia.Machines.CollectionTriggerPolicy
import Mettapedia.Machines.PlannedInvocationOperands
import Mettapedia.Machines.GenerationInvalidation
import Mettapedia.Machines.InternChunkOwnership
import Mettapedia.Machines.SourceResumeBoundary
import Mettapedia.Machines.SourceCondition
import Mettapedia.Machines.PreparedReturnCompletion
import Mettapedia.Machines.AuthorityObservation
import Mettapedia.Machines.SourceRoleElaboration
import Mettapedia.Machines.SourceContextAdmission
import Mettapedia.Machines.BranchLocalNeed.CacheLaws
import Mettapedia.Machines.LexicalSourceOpening
import Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences
import Mettapedia.Machines.SourceStepSelection
import Mettapedia.Machines.CompilerRefusalReport
import Mettapedia.Machines.CollectionOfferScheduling
import Mettapedia.Machines.PreparedRefusalCache
import Mettapedia.Machines.NativeProjectionObservation
import Mettapedia.Machines.PreparedCallerStorage
import Mettapedia.Machines.NativeParentFusion
import Mettapedia.Machines.ConditionalContinuation
import Mettapedia.Machines.NativeCallReturn
import Mettapedia.Machines.OwnedBind
import Mettapedia.Machines.ExecutionControl
import Mettapedia.Machines.ContextualCBPV
import Mettapedia.Machines.CompilerDemandTrace
import Mettapedia.Machines.IntrinsicDispatch
import Mettapedia.Machines.InvocationResultDemand
import Mettapedia.Machines.UnificationWorklist
import Mettapedia.Machines.ContextualInvocation
import Mettapedia.Data.List.OrderedOccurrenceCursor
import Mettapedia.Machines.MatchIndexProjection
import Mettapedia.Machines.Cursor.GenerationalSharing
import Mettapedia.Machines.Cursor.NativeBorrowedReturn
import Mettapedia.Machines.PartialHashIndex
import Mettapedia.Machines.RegisterCode
import Mettapedia.Machines.PreparedComputation
import Mettapedia.Machines.SourceAccounting
import Mettapedia.Machines.CollectionDemand
import Mettapedia.Machines.Cursor.ScopedGraphLoan
import Mettapedia.Machines.CalleeAdmission
import Mettapedia.Machines.ContextualSourceAdmission
import Mettapedia.Machines.SourceCollection
import Mettapedia.Machines.SourceSchedulingBoundary
import Mettapedia.Machines.Cursor.BoundedTermLookup
import Mettapedia.Machines.SourceCase
import Mettapedia.Machines.HEInstructionControl
import Mettapedia.Machines.HEInstructionSource
import Mettapedia.Machines.CapturedBindingProjection
import Mettapedia.Machines.PreparedSyntax
import Mettapedia.Machines.SourcePlanPositions
import Mettapedia.Machines.FoldNativeCompletion
import Mettapedia.Machines.CalleeRefusalScope
import Mettapedia.Machines.NativeTailReturn
import Mettapedia.Machines.ParameterizedBodyEntry
import Mettapedia.Machines.CallerCursorJoin
import Mettapedia.Machines.InvocationSpanEntry
import Mettapedia.Machines.ClosedPatternRefutation
import Mettapedia.Machines.CompletedContextReturn
import Mettapedia.Machines.ResumptionClosure
import Mettapedia.Machines.PreparedCallerProjection
import Mettapedia.Machines.SourceWordAdmission
import Mettapedia.Machines.HEInstructionCompletion
import Mettapedia.Machines.OrderedHeadPlan
import Mettapedia.Machines.InvocationEntrySchedule
import Mettapedia.Machines.PackedPlanKey
import Mettapedia.Machines.LocalWorklistStorage
import Mettapedia.Machines.DispatchOperands
import Mettapedia.Machines.ScopedFirst
import Mettapedia.Logic.KernelFoundationManifest

/-!
# Foundations of the maintained execution models

The audit selects declarations by their recorded owning module, including
private and generated declarations. Every safe kernel declaration is checked
for transitive axioms in both its type and body. Only `propext`,
`Classical.choice` and `Quot.sound` are accepted. Compiler-only entries and
recognized unsafe runtime counterparts receive no mathematical proof credit.

The selected roots come from this file's actual direct imports. A module that
is also a dependency is audited once. The imported local-module inventory is
emitted separately for source/object identity receipts. These checks establish
foundations of the compiled environment, not native C correspondence or the
adequacy of a theorem's statement for its intended implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ExecutionAudit

open Lean Elab Command
open Mettapedia.Logic.KernelFoundationManifest

def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Fail on an actual primitive assumption, including an admitted body. -/
def requireAllowedAxioms (declaration : Name) (dependencies : Array Name) : MetaM Unit := do
  for dependency in dependencies do
    unless allowedAxioms.contains dependency do
      throwError "execution audit rejected {declaration}: nonstandard axiom {dependency}"

structure ModuleInventory where
  names : Array Name
  extras : Array Name
  exportOccurrences : Nat
  crossModuleExports : Nat
  deriving Inhabited

/-- Lazy equation helpers can be exported again by later importing modules.
Scan all import tables, assign by Lean's recorded owner and deduplicate names
before audit. A selected owner keeps helpers emitted from any imported table. -/
def collectInventories (roots : Array Name) : MetaM (Array ModuleInventory) := do
  let env ← getEnv
  let mut slots : Std.HashMap Nat Nat := {}
  for index in [:roots.size] do
    let some moduleIndex := env.getModuleIdx? roots[index]!
      | throwError "execution audit module is not imported: {roots[index]!}"
    slots := slots.insert moduleIndex.toNat index
  let mut names : Array NameSet := roots.map fun _ => {}
  let mut extras : Array NameSet := roots.map fun _ => {}
  let mut occurrences : Array Nat := roots.map fun _ => 0
  let mut cross : Array Nat := roots.map fun _ => 0
  for exportedFrom in [:env.header.moduleData.size] do
    let data := env.header.moduleData[exportedFrom]!
    for (entries, extra) in [(data.constNames, false), (data.extraConstNames, true)] do
      for name in entries do
        if let some owner := env.getModuleIdxFor? name then
          if let some slot := slots[owner.toNat]? then
            names := names.modify slot (·.insert name)
            occurrences := occurrences.modify slot (· + 1)
            if extra then extras := extras.modify slot (·.insert name)
            if owner.toNat != exportedFrom then cross := cross.modify slot (· + 1)
  return roots.mapIdx fun index _ =>
    ⟨names[index]!.toArray.qsort Name.lt, extras[index]!.toArray.qsort Name.lt,
      occurrences[index]!, cross[index]!⟩

structure OwnedSummary where
  moduleName : Name
  declarations : Nat
  checkedBodies : Nat
  theorems : Nat
  runtimeCounterparts : Array (Name × Name)
  compilerOnly : Array Name
  usedAxioms : Array Name
  exports : Nat
  crossExports : Nat

/-- Reuse the foundation manifest's safety and counterpart classification.
The trust input is the checked environment and module tables, not spelling or
source comments. A missing main kernel entry cannot look axiom-free. -/
def auditInventory (moduleName : Name) (inventory : ModuleInventory) : MetaM OwnedSummary := do
  let env ← getEnv
  let mut declarations := 0
  let mut bodies := 0
  let mut theorems := 0
  let mut counterparts := #[]
  let mut compilerOnly := #[]
  let mut axioms := #[]
  for name in inventory.names do
    let actualOwner := (env.getModuleIdxFor? name).bind (env.header.modules[·]?)
    unless actualOwner.any (·.module == moduleName) do
      throwError "execution audit ownership index mismatch: {moduleName} / {name}"
    if let some info := env.checked.get.find? name then
      if info.isUnsafe || info.isPartial then
        let some parent := runtimeCounterpart? env name
          | throwError "execution audit found an unpaired nonlogical implementation: {name}"
        counterparts := counterparts.push (name, parent)
      else
        let dependencies ← collectAxioms name
        requireAllowedAxioms name dependencies
        for dependency in dependencies do
          unless axioms.contains dependency do axioms := axioms.push dependency
        declarations := declarations + 1
        if hasCheckedBody info then bodies := bodies + 1
        if let .thmInfo _ := info then theorems := theorems + 1
    else if inventory.extras.contains name then
      compilerOnly := compilerOnly.push name
    else
      throwError "execution audit missing kernel declaration: {moduleName} / {name}"
  if bodies == 0 || theorems == 0 then
    throwError "execution audit root has no checked body/theorem coverage: {moduleName}"
  return ⟨moduleName, declarations, bodies, theorems, counterparts,
    compilerOnly, axioms.qsort Name.lt, inventory.exportOccurrences, inventory.crossModuleExports⟩

/-- The same owned-module check is available to isolated regression fixtures. -/
def auditOwnedModule (moduleName : Name) : MetaM OwnedSummary := do
  let inventory ← collectInventories #[moduleName]
  auditInventory moduleName inventory[0]!

def summaryJson (summary : OwnedSummary) : Json := Json.mkObj [
  ("module", .str summary.moduleName.toString),
  ("kernelDeclarations", toJson summary.declarations),
  ("checkedBodies", toJson summary.checkedBodies),
  ("theorems", toJson summary.theorems),
  ("exportOccurrences", toJson summary.exports),
  ("crossModuleExports", toJson summary.crossExports),
  ("duplicateExports", toJson (summary.exports - summary.declarations -
    summary.runtimeCounterparts.size - summary.compilerOnly.size)),
  ("runtimeCounterparts", .arr (summary.runtimeCounterparts.map fun pair =>
    Json.mkObj [("name", .str pair.1.toString), ("checkedParent", .str pair.2.toString)])),
  ("compilerOnly", .arr (summary.compilerOnly.map fun name => .str name.toString)),
  ("usedAxioms", .arr (summary.usedAxioms.map fun name => .str name.toString))
]

elab "#execution_foundation_audit" : command => do
  let env ← getEnv
  let excluded := #[`Init, `Mettapedia.Logic.KernelFoundationManifest]
  let roots := (env.header.imports.map (·.module)).filter (!excluded.contains ·)
    |>.toList.eraseDups |>.toArray.qsort Name.lt
  unless roots.size == 89 do
    throwError "execution audit expected 89 owned roots, found {roots.size}"
  let summaries ← liftTermElabM do
    let inventory ← collectInventories roots
    roots.mapIdxM fun index name => do
      let summary ← auditInventory name inventory[index]!
      pure summary
  let declarations := summaries.foldl (fun sum item => sum + item.declarations) 0
  let bodies := summaries.foldl (fun sum item => sum + item.checkedBodies) 0
  let theorems := summaries.foldl (fun sum item => sum + item.theorems) 0
  let counterparts := summaries.foldl (fun sum item => sum + item.runtimeCounterparts.size) 0
  let compilerOnly := summaries.foldl (fun sum item => sum + item.compilerOnly.size) 0
  let exports := summaries.foldl (fun sum item => sum + item.exports) 0
  let crossExports := summaries.foldl (fun sum item => sum + item.crossExports) 0
  let used := (summaries.flatMap (·.usedAxioms)).toList.eraseDups.toArray.qsort Name.lt
  let localModules := (env.header.moduleNames.filter (fun name => (`Mettapedia).isPrefixOf name)).push env.mainModule
    |>.toList.eraseDups |>.toArray.qsort Name.lt
  for name in localModules do logInfo m!"EXECUTION-THEORY-SOURCE {name}"
  for summary in summaries do logInfo m!"EXECUTION-THEORY-MODULE {(summaryJson summary).compress}"
  let result := Json.mkObj [
    ("schema", .str "execution-foundations-v1"),
    ("leanVersion", .str Lean.versionString),
    ("ownedModules", toJson roots.size),
    ("localSourceModules", toJson localModules.size),
    ("kernelDeclarations", toJson declarations),
    ("checkedBodies", toJson bodies),
    ("theorems", toJson theorems),
    ("runtimeCounterparts", toJson counterparts),
    ("compilerOnly", toJson compilerOnly),
    ("duplicateExports", toJson (exports - declarations - counterparts - compilerOnly)),
    ("crossModuleExports", toJson crossExports),
    ("allowedAxioms", .arr (allowedAxioms.map fun name => .str name.toString)),
    ("usedAxioms", .arr (used.map fun name => .str name.toString))
  ]
  logInfo m!"EXECUTION-THEORY-PASS {result.compress}"

end Mettapedia.Machines.ExecutionAudit

#execution_foundation_audit
