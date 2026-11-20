import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.All
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

/-!
# Strict declaration-origin qualification

The origin whitelist includes private helpers and generated kernel declarations
of every included theory/control module. Authored unsafe or partial definitions,
added axioms, proof holes and nonstandard transitive logical axioms are rejected.
Compiler-generated recursion companions require safe total parents. Qualification
of this package does not assert missing operational correspondence theorems.
-/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let root := `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
  let schemas : List Name :=
    [`Schema, `Opening, `Amalgamation, `Materialization,
     `Renaming, `QuantifierControls, `Regions, `Generalization,
     `AlphaKey, `AlphaControls, `AlphaRegions, `State,
     `Rule, `Selection, `Step, `Shared,
     `SharedAdmission, `SharedProjection, `SharedTransitions, `ApplicationSyntax,
     `ApplicationSemantics, `ReadModels, `RegionControls, `Substitution,
     `ApplicationSubstitution, `PrincipalTemplates, `PrincipalOutputs, `ApplicationMachine,
     `SelectedPatterns, `DataViews, `ApplicationReadings, `ApplicationResultReadings,
     `DataViewModels, `ApplicationCut, `ApplicationRunSound,
     `FreshNamespaces, `ApplicationSupport, `ApplicationOpening, `ApplicationCandidate,
     `ApplicationCandidateFresh, `ApplicationCandidateModels, `ApplicationCandidateAdmission,
     `ApplicationOneStep, `ApplicationStoreLaws,
     `ApplicationRetainedRuns, `ApplicationProtectedRuns, `ApplicationCompleteness,
     `ApplicationClosure, `ApplicationControls, `ApplicationRigidTerms,
     `ApplicationFamilies, `ApplicationFamilyModels, `ApplicationPairRuns,
     `ApplicationPairRounds, `ApplicationRoundStages, `ApplicationSaturation,
     `ApplicationSaturationFixed, `ApplicationSaturationControls,
     `ApplicationContextCost, `ApplicationContextControls, `AlphaSet, `HeldFreshNamespaces,
     `HeldCopyConsumer, `HeldReadConsumer, `HeldReadMaterializer, `HeldReadProtocol,
     `HeldReadControls, `HeldReadEncoding, `HeldReadDirectCandidate, `HeldReadDirectModels,
     `HeldReadDirectBridge, `HeldReadScopeReassociation, `HeldReadExtensionSum,
     `HeldReadStateScope, `HeldReadDatumSpan, `HeldReadFreshStaging, `HeldReadDirectControls,
     `HeldReadGenericSources, `HeldReadGenericFirings, `HeldReadGenericFresh,
     `HeldReadGenericModels, `HeldReadGenericResources, `HeldReadGenericSpan,
     `HeldReadGenericShapes, `HeldReadGenericAdmission, `HeldReadGenericExtensions,
     `HeldReadGenericProtocol, `LiveObservations, `HeldReadGenericAgreement,
     `ProtectedTwoStage, `ProtectedTwoStageCoherence, `HeldReadMixedSourceAdapter,
     `HeldReadMixedSourceAdmission, `HeldReadProtected, `HeldReadMixedSourceResults,
     `HeldReadMixedSourceExecution, `HeldReadGenericControls, `LiveObservationControls,
     `HeldReadProtectedSource]
  let kernels : List Name :=
    [`KernelRoundsStages, `KernelRoundsStep, `KernelRoundsDepth, `KernelRoundsFinite,
     `KernelRoundsControls, `KernelRoundsOpenControls, `KernelRoundsTiming]
  let modules := schemas.map (fun suffix => root ++ `SchematicRows ++ suffix) ++
    kernels.map (fun suffix => root ++ `StepWeb ++ suffix)
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for moduleName in modules do
    unless environment.header.moduleNames.contains moduleName do
      throwError "Missing qualified module: {moduleName}"
  let negative ← collectAxioms ``sorryAx
  unless negative.any (fun dependency => !allowed.contains dependency) do
    throwError "The proof-hole rejection control failed"
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut controls : Nat := 0
  let mut companions : Nat := 0
  for (name, info) in environment.constants.toList do
    let some index := environment.getModuleIdxFor? name | continue
    let origin := environment.header.moduleNames[index.toNat]!
    unless modules.contains origin do continue
    if name.toString.contains "_wanted" then
      throwError "Wishlist declaration: {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration: {name}"
    if info.isPartial then
      let some parent := Compiler.isUnsafeRecName? name
        | throwError "Authored partial declaration: {name}"
      let some parentInfo := environment.find? parent
        | throwError "Missing compiler companion parent: {name}"
      if parentInfo.isUnsafe || parentInfo.isPartial then
        throwError "Invalid compiler companion parent: {name}"
      companions := companions + 1
      continue
    if let .axiomInfo _ := info then
      throwError "Added axiom: {name}"
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {name}"
    declarations := declarations + 1
    if let .thmInfo _ := info then
      theorems := theorems + 1
      if origin.toString.endsWith "Controls" then controls := controls + 1
  if declarations == 0 || theorems == 0 || controls == 0 then
    throwError "Empty schematic-row/kernel-round qualification"
  logInfo m!"Schematic-row/kernel-round strict audit: {modules.length} modules; {declarations} safe logical declarations; {theorems} theorem constants ({controls} in control modules); {companions} checked compiler companions; only propext, Classical.choice and Quot.sound"

