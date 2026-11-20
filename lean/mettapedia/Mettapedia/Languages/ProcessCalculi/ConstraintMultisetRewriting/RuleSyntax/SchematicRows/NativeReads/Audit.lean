import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.All
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

/-! # Strict declaration-origin audit for the native-read theory package -/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let root := `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads
  let names : List Name :=
    [`Enumeration, `RigidIndex, `FrameFilter, `SchematicIndex,
     `BinaryCut, `BinaryCost, `HeadRanges, `RangeOrder, `NativeHeadIndex,
     `RegionFilter, `ConflictCores, `OccurrenceKey, `BoundedCodec, `BorrowedRoots, `BorrowedViews,
     `CursorProtocol, `Boundary, `LateFailure, `RegisteredLifetime, `SourceStorage, `Promotion, `StorageExecution,
     `TakeValidity, `DeadAlternatives, `ContextualIndex, `QueryProjection,
     `BorrowedQuery, `JoinCosts, `IdentityCosts, `IndexControls,
     `LifetimeControls, `PhysicalControls, `BoundaryControls, `BorrowedQueryControls, `ConflictControls]
  let modules := names.map (root ++ ·)
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for moduleName in modules do
    unless environment.header.moduleNames.contains moduleName do
      throwError "Missing audited module: {moduleName}"
  let rejection ← collectAxioms ``sorryAx
  unless rejection.any (fun dependency => !allowed.contains dependency) do
    throwError "Proof-hole rejection control failed"
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut controls : Nat := 0
  let mut companions : Nat := 0
  for (name, info) in environment.constants.toList do
    let some index := environment.getModuleIdxFor? name | continue
    let origin := environment.header.moduleNames[index.toNat]!
    unless modules.contains origin do continue
    if name.toString.contains "_wanted" then throwError "Wishlist declaration: {name}"
    if info.isUnsafe then throwError "Unsafe declaration: {name}"
    if info.isPartial then
      let some parent := Compiler.isUnsafeRecName? name
        | throwError "Authored partial declaration: {name}"
      let some parentInfo := environment.find? parent
        | throwError "Missing recursion companion parent: {name}"
      if parentInfo.isUnsafe || parentInfo.isPartial then
        throwError "Unsafe or partial recursion parent: {parent}"
      companions := companions + 1
      continue
    if let .axiomInfo _ := info then throwError "Added axiom: {name}"
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {name}"
    declarations := declarations + 1
    if let .thmInfo _ := info then
      theorems := theorems + 1
      if origin.toString.endsWith "Controls" then controls := controls + 1
  if declarations == 0 || theorems == 0 || controls == 0 then
    throwError "Empty native-read qualification"
  logInfo m!"Native-read strict audit: {modules.length} modules; {declarations} safe logical declarations; {theorems} theorem constants ({controls} in controls); {companions} checked safe-parent compiler companions; only propext, Classical.choice and Quot.sound"
