import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SolverSymmetry
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

/-!
# Strict qualification of the CMR solver/symmetry package

Declaration origins, rather than public namespace prefixes alone, select the
owned modules. Private helpers and generated kernel declarations are included.
Only exact compiler-generated recursive companions with safe total parents are
classified separately. Authored unsafe/partial definitions, added axioms and
nonstandard transitive logical axioms are rejected.
-/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let root := `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
  let joint := root ++ `RuleSyntax.JointFirings
  let modules := [root ++ `FirstOrderLicence, root ++ `FirstOrderLicenceControls,
    root ++ `RuleSyntax.FirstOrderLicence, `Mettapedia.Logic.LP.MutualListInstantiation] ++
    ([`MatchIdentity, `SymmetricMatches, `PatternAssignmentOrder, `SymmetricTransport,
      `SymmetricSemantics, `SymmetricFiringModels, `SymmetricFiringResults,
      `SymmetricPrincipalResults, `FreshResultNames, `SymmetricBatchSemantics,
      `SymmetricGivenValues, `SymmetricBatchResults, `SymmetricFinite, `MatchIdentityOrder,
      `SymmetricResources, `SymmetricOffers, `MemberCoordinates, `BagCoordinates,
      `FiniteMatchIdentity, `OrderedFinite, `SymmetricBagTransport, `SymmetricIncidence,
      `SymmetricAliases, `SymmetricReselection, `CanonicalMatches, `RelabelTransport,
      `SymmetricValueStates, `SymmetricBatchWords, `SymmetricBatchPrincipal,
      `SymmetricBatchResources, `SymmetricBatchValueStates, `SymmetricControls,
      `SymmetricOperationalControls, `SymmetricOpenControls, `OrderedMatchCompatibility] : List Name).map
        (fun suffix => joint ++ suffix)
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
    throwError "Empty solver/symmetry qualification"
  logInfo m!"CMR solver/symmetry strict audit: {modules.length} modules; {declarations} safe logical declarations; {theorems} theorem constants ({controls} in control modules); {companions} checked compiler companions; only propext, Classical.choice and Quot.sound"
