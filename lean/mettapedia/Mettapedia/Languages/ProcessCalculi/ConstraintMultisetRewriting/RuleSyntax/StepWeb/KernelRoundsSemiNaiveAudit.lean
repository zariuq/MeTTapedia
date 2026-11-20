import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsSemiNaiveControls
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

/-! Declaration-origin qualification of the frontier construction and controls. -/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let root := `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb
  let modules := ([`KernelRoundsSemiNaive, `KernelRoundsSemiNaiveControls] : List Name).map (root ++ ·)
  for moduleName in modules do
    unless environment.header.moduleNames.contains moduleName do
      throwError "Missing frontier module: {moduleName}"
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let negative ← collectAxioms ``sorryAx
  unless negative.any (fun dependency => !allowed.contains dependency) do
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
        | throwError "Missing compiler companion parent: {name}"
      if parentInfo.isUnsafe || parentInfo.isPartial then
        throwError "Invalid compiler companion parent: {name}"
      unless parent == root ++ `KernelRounds.SemiNaive.rounds do
        throwError "Unexpected compiler companion: {name}"
      companions := companions + 1
      continue
    if let .axiomInfo _ := info then throwError "Added axiom: {name}"
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do throwError "Unexpected axiom {dependency} in {name}"
    declarations := declarations + 1
    if let .thmInfo _ := info then
      theorems := theorems + 1
      if origin.toString.endsWith "Controls" then controls := controls + 1
  let anchors := ([`round_known, `round_invariant, `rounds_eq_stage,
      `delta_empty_iff_fixed, `exists_finished, `every_run_eq_frontier,
      `exists_every_frontier_execution, `Controls.transitive_chain,
      `Controls.wrong_frontier_invalid, `Controls.finite_seed_never_stops] : List Name).map
    (fun suffix => root ++ `KernelRounds.SemiNaive ++ suffix)
  for anchor in anchors do
    let some (.thmInfo _) := environment.find? anchor
      | throwError "Missing frontier theorem: {anchor}"
  unless declarations > 0 do throwError "Frontier qualification omitted declarations"
  unless theorems ≥ 20 do throwError "Frontier qualification omitted theorems"
  unless controls ≥ 8 do throwError "Frontier qualification omitted controls"
  logInfo m!"Frontier audit: {modules.length} modules; {declarations} safe logical declarations; {theorems} theorem constants; {controls} controls; {companions} total-recursion compiler companions; {anchors.length} anchors; only the three standard Lean axioms"
