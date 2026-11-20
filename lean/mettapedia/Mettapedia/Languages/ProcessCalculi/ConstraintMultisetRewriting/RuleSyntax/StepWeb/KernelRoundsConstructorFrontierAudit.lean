import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsConstructorFrontier
import Lean.Util.CollectAxioms

/-! Strict declaration-origin qualification of constructor frontier filtering. -/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let root := `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb
  let origin := root ++ `KernelRoundsConstructorFrontier
  unless environment.header.moduleNames.contains origin do
    throwError "Missing constructor-frontier model"
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let negative ← collectAxioms ``sorryAx
  unless negative.any (fun dependency => !allowed.contains dependency) do
    throwError "Proof-hole rejection control failed"
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut controls : Nat := 0
  for (name, info) in environment.constants.toList do
    let some index := environment.getModuleIdxFor? name | continue
    unless environment.header.moduleNames[index.toNat]! == origin do continue
    if name.toString.contains "_wanted" then throwError "Wishlist declaration: {name}"
    if info.isUnsafe || info.isPartial then throwError "Unsafe or partial declaration: {name}"
    if let .axiomInfo _ := info then throwError "Added axiom: {name}"
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do throwError "Unexpected axiom {dependency} in {name}"
    declarations := declarations + 1
    if let .thmInfo _ := info then
      theorems := theorems + 1
      if name.toString.contains ".Controls." then controls := controls + 1
  let anchors := ([`substitute_head, `candidate_of_new_read, `candidate_of_hot,
      `heads_eq, `round_eq, `round_known, `cold_not_hot,
      `Controls.empty_kept, `Controls.unknown_kept,
      `Controls.same_constructor_kept, `Controls.different_constructor_cold,
      `Controls.changed_subtree_keeps_constructor] : List Name).map
    (fun suffix => root ++ `KernelRounds.ConstructorFrontier ++ suffix)
  for anchor in anchors do
    let some (.thmInfo _) := environment.find? anchor
      | throwError "Missing constructor frontier theorem: {anchor}"
  unless declarations > 0 && theorems ≥ 12 && controls ≥ 5 do
    throwError "Incomplete constructor frontier qualification"
  logInfo m!"Constructor frontier audit: {declarations} safe declarations; {theorems} theorem constants; {controls} controls; {anchors.length} anchors; only the three standard Lean axioms"
