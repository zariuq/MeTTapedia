import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreAll
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

/-!
# Strict qualification of ask timing and set-store contracts

Declaration origins select the package, including private helpers and generated
declarations. Only exact compiler companions of safe total recursive definitions
are classified separately. The qualification rejects additional logical axioms,
authored unsafe or partial definitions, and proof-hole dependencies.
-/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let root := `Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
  let modules := ([`SetStore, `SetStoreStep, `SetStoreClosure, `SetStoreSyntax,
      `SetStoreFirings, `SetStoreLifting, `SetStoreReopening, `SetStoreFamilies,
      `SetStoreCompletion, `SetStoreOrderedBags, `SetStoreDisciplines, `SetStoreOutcomes,
      `SetStoreControls, `SetStoreOpenControls, `SetStoreDisciplineControls,
      `SetStoreAliasControls, `SetStoreGrowthControls, `SetStorePathControls,
      `SetStoreInvariance, `SetStoreAskTiming, `SetStoreTimedOutcomes,
      `SetStoreTimingControls, `SetStoreTimedPathControls, `SetStoreAll] : List Name).map (root ++ ·) ++
    ([`AskTiming, `AskTimingControls, `FirstOrderFreshFamily, `FirstOrderAskLicence] : List Name).map
      (fun suffix => root ++ `JointFirings ++ suffix) ++
    ([`AskTiming, `AskTimingInstances, `AskTimingControls] : List Name).map
      (fun suffix => root ++ `StepWeb ++ suffix)
  for moduleName in modules do
    unless environment.header.moduleNames.contains moduleName do
      throwError "Missing qualified module: {moduleName}"
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
  let anchors := ([`JointFirings.Bag.beforeTells_step,
    `JointFirings.Bag.beforeTells_iff_of_entailed_tells,
    `JointFirings.AskTimingControls.strict_inclusion,
    `JointFirings.AskTimingControls.mutual_before_refused,
    `JointFirings.AskTimingControls.Inconsistent.bag_refused,
    `JointFirings.AskTimingControls.MatchingOnly.before_is_not_own,
    `JointFirings.FirstOrderAskLicence.before_tells_iff_checked,
    `JointFirings.FirstOrderAskLicence.after_tells_iff_checked,
    `SetStore.readings_normalize, `SetStore.support_result_set_update,
    `SetStore.step_iff_occurrence, `SetStore.occurrence_step_or_stutter,
    `SetStore.firing_rename_observation, `SetStore.self_is_not_step,
    `SetStoreSyntax.actual_exists_terminal, `SetStoreSyntax.actual_no_infinite_run,
    `SetStoreSyntax.snapshot_iff_joint_of_no_takes, `SetStoreSyntax.exists_every_bag,
    `SetStoreSyntax.exists_maximal_complete_bag, `SetStoreSyntax.discipline_progress,
    `SetStoreSyntax.discipline_has_least_outcome, `SetStoreSyntax.completed_outcomes_agree,
    `JointFirings.Bag.AdmitsEveryBeforeTellsBy.keys_perm,
    `JointFirings.Bag.everyBeforeTellsBy_iff_of_entailed,
    `JointFirings.Bag.everyBeforeTellsBy_ordered_iff,
    `SetStoreSyntax.quantified_iff_of_no_tells,
    `SetStoreSyntax.quantified_has_least_outcome,
    `SetStoreSyntax.quantified_completed_outcomes_agree,
    `SetStoreTimingControls.distinct_before_tells_set_contracts,
    `SetStoreTimedPathControls.all_six_profiles_finish_at_paths,
    `SetStoreTimedPathControls.ambiguous_unique_refuses,
    `SetStoreOpenControls.positive_open_input_has_two_terminal_outcomes,
    `SetStoreDisciplineControls.unique_makes_progress, `SetStoreDisciplineControls.no_complete_unique_bag,
    `SetStoreControls.same_support_different_count,
    `SetStoreControls.a_duplicate_source_is_not_membership_removal,
    `SetStoreAliasControls.aliased_unknowns_refuse_distinct_values,
    `SetStoreAliasControls.independent_unknowns_allow_distinct_values,
    `SetStoreGrowthControls.grows, `SetStoreGrowthControls.finite_input_no_closed_carrier,
    `SetStorePathControls.all_six_profiles_finish_at_paths,
    `JointFirings.Synchronous.both_admitted, `JointFirings.Synchronous.no_run_reaches,
    `JointFirings.Shop.both_refused,
    `JointFirings.SymmetricMatches.finite_admitted_representatives,
    `JointFirings.SymmetricMatches.finite_ordered_representatives,
    `JointFirings.SymmetricMatches.resultModel_iff,
    `JointFirings.SymmetricMatches.Same.read_occurrences,
    `FirstOrderLicence.admits_iff_checked] : List Name).map (root ++ ·)
  for name in anchors do
    let some (.thmInfo _) := environment.find? name
      | throwError "Missing theorem anchor: {name}"
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do
        throwError "Unexpected anchor axiom {dependency} in {name}"
  if declarations == 0 || theorems == 0 || controls == 0 then
    throwError "Empty ask/set-store qualification"
  logInfo m!"CMR ask/set-store strict audit: {modules.length} modules; {declarations} safe logical declarations; {theorems} theorem constants ({controls} in control modules); {companions} checked compiler companions; {anchors.length} theorem anchors; only propext, Classical.choice and Quot.sound"
