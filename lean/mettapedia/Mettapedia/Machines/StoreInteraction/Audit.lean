import Mettapedia.Machines.StoreInteraction
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut companions : Nat := 0
  for (name, info) in environment.constants.toList do
    if (`Mettapedia.Machines.StoreInteraction).isPrefixOf name then
      if info.isUnsafe then
        throwError "Unsafe declaration: {name}"
      if info.isPartial then
        let some parent := Compiler.isUnsafeRecName? name
          | throwError "Noncompiler partial declaration: {name}"
        let some parentInfo := environment.find? parent
          | throwError "Missing total parent for {name}"
        if parentInfo.isUnsafe || parentInfo.isPartial then
          throwError "Invalid parent for {name}"
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
  if declarations == 0 || theorems == 0 then
    throwError "Empty qualification"
  let anchors := [
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.round_serializable_iff,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.snapshot_refines_of_acyclic,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.serialOutcome_effect_iff_acyclic,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.no_double_take,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.every_fires_serializable_iff,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.executable_fusion_iff,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fusion_not_traceEq,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.TraceEq.answers_eq,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.static_covers,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.independent_of_staticApart,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Run.refines,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.await_fires,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.await_fires_of_stable,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.whenever_fires_often,
    `Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.kindIndex_noLostWakeup,
    `Mettapedia.Machines.Cursor.ReadScopeComposition.per_call_views_refine_nested,
    `Mettapedia.Machines.Cursor.ReadScopeComposition.stable_drain_agrees,
    `Mettapedia.Machines.Cursor.JoinOrderProfiles.fixed_join_bag_commutes,
    `Mettapedia.Machines.Cursor.ReadAdmissionProfiles.LibraryControls.library_stable_law_is_not_adaptive_equivalence,
    `Mettapedia.GSLT.OpenEnded.ChaoticIteration.schedule_independent]
  for name in anchors do
    let some (.thmInfo _) := environment.find? name
      | throwError "Missing theorem anchor: {name}"
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do
        throwError "Unexpected anchor axiom {dependency} in {name}"
  logInfo m!"Store-interaction qualification: {declarations} safe declarations, {theorems} theorem constants, {companions} compiler companions; {anchors.length} existing theorem anchors; only standard axioms"
