import Mettapedia.Machines.ScheduledRun
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

/-!
# Strict qualification of scheduled-run certificates

The audit selects declarations by source-module origin, covering private
helpers and generated kernel declarations as well as public theorem names.
Only exact generated recursive companions with safe total parents are treated
separately. No authored unsafe/partial definition or nonstandard logical axiom
is accepted.
-/

#print axioms Mettapedia.Machines.ScheduledRun.rotating_return_periodic
#print axioms Mettapedia.Machines.ScheduledRun.return_mod_lcm_periodic
#print axioms Mettapedia.Machines.ScheduledRun.return_mod_prefix_lcm_periodic
#print axioms Mettapedia.Machines.ScheduledRun.canonical_return_periodic
#print axioms Mettapedia.Machines.ScheduledRun.Controls.rotating_revisit_not_infinite
#print axioms Mettapedia.Machines.ScheduledRun.Controls.stale_phase_not_infinite
#print axioms Mettapedia.Machines.ScheduledRun.finite_infinite_detected
#print axioms Mettapedia.Machines.ScheduledRun.finite_reachable_infinite_detected
#print axioms Mettapedia.Machines.ScheduledRun.finite_run_never_claimed
#print axioms Mettapedia.Machines.ScheduledRun.claimsAt_sound
#print axioms Mettapedia.Machines.ScheduledRun.finite_monitor_reports_iff
#print axioms Mettapedia.Machines.ScheduledRun.finite_eventually_reports_iff
#print axioms Mettapedia.Machines.ScheduledRun.checkLoop_sound_of_entry
#print axioms Mettapedia.Machines.ScheduledRun.checkLoop_congr_next
#print axioms Mettapedia.Machines.ScheduledRun.checkLoop_reuse
#print axioms Mettapedia.Machines.ScheduledRun.finite_portfolio_reports_iff

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let root := `Mettapedia.Machines.ScheduledRun
  let modules := ([`Core, `Replay, `Periodicity, `Finite, `Controls, `PeriodTracker,
    `Monitor, `Detection, `Sharpness, `MonitorControls, `Certificates, `CertificateReuse,
    `CertificateControls, `LocalDetection, `LocalControls, `BoundedClock] : List Name).map
      (fun suffix => root ++ suffix)
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for moduleName in modules do
    unless environment.header.moduleNames.contains moduleName do
      throwError "Missing qualification module: {moduleName}"
  unless (← collectAxioms ``sorryAx).any (fun dependency => !allowed.contains dependency) do
    throwError "Proof-hole rejection control failed"
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
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
        | throwError "Missing generated-companion parent: {name}"
      if parentInfo.isUnsafe || parentInfo.isPartial then throwError "Invalid generated-companion parent: {name}"
      companions := companions + 1
      continue
    if let .axiomInfo _ := info then throwError "Added axiom: {name}"
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do throwError "Unexpected axiom {dependency} in {name}"
    declarations := declarations + 1
    if let .thmInfo _ := info then theorems := theorems + 1
  if declarations == 0 || theorems == 0 then throwError "Empty scheduled-run qualification"
  logInfo m!"Scheduled-run strict audit: {modules.length} modules; {declarations} safe logical declarations; {theorems} theorem constants; {companions} checked compiler companions; only propext, Classical.choice and Quot.sound"
