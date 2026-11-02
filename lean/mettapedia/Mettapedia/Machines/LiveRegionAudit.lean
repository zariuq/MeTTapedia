import Mettapedia.Machines.LiveRegionControls
import Mettapedia.Logic.KernelFoundationManifest

/-! Owner-module inventory for live admission, interference and the actual
word instance. Compiler runtime counterparts receive no proof credit. -/

#print axioms Mettapedia.Machines.Cursor.LiveAdmission.PartialWorker.advance_exact
#print axioms Mettapedia.Machines.Cursor.LiveAdmission.Planner.replay_exact
#print axioms Mettapedia.Machines.Cursor.LiveAdmission.Planner.cached_attempt_eq_live
#print axioms Mettapedia.Machines.Cursor.InterleavedRegions.history_exact
#print axioms Mettapedia.Machines.Cursor.InterleavedRegions.adaptive_schedule_exact
#print axioms Mettapedia.Machines.RegionDependencyStability.coexist_of_cross_footprints
#print axioms Mettapedia.Machines.LiveWordRegions.add_admitted_iff
#print axioms Mettapedia.Machines.LiveWordRegions.Renaming.worker_exact
#print axioms Mettapedia.Machines.LiveWordRegions.Controls.actual_dynamic_entry_exit_reentry

#foundation_manifest_module Mettapedia.Machines.LiveRegionAdmission
#foundation_manifest_module Mettapedia.Machines.InterleavedProtocolRegions
#foundation_manifest_module Mettapedia.Machines.RegionDependencyStability
#foundation_manifest_module Mettapedia.Machines.LiveWordRegions
#foundation_manifest_module Mettapedia.Machines.LiveRegionRenaming
#foundation_manifest_module Mettapedia.Machines.LiveRegionControls
