import Mettapedia.Machines.Supercompilation.DrivingControls
import Mettapedia.ProbabilityTheory.BayesianNetworks.GradedFactorChain
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSpecializationControls

/-! # Foundation audit for guarded driving and its two semantic clients -/

open Mettapedia.Machines
open Mettapedia.Machines.Supercompilation
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

#print axioms ReadOnlySpecialization.Residual.tryRun_sound
#print axioms ReadOnlySpecialization.restore_records_reads
#print axioms ReadOnlySpecialization.restore_drive
#print axioms ReadOnlySpecialization.drive_agrees
#print axioms ReadOnlySpecialization.drive_reads_from_source
#print axioms ReadOnlySpecialization.drive_reads_le
#print axioms ReadOnlySpecialization.drive_sound_of_stamps
#print axioms Graph.compile_size_le
#print axioms Graph.compile_nodup
#print axioms dispatch_exact
#print axioms ordered_dispatch_eq
#print axioms resume_exact
#print axioms dispatch_guard_eval
#print axioms Controls.loop_folds_and_repeats_survive
#print axioms Controls.live_suffix_is_executed
#print axioms Controls.same_bag_different_order_is_stale
#print axioms Controls.equal_memory_cannot_authorize_other_program
#print axioms Controls.filling_an_absence_invalidates
#print axioms Controls.budget_cut_resumes_current_configuration
#print axioms Controls.capture_rejects_wrong_key
#print axioms Controls.capture_still_checks_values
#print axioms Controls.duplicate_effects_and_stale_order
#print axioms Controls.once_uses_the_live_order
#print axioms GradedFactorChain.contract_eq
#print axioms GradedFactorChain.refresh_prepare
#print axioms GradedFactorChain.refreshed_pathMass
#print axioms GradedFactorChain.specialize_left
#print axioms GradedFactorChain.stale_output_accumulates
#print axioms NativeTypeSpecialization.prepared_trace
#print axioms NativeTypeSpecialization.prepared_answer
#print axioms NativeTypeSpecialization.closure_stays_live
#print axioms NativeTypeSpecialization.changed_annotation_declines
