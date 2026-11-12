import Mettapedia.Machines.TIsa.Core
import Mettapedia.Machines.TIsa.FoundationAudit

/-! Kernel dependency audit for the native-profile interfaces. -/

#print axioms Mettapedia.Machines.TIsa.RuleTable.Plan.run_eq_some_iff
#print axioms Mettapedia.Machines.TIsa.RuleTable.Rule.compile_iff
#print axioms Mettapedia.Machines.TIsa.RuleTable.Rule.checkPlan_correct
#print axioms Mettapedia.Machines.TIsa.Scalar.compare_boolean
#print axioms Mettapedia.Machines.TIsa.Cells.scalar_update_realized
#print axioms Mettapedia.Machines.TIsa.Cells.scalar_update_reflected
#print axioms Mettapedia.Machines.TIsa.Cells.fire_preserves_frame
#print axioms Mettapedia.Machines.TIsa.Hosted.rewrite_iff_scalar_update
#print axioms Mettapedia.Machines.TIsa.Hosted.nativeDiamond_iff_scalar_update
#print axioms Mettapedia.Machines.TIsa.ByteRange.access?_no_wrap
#print axioms Mettapedia.Machines.TIsa.readBytes_after_write
#print axioms Mettapedia.Machines.TIsa.CellEffects.profile_rewrite_iff
#print axioms Mettapedia.Machines.TIsa.Control.program_rewrite_iff
#print axioms Mettapedia.Machines.TIsa.pack_unpack64
#print axioms Mettapedia.Machines.TIsa.word_read_after_write
#print axioms Mettapedia.Machines.TIsa.low32_extend32
#print axioms Mettapedia.Machines.TIsa.checkedAddress_no_wrap
#print axioms Mettapedia.Machines.TIsa.checkedAddress_in_capability
#print axioms Mettapedia.Machines.TIsa.Registers.Placement.check_iff
#print axioms Mettapedia.Machines.TIsa.Registers.Placement.resolve_injective
#print axioms Mettapedia.Machines.TIsa.Registers.update_related
#print axioms Mettapedia.Machines.TIsa.Registers.canonical_admitted
#print axioms Mettapedia.Machines.TIsa.Layout.fields_separate
#print axioms Mettapedia.Machines.TIsa.NativeBoundary.layouts_admitted
#print axioms Mettapedia.Machines.TIsa.Memory.access?_no_wrap
#print axioms Mettapedia.Machines.TIsa.Memory.access?_inside
#print axioms Mettapedia.Machines.TIsa.Memory.Store.preserves_outside
#print axioms Mettapedia.Machines.TIsa.Memory.program_rewrite_iff
#print axioms Mettapedia.Machines.TIsa.RegisterProfile.scalarWrite?_refines
#print axioms Mettapedia.Machines.TIsa.RegisterProfile.Write.source_live
#print axioms Mettapedia.Machines.TIsa.RegisterProfile.lowerWrites?_source
#print axioms Mettapedia.Machines.TIsa.ScalarType.normalize_valid
#print axioms Mettapedia.Machines.TIsa.typed_normalized_update
#print axioms Mettapedia.Machines.TIsa.Control.Branch.realized
#print axioms Mettapedia.Machines.TIsa.Control.Branch.target?_iff
#print axioms Mettapedia.Machines.TIsa.Control.counter_increment_no_wrap
#print axioms Mettapedia.Machines.TIsa.Control.Loop.latch_decreases
#print axioms Mettapedia.Machines.TIsa.Control.Loop.latch_wellFounded
#print axioms Mettapedia.Machines.TIsa.RelativeBranch.encoded_target_exact
#print axioms Mettapedia.Machines.TIsa.Control.edgeProgram_rewrite_iff
#print axioms Mettapedia.Machines.TIsa.RegisterBlock.run_realized
#print axioms Mettapedia.Machines.TIsa.RegisterBlock.head_step_iff
#print axioms Mettapedia.Machines.TIsa.Admission.admitted_carrier_iff
#print axioms Mettapedia.Machines.TIsa.RegisterBlock.completion_iff
#print axioms Mettapedia.Machines.TIsa.RegisterBlock.source_completion_iff
#print axioms Mettapedia.Machines.TIsa.RegisterProfile.partial_initialization_live
#print axioms Mettapedia.Machines.TIsa.Framing.profile_frame_inert
#print axioms Mettapedia.Machines.TIsa.Framing.profile_fires_frame_iff
#print axioms Mettapedia.Machines.TIsa.Framing.profile_safe_frame
#print axioms Mettapedia.Machines.TIsa.Funding.Grade.of?_isSome_iff
#print axioms Mettapedia.Machines.TIsa.Funding.paid_no_wrap
#print axioms Mettapedia.Machines.TIsa.Funding.available_sub_iff
#print axioms Mettapedia.Machines.TIsa.Funding.paid_monotone
#print axioms Mettapedia.Machines.TIsa.Funding.zero_allowance
#print axioms Mettapedia.Machines.TIsa.Funding.Gate.exhausted_keeps_receipt
#print axioms Mettapedia.Machines.TIsa.Funding.Gate.profile_rewrite_iff
#print axioms Mettapedia.Machines.TIsa.FundingTrace.complete_iff
#print axioms Mettapedia.Machines.TIsa.FundingTrace.run_append
#print axioms Mettapedia.Machines.TIsa.FundingTrace.no_complete_of_cost_overflow
#print axioms Mettapedia.Machines.TIsa.FundingTrace.two_frontiers
#print axioms Mettapedia.Machines.TIsa.FundingTrace.Controls.merging_changes_exhaustion
#print axioms Mettapedia.Machines.TIsa.FundingTrace.Controls.nested_payment_trace_cannot_complete
#print axioms Mettapedia.Machines.TIsa.Registers.scratch_apart
#print axioms Mettapedia.Machines.TIsa.Registers.write_scratch_preserves
#print axioms Mettapedia.Machines.TIsa.Registers.write_logical_related

#tisa_foundations
