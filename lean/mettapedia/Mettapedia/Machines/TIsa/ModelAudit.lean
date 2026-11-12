import Mettapedia.Machines.TIsa.Audit
import Mettapedia.Machines.TIsa.RV64Model
import Mettapedia.Machines.TIsa.ImportedTheory
import Mettapedia.Machines.TIsa.ImportedBoundary
import Mettapedia.Machines.TIsa.ImportedImages
import Mettapedia.Machines.TIsa.ImportedP1
import Mettapedia.Machines.TIsa.X86RegisterRefinement
import Mettapedia.Machines.TIsa.X86RegisterEncoding
import Mettapedia.Machines.TIsa.X86Move
import Mettapedia.Machines.TIsa.X86OpcodeDispatch
import Mettapedia.Machines.TIsa.X86Prefix
import Mettapedia.Machines.TIsa.X86FetchMemory
import Mettapedia.Machines.TIsa.X86EffectiveFetch
import Mettapedia.Machines.TIsa.X86InstructionFetch
import Mettapedia.Machines.TIsa.X86ResourceCopy
import Mettapedia.Machines.TIsa.X86MovCapture
import Mettapedia.Machines.TIsa.X86Alu
import Mettapedia.Machines.TIsa.X86LegacyFetch
import Mettapedia.Machines.TIsa.X86Flags
import Mettapedia.Machines.TIsa.X86Arithmetic
import Mettapedia.Machines.TIsa.X86ResourceBinary
import Mettapedia.Machines.TIsa.X86BinCapture
import Mettapedia.Machines.TIsa.X86Execution
import Mettapedia.Machines.TIsa.X86BinBlock
import Mettapedia.Machines.TIsa.SailRange
import Mettapedia.Machines.TIsa.X86ReadWords
import Mettapedia.Machines.TIsa.X86FrameLoad
import Mettapedia.Machines.TIsa.X86FrameLoadCapture
import Mettapedia.Machines.TIsa.X86DwordLoad
import Mettapedia.Machines.TIsa.X86SubImmediate
import Mettapedia.Machines.TIsa.X86P1LoadBounds
import Mettapedia.Machines.TIsa.X86P1LoadCapture
import Mettapedia.Machines.TIsa.X86P1TagCompare
import Mettapedia.Machines.TIsa.X86ConditionByte
import Mettapedia.Machines.TIsa.X86P1CompareCapture
import Mettapedia.Machines.TIsa.X86P1IfCapture
import Mettapedia.Machines.TIsa.X86P1RefusedCapture
import Mettapedia.Machines.TIsa.NativeRefinement
import Mettapedia.Machines.TIsa.X86CopyBlock
import Mettapedia.Machines.TIsa.X86BlockCompiler
import Mettapedia.Machines.TIsa.X86WordLibrary
import Mettapedia.Machines.TIsa.X86LogicalFlags
import Mettapedia.Machines.TIsa.X86Comparison
import Mettapedia.Machines.TIsa.X86BranchCondition
import Mettapedia.Machines.TIsa.X86NearBranch
import Mettapedia.Machines.TIsa.X86TwoByteDispatch
import Mettapedia.Machines.TIsa.X86EscapeFetch
import Mettapedia.Machines.TIsa.NativeBranchProfile
import Mettapedia.Machines.TIsa.X86UnconditionalJump
import Mettapedia.Machines.TIsa.X86StateFrame
import Mettapedia.Machines.TIsa.X86WriteWords
import Mettapedia.Machines.TIsa.X86FrameIncrement
import Mettapedia.Machines.TIsa.NativeFuelProfile
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86CodePlacement
import Mettapedia.Machines.TIsa.NativeFuelRefinement
import Mettapedia.Machines.TIsa.X86FueledBin
import Mettapedia.Machines.TIsa.NativeFueledBin
import Mettapedia.Machines.TIsa.X86FrameStore
import Mettapedia.Machines.TIsa.X86OutcomeLoad
import Mettapedia.Machines.TIsa.X86FailureHandler
import Mettapedia.Machines.TIsa.X86ReturnPath
import Mettapedia.Machines.TIsa.NativeFailureProfile
import Mettapedia.Machines.TIsa.NativeFailureRefinement
import Mettapedia.Machines.TIsa.NativeExhaustion
import Mettapedia.Machines.TIsa.X86PlainFetch
import Mettapedia.Machines.TIsa.X86Stack
import Mettapedia.Machines.TIsa.X86Epilogue
import Mettapedia.Machines.TIsa.X86Prologue
import Mettapedia.Machines.TIsa.X86CallWrapper
import Mettapedia.Machines.TIsa.X86FundCall
import Mettapedia.Machines.TIsa.NativeEpilogueRefinement
import Mettapedia.Machines.TIsa.X86Symbolic
import Mettapedia.Machines.TIsa.X86Funding

/-! The architecture adapter and actual native imports join the dependency audit. -/

#tisa_foundations

#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.frame_reads
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.changed_register_not_inherited
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.fund_remaining
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.realizes_charge
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.paid_wrong_target
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.exhausted_no_early_payment
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.sample_input
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.sample_paid
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.sample_exhaustion_refuses_payment
#print axioms Mettapedia.Machines.TIsa.X86Funding.Capture.captured_block_checked
#print axioms Mettapedia.Machines.TIsa.X86Funding.Capture.changed_branch_refused
#print axioms Mettapedia.Machines.TIsa.X86Funding.Capture.window_from_image
#print axioms Mettapedia.Machines.TIsa.X86Funding.Capture.realizes_charge
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.symbolic_mov
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.symbolic_changed_destination
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.symbolic_mov32
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.two_moves
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.add_wraps
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.altered_modrm_refuses_original_answer
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.missing_byte
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.captured_mov
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.symbolic_store_width
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.store_then_load
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.big_endian_refused
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.subtract_memory
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.symbolic_grade
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.wrong_grade_refused

#print axioms Mettapedia.Machines.TIsa.RV64Model.mul_agrees
#print axioms Mettapedia.Machines.TIsa.RV64Model.shl_agrees
#print axioms Mettapedia.Machines.TIsa.RV64Model.slt_agrees
#print axioms Mettapedia.Machines.TIsa.RV64Model.addw_agrees
#print axioms Mettapedia.Machines.TIsa.X86RegisterRefinement.read_gpr_exact
#print axioms Mettapedia.Machines.TIsa.X86RegisterRefinement.write_gpr_exact
#print axioms Mettapedia.Machines.TIsa.X86RegisterRefinement.wr32_exact
#print axioms Mettapedia.Machines.TIsa.X86RegisterRefinement.write_logical_represents
#print axioms Mettapedia.Machines.TIsa.X86RegisterRefinement.put_scratch_represents
#print axioms Mettapedia.Machines.TIsa.X86RegisterRefinement.put_flags
#print axioms Mettapedia.Machines.TIsa.X86RegisterEncoding.source_register
#print axioms Mettapedia.Machines.TIsa.X86RegisterEncoding.destination_register
#print axioms Mettapedia.Machines.TIsa.Memory.Load.reads_byte
#print axioms Mettapedia.Machines.TIsa.SailInteger.half_abs_decreases
#print axioms Mettapedia.Machines.TIsa.X86Memory.read_one
#print axioms Mettapedia.Machines.TIsa.X86Move.register64
#print axioms Mettapedia.Machines.TIsa.X86Move.register64_three_bytes
#print axioms Mettapedia.Machines.TIsa.X86Move.Controls.altered_rex_refuses_original_answer
#print axioms Mettapedia.Machines.TIsa.X86OpcodeDispatch.move_register64
#print axioms Mettapedia.Machines.TIsa.X86OpcodeDispatch.register64_three_bytes
#print axioms Mettapedia.Machines.TIsa.X86OpcodeDispatch.locked_move_refused
#print axioms Mettapedia.Machines.TIsa.X86Prefix.unfold_original
#print axioms Mettapedia.Machines.TIsa.X86Prefix.unique
#print axioms Mettapedia.Machines.TIsa.X86Prefix.Controls.zero_count_refused
#print axioms Mettapedia.Machines.TIsa.X86Prefix.Controls.excessive_count_refused
#print axioms Mettapedia.Machines.TIsa.X86FetchMemory.rb_one_unfold
#print axioms Mettapedia.Machines.TIsa.X86FetchMemory.rb_one_exact
#print axioms Mettapedia.Machines.TIsa.X86FetchMemory.rb_one_missing
#print axioms Mettapedia.Machines.TIsa.X86FetchMemory.Controls.wrong_opcode_refused
#print axioms Mettapedia.Machines.TIsa.X86FetchMemory.Controls.missing_opcode
#print axioms Mettapedia.Machines.TIsa.X86EffectiveFetch.effective_read_uses_rb
#print axioms Mettapedia.Machines.TIsa.X86EffectiveFetch.effective_read_exact
#print axioms Mettapedia.Machines.TIsa.X86EffectiveFetch.effective_read_missing
#print axioms Mettapedia.Machines.TIsa.X86EffectiveFetch.Controls.wrong_opcode_refused
#print axioms Mettapedia.Machines.TIsa.X86EffectiveFetch.Controls.missing_opcode
#print axioms Mettapedia.Machines.TIsa.X86PrefixRead.rex_then_opcode
#print axioms Mettapedia.Machines.TIsa.X86PrefixRead.Controls.wrong_rex_refused
#print axioms Mettapedia.Machines.TIsa.X86InstructionFetch.fetch_to_dispatch
#print axioms Mettapedia.Machines.TIsa.X86InstructionFetch.fetch_register64
#print axioms Mettapedia.Machines.TIsa.X86InstructionFetch.Controls.step_mov
#print axioms Mettapedia.Machines.TIsa.X86InstructionFetch.Controls.altered_modrm_refuses_original_answer
#print axioms Mettapedia.Machines.TIsa.X86ResourceCopy.fetched_copy_refines
#print axioms Mettapedia.Machines.TIsa.X86ResourceCopy.fetched_scratch_copy_preserves
#print axioms Mettapedia.Machines.TIsa.X86ResourceCopy.copy_reflected
#print axioms Mettapedia.Machines.TIsa.X86ResourceCopy.copy_self_fire
#print axioms Mettapedia.Machines.TIsa.X86ResourceCopy.Controls.wrong_copy_result_refused
#print axioms Mettapedia.Machines.TIsa.X86MovCapture.every_output_exact
#print axioms Mettapedia.Machines.TIsa.X86MovCapture.captured_code_fields
#print axioms Mettapedia.Machines.TIsa.X86MovCapture.altered_prefix_rejected
#print axioms Mettapedia.Machines.TIsa.X86MovCapture.captured_copy_refines
#print axioms Mettapedia.Machines.TIsa.ImportedImages.hosting_inventory_exact
#print axioms Mettapedia.Machines.TIsa.ImportedImages.stale_four_carrier_inventory_rejected
#print axioms X86Registers.Functions.logcount_int
#print axioms Mettapedia.Machines.TIsa.X86Alu.add_executes
#print axioms Mettapedia.Machines.TIsa.X86Alu.sub_executes
#print axioms Mettapedia.Machines.TIsa.X86Alu.or_value
#print axioms Mettapedia.Machines.TIsa.X86Alu.and_value
#print axioms Mettapedia.Machines.TIsa.X86Alu.xor_value
#print axioms Mettapedia.Machines.TIsa.X86Alu.Controls.wrong_add_result_refused
#print axioms Mettapedia.Machines.TIsa.X86Alu.add_executes_defined
#print axioms Mettapedia.Machines.TIsa.X86Alu.sub_executes_defined
#print axioms Mettapedia.Machines.TIsa.X86LegacyFetch.checkOpcode_iff
#print axioms Mettapedia.Machines.TIsa.X86LegacyFetch.fetch_to_dispatch
#print axioms Mettapedia.Machines.TIsa.X86Flags.write_defined_flags
#print axioms Mettapedia.Machines.TIsa.X86Flags.write_missing_flags
#print axioms Mettapedia.Machines.TIsa.X86Flags.putFlags_gpr
#print axioms Mettapedia.Machines.TIsa.X86Flags.putFlags_represents
#print axioms Mettapedia.Machines.TIsa.X86Flags.Controls.clearing_control_refused
#print axioms Mettapedia.Machines.TIsa.X86Arithmetic.register64
#print axioms Mettapedia.Machines.TIsa.X86Arithmetic.fetched_register64
#print axioms Mettapedia.Machines.TIsa.X86Arithmetic.Controls.fetched_alias_add
#print axioms Mettapedia.Machines.TIsa.X86Arithmetic.Controls.altered_opcode_refuses_original_answer
#print axioms Mettapedia.Machines.TIsa.X86ResourceBinary.realized
#print axioms Mettapedia.Machines.TIsa.X86ResourceBinary.reflected
#print axioms Mettapedia.Machines.TIsa.X86ResourceBinary.fetched_inplace_refines
#print axioms Mettapedia.Machines.TIsa.X86ResourceBinary.Controls.wrong_result_refused
#print axioms Mettapedia.Machines.TIsa.X86BinCapture.every_output_exact
#print axioms Mettapedia.Machines.TIsa.X86BinCapture.captured_middle_executes
#print axioms Mettapedia.Machines.TIsa.X86BinCapture.altered_opcode_refused
#print axioms Mettapedia.Machines.TIsa.X86Execution.rebase
#print axioms Mettapedia.Machines.TIsa.X86Execution.three_steps_deterministic
#print axioms Mettapedia.Machines.TIsa.X86Execution.Controls.omitted_write_refused
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.captured_refines
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.finished_frame
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.captured_wrong_answer_refused
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.Controls.captured_add_three_steps
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.Controls.changed_opcode_refuses_add_answer
#print axioms Mettapedia.Machines.TIsa.SailRange.forIn_foldlM
#print axioms Mettapedia.Machines.TIsa.SailRange.Controls.iteration_error_stops
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.rb_fold
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.rb_word_exact
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.rb_dword_exact
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.load_word_exact
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.signed_displacement_exact
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.Controls.missing_high_byte_refused
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.Controls.zero_extended_negative_displacement_refused
#print axioms Mettapedia.Machines.TIsa.X86FrameLoad.effective_disp32
#print axioms Mettapedia.Machines.TIsa.X86FrameLoad.fetched_frame
#print axioms Mettapedia.Machines.TIsa.X86FrameLoadCapture.every_sample_checked
#print axioms Mettapedia.Machines.TIsa.X86FrameLoadCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86FrameLoadCapture.changed_register_byte_refused
#print axioms Mettapedia.Machines.TIsa.X86FrameLoadCapture.changed_offset_byte_refused
#print axioms Mettapedia.Machines.TIsa.X86FrameLoadCapture.Controls.captured_budget_load
#print axioms Mettapedia.Machines.TIsa.X86FrameLoadCapture.Controls.changed_field_refuses_budget_answer
#print axioms Mettapedia.Machines.TIsa.X86LogicalFlags.merged_zero
#print axioms Mettapedia.Machines.TIsa.X86LogicalFlags.write_logical_flags
#print axioms Mettapedia.Machines.TIsa.X86Comparison.fetched_compare_observes
#print axioms Mettapedia.Machines.TIsa.X86Comparison.fetched_test_observes
#print axioms Mettapedia.Machines.TIsa.X86Comparison.Controls.compare_unsigned_high_bit
#print axioms Mettapedia.Machines.TIsa.X86Comparison.Controls.changed_opcode_refuses_compare_carry
#print axioms Mettapedia.Machines.TIsa.X86BranchCondition.compare_then_above_equal
#print axioms Mettapedia.Machines.TIsa.X86BranchCondition.test_then_zero
#print axioms Mettapedia.Machines.TIsa.X86BranchCondition.Controls.altered_condition_refuses_original_answer
#print axioms Mettapedia.Machines.TIsa.X86BranchCondition.Controls.missing_flags_refused
#print axioms Mettapedia.Machines.TIsa.X86NearBranch.handler
#print axioms Mettapedia.Machines.TIsa.X86NearBranch.Controls.backward_taken
#print axioms Mettapedia.Machines.TIsa.X86TwoByteDispatch.decode_to_branch
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.fetched_branch
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.Controls.above_excludes_equality
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.Controls.changed_displacement_refuses_forward_target
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.Controls.changed_condition_refuses_taken_target
#print axioms Mettapedia.Machines.TIsa.NativeBranchProfile.every_imported_image_supported
#print axioms Mettapedia.Machines.TIsa.NativeBranchProfile.conditional_bytes
#print axioms Mettapedia.Machines.TIsa.NativeBranchProfile.unconditional_bytes
#print axioms Mettapedia.Machines.TIsa.X86UnconditionalJump.fetched_jump
#print axioms Mettapedia.Machines.TIsa.X86UnconditionalJump.Controls.changed_displacement_refuses_forward_target
#print axioms Mettapedia.Machines.TIsa.X86StateFrame.Frame.trans
#print axioms Mettapedia.Machines.TIsa.X86StateFrame.Frame.codeLoaded
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.wb_exact
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.storeBytes_frame
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.store_word_exact
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.Controls.round_trip
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.Controls.omitted_write_footprint_refused
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.Controls.unaligned_store_refused
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.handler_increment
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.fetched_increment
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.result_frame
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.increment_wraps
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.wrong_answer_refused
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.exact_frame
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.suffix_preserved
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.omitted_write_footprint_refused
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.all_checked
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.every_image_has_fuel
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.increment_bytes
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.exhausted_target_decoded
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.Controls.changed_immediate_refused
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.Controls.changed_counter_field_refused
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.Controls.changed_exhaustion_target_refused
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.executes
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.any_run_refines
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.Controls.available
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.Controls.exhausted_equal
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.Controls.unlimited_wraps
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.Controls.wrong_counter_refused
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.Controls.exhaustion_increment_refused
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.code_of_read_range
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.Controls.shifted_base_refused
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.Controls.changed_byte_refused
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.Placed.preserved
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.Controls.disjoint_data_write_preserves_image
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.Controls.whole_image_exclusion_required
#print axioms Mettapedia.Machines.TIsa.NativeFuelProfile.all_full_spans_checked
#print axioms Mettapedia.Machines.TIsa.NativeFuelRefinement.relative_target
#print axioms Mettapedia.Machines.TIsa.NativeFuelRefinement.executes_checked
#print axioms Mettapedia.Machines.TIsa.NativeFuelRefinement.observed_run_refines
#print axioms Mettapedia.Machines.TIsa.NativeFuelRefinement.imported_span_executes
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.executes
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.any_run_refines
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.source_refines
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Result.image_preserved
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Controls.add_alias
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Controls.sub_alias
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Controls.exhausted_execution_refused
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Controls.changed_opcode_refuses_add
#print axioms Mettapedia.Machines.TIsa.NativeFueledBin.executes_checked
#print axioms Mettapedia.Machines.TIsa.NativeFueledBin.observed_run_refines
#print axioms Mettapedia.Machines.TIsa.NativeFueledBin.Controls.changed_opcode_refused
#print axioms Mettapedia.Machines.TIsa.ExitStatus.encoding
#print axioms Mettapedia.Machines.TIsa.X86FrameStore.fetched_register
#print axioms Mettapedia.Machines.TIsa.X86FrameStore.fetched_immediate
#print axioms Mettapedia.Machines.TIsa.X86FrameStore.Controls.zero_extended_negative_refused
#print axioms Mettapedia.Machines.TIsa.X86OutcomeLoad.fetched_eax
#print axioms Mettapedia.Machines.TIsa.X86OutcomeLoad.Controls.sign_extension_refused
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.executes
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.finished_result
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.any_run_refines
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.Result.image_preserved
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.Controls.exhausted_publishes
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.Controls.unchanged_return_refused
#print axioms Mettapedia.Machines.TIsa.NativeFailureProfile.all_checked
#print axioms Mettapedia.Machines.TIsa.NativeFailureProfile.Controls.changed_status_refused
#print axioms Mettapedia.Machines.TIsa.NativeFailureRefinement.executes_checked
#print axioms Mettapedia.Machines.TIsa.X86StateFrame.basisAt
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.imported_pair
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.handlerInput
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.executes
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.any_run_refines
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.Controls.actual_fuel_span_exhausted
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.Controls.incremented_counter_refused
#print axioms Mettapedia.Machines.TIsa.X86PlainFetch.fetch_to_dispatch
#print axioms Mettapedia.Machines.TIsa.X86PlainFetch.fetch_rex_to_dispatch
#print axioms Mettapedia.Machines.TIsa.X86Stack.fetched_pop
#print axioms Mettapedia.Machines.TIsa.X86Stack.fetched_ret
#print axioms Mettapedia.Machines.TIsa.X86Epilogue.executes
#print axioms Mettapedia.Machines.TIsa.X86Epilogue.finished_result
#print axioms Mettapedia.Machines.TIsa.X86Epilogue.Controls.restores_and_returns
#print axioms Mettapedia.Machines.TIsa.X86Epilogue.Controls.unrestored_register_refused
#print axioms Mettapedia.Machines.TIsa.NativeEpilogueRefinement.executes_checked
#print axioms Mettapedia.Machines.TIsa.NativeEpilogueRefinement.Controls.changed_pop_refused
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericGrade.handler
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericGrade.fetched
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericGrade.result_frame
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.subtract_handler
#print axioms Mettapedia.Machines.TIsa.FundingTrace.charge_of_remaining_bound
#print axioms Mettapedia.Machines.TIsa.FundingTrace.paid_at_prefix
#print axioms Mettapedia.Machines.TIsa.P1Source.Stmt.reportedBound_exact
#print axioms Mettapedia.Machines.TIsa.P1Source.Controls.exact_maximum_fits
#print axioms Mettapedia.Machines.TIsa.P1Source.Controls.overflowing_nested_bound
#print axioms Mettapedia.Machines.TIsa.P1Source.readText_exact
#print axioms Mettapedia.Machines.TIsa.P1Scalar.rewrite_iff
#print axioms Mettapedia.Machines.TIsa.P1Scalar.lower?_eq_some_iff
#print axioms Mettapedia.Machines.TIsa.P1Scalar.edge_guard_iff
#print axioms Mettapedia.Machines.TIsa.P1Scalar.invalid_realized
#print axioms Mettapedia.Machines.TIsa.P1Scalar.invalid_rewrite_iff
#print axioms Mettapedia.Machines.TIsa.P1Scalar.invalid_preserves_data
#print axioms Mettapedia.Machines.TIsa.Control.Edge.finish_of_no_outputs
#print axioms Mettapedia.Machines.TIsa.Control.Edge.readonly_realized
#print axioms Mettapedia.Machines.TIsa.P1Memory.address?_inside
#print axioms Mettapedia.Machines.TIsa.P1Memory.access?_iff_inside
#print axioms Mettapedia.Machines.TIsa.P1Memory.load_rewrite_iff
#print axioms Mettapedia.Machines.TIsa.P1Memory.store_guard_iff
#print axioms Mettapedia.Machines.TIsa.P1Memory.store_preserves_outside
#print axioms Mettapedia.Machines.TIsa.P1Memory.addressValue_inside
#print axioms Mettapedia.Machines.TIsa.P1Memory.load_cases_complete
#print axioms Mettapedia.Machines.TIsa.P1Memory.load_bounds_exclusive
#print axioms Mettapedia.Machines.TIsa.P1Memory.load_boolean_exclusive
#print axioms Mettapedia.Machines.TIsa.P1Memory.frame_access
#print axioms Mettapedia.Machines.TIsa.P1Memory.Controls.intermediate_escape_rejected
#print axioms Mettapedia.Machines.TIsa.P1Memory.Controls.load_pointer_alias_fires
#print axioms Mettapedia.Machines.TIsa.P1Memory.Controls.loaded_bad_bool_fires_error
#print axioms Mettapedia.Machines.TIsa.P1Memory.Controls.bounds_error_without_any_byte_cell
#print axioms Mettapedia.Machines.TIsa.P1Memory.Controls.byte_into_i32_is_not_signed_byte
#print axioms Mettapedia.Machines.TIsa.P1Memory.Controls.malformed_byte_is_not_a_boolean_fault
#print axioms Mettapedia.Machines.TIsa.P1Memory.Controls.readonly_store_not_enabled
#print axioms Mettapedia.Machines.TIsa.P1Memory.Controls.negative_store_offset_and_little_endian
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.load_dword_exact
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.effective_disp32
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.operand_dword
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.handler_dword
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.fetched_dword
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.result_frame
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.Controls.high_dword_zero_extended
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.Controls.sign_extension_rejected
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.Controls.changed_modrm_changes_destination
#print axioms Mettapedia.Machines.TIsa.X86SubImmediate.handler_sub4
#print axioms Mettapedia.Machines.TIsa.X86SubImmediate.fetched_sub4
#print axioms Mettapedia.Machines.TIsa.X86SubImmediate.no_borrow
#print axioms Mettapedia.Machines.TIsa.X86SubImmediate.result_frame
#print axioms Mettapedia.Machines.TIsa.X86SubImmediate.Controls.enough_length
#print axioms Mettapedia.Machines.TIsa.X86SubImmediate.Controls.short_length_borrows
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.arithmetic_prefix
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.borrow_prefix
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.range_prefix
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.bounds_classifies
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.load_executes
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.load_observes
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.short_rejects
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.range_rejects
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.Controls.boundary_accepts
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.Controls.interior_accepts
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.Controls.empty_rejects
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.Controls.short_rejects
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.Controls.end_pointer_rejects
#print axioms Mettapedia.Machines.TIsa.X86P1LoadBounds.Controls.end_pointer_unmapped
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.selected_by_name
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.source_instruction
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.captured_fields
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.p1_value
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.resource_step
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.source_recipe
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.span_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.span_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.bounds_classifies
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.load_executes
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.source_guard
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.bounds_agree
#print axioms Mettapedia.Machines.TIsa.X86P1TagCompare.sub32_executes
#print axioms Mettapedia.Machines.TIsa.X86P1TagCompare.handler_cmp32
#print axioms Mettapedia.Machines.TIsa.X86P1TagCompare.fetched_cmp32
#print axioms Mettapedia.Machines.TIsa.X86P1TagCompare.equal_sense
#print axioms Mettapedia.Machines.TIsa.X86P1TagCompare.result_frame
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.rex_escape_scan
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.fetch_to_rex_escape
#print axioms Mettapedia.Machines.TIsa.X86TwoByteDispatch.decode_register
#print axioms Mettapedia.Machines.TIsa.X86TwoByteDispatch.select_sete
#print axioms Mettapedia.Machines.TIsa.X86TwoByteDispatch.select_movzx
#print axioms Mettapedia.Machines.TIsa.X86ConditionByte.replaceByte_low
#print axioms Mettapedia.Machines.TIsa.X86ConditionByte.sete_handler
#print axioms Mettapedia.Machines.TIsa.X86ConditionByte.movzx_handler
#print axioms Mettapedia.Machines.TIsa.X86ConditionByte.fetched_sete
#print axioms Mettapedia.Machines.TIsa.X86ConditionByte.fetched_movzx
#print axioms Mettapedia.Machines.TIsa.X86ConditionByte.byte_frame
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.observes
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.executes
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.source_instruction
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.source_value
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.resource_step
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.Controls.matching_tag
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.Controls.different_tag
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.test_step
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.executes
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.source_condition
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.compare_then_if
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.common_handlers
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.load_compare_if
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.Controls.false_branches
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.Controls.true_falls_through
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.PrefixControls.control
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.PrefixControls.matching_tag
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.PrefixControls.different_tag
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.source_block
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.containing_spans
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.captured_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.load_compare_refused
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.captured_prologue
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.captured_epilogue
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.public_refused
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.Controls.different_tag_returns_zero
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.Controls.wrong_completion_refused
#print axioms Mettapedia.Machines.TIsa.NativeRefinement.Boundary.realizes
#print axioms Mettapedia.Machines.TIsa.NativeRefinement.Boundary.wp_native
#print axioms Mettapedia.Machines.TIsa.NativeRefinement.CountedBoundary.realizes
#print axioms Mettapedia.Machines.TIsa.NativeRefinement.CountedBoundary.wp_native
#print axioms Mettapedia.Machines.TIsa.NativeRefinement.CountedBoundary.wp_native_reflects
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.action_progress
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.emit_exact
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.p1_move_iff
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.code_length
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.counted_boundary
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.compile
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.compile_wp
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.compile_reflects
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.prefix_executes
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.prefix_frame
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.prefix_preserves
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.Controls.two_copies_and_elision
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.Controls.wrong_copy_result_refused
#print axioms Mettapedia.Machines.TIsa.X86CopyBlock.Controls.changed_byte_rejected
#print axioms Mettapedia.Machines.TIsa.X86BlockCompiler.code_bind
#print axioms Mettapedia.Machines.TIsa.X86BlockCompiler.counted_boundary
#print axioms Mettapedia.Machines.TIsa.X86BlockCompiler.compile_wp
#print axioms Mettapedia.Machines.TIsa.X86BlockCompiler.compile_reflects
#print axioms Mettapedia.Machines.TIsa.X86BlockCompiler.prefix_frame
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.expected_trace
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.finished_flags
#print axioms Mettapedia.Machines.TIsa.X86WordLibrary.binSample_present
#print axioms Mettapedia.Machines.TIsa.X86WordLibrary.binaryBytes_exact
#print axioms Mettapedia.Machines.TIsa.X86WordLibrary.copy_execute
#print axioms Mettapedia.Machines.TIsa.X86WordLibrary.binary_execute
#print axioms Mettapedia.Machines.TIsa.X86WordLibrary.correct
#print axioms Mettapedia.Machines.TIsa.X86WordLibrary.p1_iff
#print axioms Mettapedia.Machines.TIsa.X86WordLibrary.prefix_preserves
#print axioms Mettapedia.Machines.TIsa.X86WordLibrary.Controls.mixed_wraparound
#print axioms Mettapedia.Machines.TIsa.X86WordLibrary.Controls.wrong_result_refused
#print axioms Mettapedia.Machines.TIsa.X86WordLibrary.Controls.changed_byte_rejected
#print axioms Mettapedia.Machines.TIsa.Control.OutcomeControls.independent_payload
#print axioms Mettapedia.Machines.TIsa.Control.OutcomeControls.conflated_status_rejected
#print axioms Mettapedia.Machines.TIsa.Control.OutcomeControls.completed_payload_42
#print axioms Mettapedia.Machines.TIsa.P1Scalar.Controls.alias_fires
#print axioms Mettapedia.Machines.TIsa.P1Scalar.Controls.invalid_boolean_fires
#print axioms Mettapedia.Machines.TIsa.P1Scalar.Controls.invalid_boolean_keeps_destination
#print axioms Mettapedia.Machines.TIsa.ImportedP1.abi_boundary_checked
#print axioms Mettapedia.Machines.TIsa.ImportedP1.premise_name_inventory
#print axioms Mettapedia.Machines.TIsa.ImportedP1.all_source_fields_checked
#print axioms Mettapedia.Machines.TIsa.ImportedP1.all_image_layouts_checked
#print axioms Mettapedia.Machines.TIsa.ImportedP1.all_source_spellings_exact
#print axioms Mettapedia.Machines.TIsa.ImportedP1.all_cost_fields_exact
#print axioms Mettapedia.Machines.TIsa.ImportedP1.changed_condition_rejected
#print axioms Mettapedia.Machines.TIsa.ImportedP1.changed_region_rejected
#print axioms Mettapedia.Machines.TIsa.ImportedP1.changed_cost_rejected
#print axioms Mettapedia.Machines.TIsa.ImportedP1.changed_path_rejected
#print axioms Mettapedia.Machines.TIsa.ImportedP1.changed_wrapper_byte_rejected
#print axioms Mettapedia.Machines.TIsa.ImportedP1.changed_abi_map_rejected
#print axioms Mettapedia.Machines.TIsa.FundingTrace.exhausted_iff_cutpoint
#print axioms Mettapedia.Machines.TIsa.FundingTrace.exhausted_iff_frontier
#print axioms Mettapedia.Machines.TIsa.FundingTrace.exhausted_suffix_irrelevant
#print axioms Mettapedia.Machines.TIsa.FundingTrace.CutpointControls.stop_after_two
#print axioms Mettapedia.Machines.TIsa.FundingTrace.CutpointControls.entry_receipt_retained
#print axioms Mettapedia.Machines.TIsa.FundingTrace.CutpointControls.larger_budget_finishes
#print axioms Mettapedia.Machines.TIsa.FundingTrace.CutpointControls.cannot_move_stop_to_entry
#print axioms Mettapedia.Machines.TIsa.FundingTrace.CutpointControls.invalid_is_not_exhausted
#print axioms Mettapedia.Machines.TIsa.FundingTrace.BoundControls.all_checks_covered
#print axioms Mettapedia.Machines.TIsa.FundingTrace.BoundControls.underfunded_test_requires_fallback
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.fetched_subtract
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.subtract_frame
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.add_handler
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.add_frame
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.fetched_add
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.remaining_prefix
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.compare_executes
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.branch_executes
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.paid
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.exhausted
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.realizes_charge
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.calibrationInput
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.Controls.inputs_inhabited
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.Controls.paid_wrong_target
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.Controls.exhausted_wrong_byte
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.captured_block_exact
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.captured_window
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.executes
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.finished_result
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.any_run_refines
#print axioms Mettapedia.Machines.TIsa.X86FailureHandler.RegisterPath.code_preserved
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.captured_slice
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.captured_window
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.executes
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.Controls.sample_code
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.Controls.sample_controls
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.Controls.sample_reaches_epilogue
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.Controls.stale_result_refused
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.Controls.early_receipt_refused

#print axioms Mettapedia.Machines.TIsa.X86ReturnPath.executes
#print axioms Mettapedia.Machines.TIsa.X86ReturnPath.finished_result
#print axioms Mettapedia.Machines.TIsa.X86ReturnPath.any_run_refines
#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.captured_slice
#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.captured_window
#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.executes
#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.Controls.sample_reaches_epilogue
#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.Controls.truncated_result_refused
#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.Controls.unpaid_receipt_refused

#print axioms Mettapedia.Machines.TIsa.X86Stack.push_handler
#print axioms Mettapedia.Machines.TIsa.X86Stack.fetched_push
#print axioms Mettapedia.Machines.TIsa.X86Stack.push_frame
#print axioms Mettapedia.Machines.TIsa.X86Prologue.executes
#print axioms Mettapedia.Machines.TIsa.X86Prologue.saved_bytes
#print axioms Mettapedia.Machines.TIsa.X86Prologue.return_bytes
#print axioms Mettapedia.Machines.TIsa.X86Prologue.epilogueStackFacts
#print axioms Mettapedia.Machines.TIsa.X86Prologue.any_run_refines
#print axioms Mettapedia.Machines.TIsa.X86Prologue.Controls.saves_initial_registers
#print axioms Mettapedia.Machines.TIsa.X86Prologue.Controls.stale_stack_word_refused
#print axioms Mettapedia.Machines.TIsa.X86Prologue.Controls.changed_return_address_refused

#print axioms Mettapedia.Machines.TIsa.X86Prologue.Controls.wrapper_fixture
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.epilogueInputs
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.lookup_register_equal
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.finished_result
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.executes
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.Controls.empty_body_returns
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.Controls.losing_saved_register_refused

#print axioms Mettapedia.Machines.TIsa.X86Funding.WrapperEncoding.prologue_window
#print axioms Mettapedia.Machines.TIsa.X86Funding.WrapperEncoding.epilogue_window

#print axioms Mettapedia.Machines.TIsa.X86FundCall.bodyFund
#print axioms Mettapedia.Machines.TIsa.X86FundCall.paid
#print axioms Mettapedia.Machines.TIsa.X86FundCall.exhausted
#print axioms Mettapedia.Machines.TIsa.X86FundCall.Controls.paid_returns
#print axioms Mettapedia.Machines.TIsa.X86FundCall.Controls.exhausted_returns
#print axioms Mettapedia.Machines.TIsa.X86FundCall.Controls.unpaid_receipt_refused
#print axioms Mettapedia.Machines.TIsa.X86FundCall.Controls.scratch_value_refused
#print axioms Mettapedia.Machines.TIsa.X86FundCall.Controls.epilogue_entry_refused_as_return
