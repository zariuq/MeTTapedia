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
import Mettapedia.Machines.TIsa.X86Alignment
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
import Mettapedia.Machines.TIsa.X86BranchGate
import Mettapedia.Machines.TIsa.X86Conditional
import Mettapedia.Machines.TIsa.X86RegisterIncrement
import Mettapedia.Machines.TIsa.X86LoopHeader
import Mettapedia.Machines.TIsa.X86LoopLatch
import Mettapedia.Machines.TIsa.X86P1LoopCapture
import Mettapedia.Machines.TIsa.X86WordBody
import Mettapedia.Machines.TIsa.X86CountedWordLoop
import Mettapedia.Machines.TIsa.X86Immediate32
import Mettapedia.Machines.TIsa.X86Zero32
import Mettapedia.Machines.TIsa.X86CapGate
import Mettapedia.Machines.TIsa.X86LoopEntry
import Mettapedia.Machines.TIsa.X86P1LoopEntryCapture
import Mettapedia.Machines.TIsa.X86CountedWordProgram
import Mettapedia.Machines.TIsa.X86QwordLoad
import Mettapedia.Machines.TIsa.X86AddImmediate
import Mettapedia.Machines.TIsa.X86SubByteImmediate
import Mettapedia.Machines.TIsa.X86P1QwordBounds
import Mettapedia.Machines.TIsa.X86P1QwordLoadCapture
import Mettapedia.Machines.TIsa.X86QwordZero
import Mettapedia.Machines.TIsa.X86P1QwordCompareCapture
import Mettapedia.Machines.TIsa.X86P1QwordGuardCapture
import Mettapedia.Machines.TIsa.X86PositiveImmediate
import Mettapedia.Machines.TIsa.X86DataStore
import Mettapedia.Machines.TIsa.X86SibStore
import Mettapedia.Machines.TIsa.X86P1SibStoreCapture
import Mettapedia.Machines.TIsa.X86IndexedAddress
import Mettapedia.Machines.TIsa.X86UnalignedWords
import Mettapedia.Machines.TIsa.X86Readiness
import Mettapedia.Machines.TIsa.X86ControlFlags
import Mettapedia.Machines.TIsa.X86LoopReadiness
import Mettapedia.Machines.TIsa.X86MemoryView
import Mettapedia.Machines.TIsa.X86MemoryScalarLibrary
import Mettapedia.Machines.TIsa.X86MemoryReadback
import Mettapedia.Machines.TIsa.X86MemoryBounds
import Mettapedia.Machines.TIsa.X86MemoryFieldLoad
import Mettapedia.Machines.TIsa.X86MemoryStore
import Mettapedia.Machines.TIsa.X86MemoryAdapterStore
import Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure
import Mettapedia.Machines.TIsa.X86Assembler
import Mettapedia.Machines.TIsa.X86AssemblerExecution
import Mettapedia.Machines.TIsa.X86AssemblerCapture
import Mettapedia.Machines.TIsa.X86BranchCompiler
import Mettapedia.Machines.TIsa.X86BranchCompilerControls
import Mettapedia.Machines.TIsa.X86BranchRegion
import Mettapedia.Machines.TIsa.X86BranchRegionControls
import Mettapedia.Machines.TIsa.X86BranchGraph
import Mettapedia.Machines.TIsa.X86BranchGraphControls
import Mettapedia.Machines.TIsa.X86WordPrimitive
import Mettapedia.Machines.TIsa.X86MixedRegion
import Mettapedia.Machines.TIsa.X86MixedRegionControls
import Mettapedia.Machines.TIsa.X86MaskedFlags
import Mettapedia.Machines.TIsa.X86Shift
import Mettapedia.Machines.TIsa.X86ShiftControls
import Mettapedia.Machines.TIsa.X86SignExtension
import Mettapedia.Machines.TIsa.X86ShiftBlock
import Mettapedia.Machines.TIsa.X86ShiftBlockControls
import Mettapedia.Machines.TIsa.X86DataPrimitive
import Mettapedia.Machines.TIsa.X86MixedShiftControls
import Mettapedia.Machines.TIsa.X86BareFetch
import Mettapedia.Machines.TIsa.X86Shift32
import Mettapedia.Machines.TIsa.X86Shift32Instruction
import Mettapedia.Machines.TIsa.X86Shift32Controls
import Mettapedia.Machines.TIsa.X86Move32
import Mettapedia.Machines.TIsa.X86Extend32
import Mettapedia.Machines.TIsa.X86FetchEntry
import Mettapedia.Machines.TIsa.X86Normalize32
import Mettapedia.Machines.TIsa.X86DwordShift
import Mettapedia.Machines.TIsa.X86TypedShiftBlock
import Mettapedia.Machines.TIsa.X86TypedShiftBlockControls
import Mettapedia.Machines.TIsa.X86ShiftLibrary
import Mettapedia.Machines.TIsa.X86TypedScalarLibrary
import Mettapedia.Machines.TIsa.X86TypedScalarControls
import Mettapedia.Machines.TIsa.X86P1ArithmeticCapture
import Mettapedia.Machines.TIsa.X86P1ScalarReadiness
import Mettapedia.Machines.TIsa.X86P1ScalarControls
import Mettapedia.Machines.TIsa.X86BoundedLoadControls
import Mettapedia.Machines.TIsa.X86BoundedStoreControls
import Mettapedia.Machines.TIsa.X86MemoryContinuation
import Mettapedia.Machines.TIsa.X86MemoryFailureControls
import Mettapedia.Machines.TIsa.LibraryLoweringControls
import Mettapedia.Machines.TIsa.RowTableViewControls
import Mettapedia.Machines.TIsa.RowTableInitialization
import Mettapedia.Machines.TIsa.BufferPublication
import Mettapedia.Machines.TIsa.X86P1StoreCapture
import Mettapedia.Machines.TIsa.X86BoundsArithmetic
import Mettapedia.Machines.TIsa.X86Bounds
import Mettapedia.Machines.TIsa.X86BoundsPrefixes
import Mettapedia.Machines.TIsa.X86P1FieldLoadCapture
import Mettapedia.Machines.TIsa.X86P1OutputCapture
import Mettapedia.Machines.TIsa.X86P1SuccessCapture
import Mettapedia.Machines.TIsa.X86P1RejectionCapture
import Mettapedia.Machines.TIsa.X86P1PropRefinement
import Mettapedia.Machines.TIsa.CheckedAdmission
import Mettapedia.Machines.TIsa.X86LogicalWord
import Mettapedia.Machines.TIsa.X86LogicalLibrary
import Mettapedia.Machines.TIsa.X86LibrarySum
import Mettapedia.Machines.TIsa.X86ScalarLibrary
import Mettapedia.Machines.TIsa.X86LogicalRecipes
import Mettapedia.Machines.TIsa.RegisterCodeLowering
import Mettapedia.Machines.TIsa.X86RegisterCodeLogical
import Mettapedia.Machines.TIsa.X86RegisterCodeScalar
import Mettapedia.Machines.TIsa.X86RowTableMark
import Mettapedia.Machines.TIsa.X86BinaryCallbackBody
import Mettapedia.Machines.TIsa.X86CanonicalSpan
import Mettapedia.Machines.TIsa.X86BinaryCallbackContract
import Mettapedia.Machines.TIsa.X86ScalarProducer
import Mettapedia.Machines.TIsa.X86P1InvalidCapture
import Mettapedia.Machines.TIsa.X86P1BoundsFailureSource
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
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.write_frame_checked
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
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.operand_dword_checked
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.handler_dword_checked
#print axioms Mettapedia.Machines.TIsa.X86DwordLoad.fetched_dword_checked
#print axioms Mettapedia.Machines.TIsa.X86Alignment.disabled_when_ac_clear
#print axioms Mettapedia.Machines.TIsa.X86Alignment.arithmetic_preserves_ac
#print axioms Mettapedia.Machines.TIsa.X86Alignment.Controls.executes
#print axioms Mettapedia.Machines.TIsa.X86Alignment.Controls.high_dword_zero_extended
#print axioms Mettapedia.Machines.TIsa.X86Alignment.Controls.sign_extension_rejected
#print axioms Mettapedia.Machines.TIsa.X86Alignment.Controls.changed_modrm_changes_destination
#print axioms Mettapedia.Machines.TIsa.X86Alignment.Controls.unaligned_address
#print axioms Mettapedia.Machines.TIsa.X86Alignment.Controls.disabled_despite_am_and_user_mode
#print axioms Mettapedia.Machines.TIsa.X86Alignment.Controls.enabled_profile_rejects_unaligned
#print axioms Mettapedia.Machines.TIsa.X86Alignment.Controls.arithmetic_keeps_alignment_disabled
#print axioms Mettapedia.Machines.TIsa.X86Alignment.Controls.memory_preserved
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
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.selected_by_name
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.source_instruction
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.captured_fields
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.captured_executes_checked
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
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.executes
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.source_instruction
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.source_value
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.resource_step
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.Controls.matching_tag
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.Controls.different_tag
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.jne_executes
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.executes
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.generic_handlers
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.nonzero_sense
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.source_condition
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.compare_then_if
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.common_handlers
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.load_compare_if
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.Controls.different_jumps
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.Controls.equal_falls_through
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.Controls.test_form_not_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.PrefixControls.control
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.PrefixControls.matching_tag
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.PrefixControls.different_tag
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.source_block
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.containing_spans
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.captured_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.load_compare_refused
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.captured_entry
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.captured_exit
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

#print axioms Mettapedia.Machines.TIsa.X86BranchGate.code_length
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.test_step
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.executes
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.prefix_frame
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.realizes
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.Controls.backward_zero
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.Controls.true_fallthrough
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.Controls.nonboolean_source_refused
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.Controls.changed_displacement
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.Controls.changed_register
#print axioms Mettapedia.Machines.TIsa.X86Conditional.displacement_exact
#print axioms Mettapedia.Machines.TIsa.X86Conditional.loaded_slice
#print axioms Mettapedia.Machines.TIsa.X86Conditional.gate
#print axioms Mettapedia.Machines.TIsa.X86Conditional.skip
#print axioms Mettapedia.Machines.TIsa.X86Conditional.At.layout
#print axioms Mettapedia.Machines.TIsa.X86Conditional.compile_wp
#print axioms Mettapedia.Machines.TIsa.X86Conditional.compile_reflects
#print axioms Mettapedia.Machines.TIsa.X86Conditional.wordValue_encode
#print axioms Mettapedia.Machines.TIsa.X86Conditional.wordCompatible
#print axioms Mettapedia.Machines.TIsa.X86Conditional.word_correct
#print axioms Mettapedia.Machines.TIsa.X86Conditional.Controls.compiled_bytes
#print axioms Mettapedia.Machines.TIsa.X86Conditional.Controls.conditional_wraparound
#print axioms Mettapedia.Machines.TIsa.X86Conditional.Controls.changed_jump_rejected
#print axioms Mettapedia.Machines.TIsa.X86Conditional.Controls.malformed_boolean_refused
#print axioms Mettapedia.Machines.TIsa.X86Conditional.Controls.empty_arm_layout
#print axioms Mettapedia.Machines.TIsa.X86Conditional.Controls.overflowing_displacement_refused

#print axioms Mettapedia.Machines.TIsa.Control.Loop.latch_realized
#print axioms Mettapedia.Machines.TIsa.Control.Loop.header_realized
#print axioms Mettapedia.Machines.TIsa.Control.LoopControls.last_latch_fires
#print axioms Mettapedia.Machines.TIsa.Control.LoopControls.zero_bound_exits
#print axioms Mettapedia.Machines.TIsa.X86RegisterIncrement.handler
#print axioms Mettapedia.Machines.TIsa.X86RegisterIncrement.fetched
#print axioms Mettapedia.Machines.TIsa.X86RegisterIncrement.result_frame
#print axioms Mettapedia.Machines.TIsa.X86RegisterIncrement.executes
#print axioms Mettapedia.Machines.TIsa.X86RegisterIncrement.Controls.every_register
#print axioms Mettapedia.Machines.TIsa.X86RegisterIncrement.Controls.wraparound
#print axioms Mettapedia.Machines.TIsa.X86RegisterIncrement.Controls.changed_immediate_rejected
#print axioms Mettapedia.Machines.TIsa.X86UnconditionalJump.Block.executes
#print axioms Mettapedia.Machines.TIsa.X86LoopHeader.compare_step
#print axioms Mettapedia.Machines.TIsa.X86LoopHeader.executes
#print axioms Mettapedia.Machines.TIsa.X86LoopHeader.prefix_frame
#print axioms Mettapedia.Machines.TIsa.X86LoopHeader.realizes
#print axioms Mettapedia.Machines.TIsa.X86LoopHeader.Controls.zero_bound_exits
#print axioms Mettapedia.Machines.TIsa.X86LoopHeader.Controls.last_iteration_continues
#print axioms Mettapedia.Machines.TIsa.X86LoopHeader.Controls.reached_bound_exits
#print axioms Mettapedia.Machines.TIsa.X86LoopHeader.Controls.changed_condition_rejected
#print axioms Mettapedia.Machines.TIsa.X86LoopLatch.executes
#print axioms Mettapedia.Machines.TIsa.X86LoopLatch.bound_outside
#print axioms Mettapedia.Machines.TIsa.X86LoopLatch.realizes
#print axioms Mettapedia.Machines.TIsa.X86LoopLatch.Controls.last_iteration
#print axioms Mettapedia.Machines.TIsa.X86LoopLatch.Controls.prefixes_preserve_frame
#print axioms Mettapedia.Machines.TIsa.X86LoopLatch.Controls.reached_bound_source_refused
#print axioms Mettapedia.Machines.TIsa.X86LoopLatch.Controls.changed_backedge_rejected
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.selected_by_name
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.source_loop
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.register_map
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.header_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.latch_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.header_executes
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.latch_executes
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.source_matches
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.header_realizes
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.latch_realizes
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.latch_then_header

#print axioms Mettapedia.Machines.TIsa.X86WordBody.encode_injective
#print axioms Mettapedia.Machines.TIsa.X86WordBody.source_frame
#print axioms Mettapedia.Machines.TIsa.X86WordBody.update_realized
#print axioms Mettapedia.Machines.TIsa.X86WordBody.source_fires
#print axioms Mettapedia.Machines.TIsa.X86WordBody.run_preserves
#print axioms Mettapedia.Machines.TIsa.X86WordBody.transfer_realized
#print axioms Mettapedia.Machines.TIsa.X86WordBody.execute
#print axioms Mettapedia.Machines.TIsa.X86WordBody.all_safe
#print axioms Mettapedia.Machines.TIsa.X86WordBody.Controls.protected_registers
#print axioms Mettapedia.Machines.TIsa.X86WordBody.Controls.unsafe_body_detected
#print axioms Mettapedia.Machines.TIsa.X86WordBody.Controls.native_body
#print axioms Mettapedia.Machines.TIsa.X86WordBody.Controls.changed_arithmetic_rejected
#print axioms Mettapedia.Machines.TIsa.X86WordBody.Controls.wrong_control_refused
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.head_displacement_exact
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.back_displacement_exact
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.header_step
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.body_step
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.latch_step
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.iteration
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.completes
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.reflects
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.transfer_postcondition
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.Controls.compiled_bytes
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.Controls.counted_execution
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.Controls.changed_jump_refused
#print axioms Mettapedia.Machines.TIsa.X86CountedWordLoop.Controls.counter_write_detected

#print axioms Mettapedia.Machines.TIsa.X86OpcodeDispatch.immediate_dword_guarded
#print axioms Mettapedia.Machines.TIsa.X86OpcodeDispatch.xor_register_guarded
#print axioms Mettapedia.Machines.TIsa.Control.Loop.entryValues_guard
#print axioms Mettapedia.Machines.TIsa.Control.Loop.entry_overwrite
#print axioms Mettapedia.Machines.TIsa.Control.Loop.entry_realized
#print axioms Mettapedia.Machines.TIsa.Control.Loop.entry_refuses_excess
#print axioms Mettapedia.Machines.TIsa.X86Immediate32.handler
#print axioms Mettapedia.Machines.TIsa.X86Immediate32.fetched
#print axioms Mettapedia.Machines.TIsa.X86Immediate32.executes
#print axioms Mettapedia.Machines.TIsa.X86Immediate32.Controls.all_registers
#print axioms Mettapedia.Machines.TIsa.X86Immediate32.Controls.changed_immediate_rejected
#print axioms Mettapedia.Machines.TIsa.X86Zero32.read32
#print axioms Mettapedia.Machines.TIsa.X86Zero32.xor_self
#print axioms Mettapedia.Machines.TIsa.X86Zero32.handler
#print axioms Mettapedia.Machines.TIsa.X86Zero32.fetched
#print axioms Mettapedia.Machines.TIsa.X86Zero32.executes
#print axioms Mettapedia.Machines.TIsa.X86Zero32.Controls.resets_counter
#print axioms Mettapedia.Machines.TIsa.X86Zero32.Controls.changed_register_rejected
#print axioms Mettapedia.Machines.TIsa.X86CapGate.compare_step
#print axioms Mettapedia.Machines.TIsa.X86CapGate.executes
#print axioms Mettapedia.Machines.TIsa.X86CapGate.prefix_frame
#print axioms Mettapedia.Machines.TIsa.X86CapGate.Controls.zero_admitted
#print axioms Mettapedia.Machines.TIsa.X86CapGate.Controls.equal_cap_admitted
#print axioms Mettapedia.Machines.TIsa.X86CapGate.Controls.excess_rejected
#print axioms Mettapedia.Machines.TIsa.X86CapGate.Controls.changed_condition_rejected
#print axioms Mettapedia.Machines.TIsa.X86LoopEntry.gate_step
#print axioms Mettapedia.Machines.TIsa.X86LoopEntry.executes
#print axioms Mettapedia.Machines.TIsa.X86LoopEntry.prefix_frame
#print axioms Mettapedia.Machines.TIsa.X86LoopEntry.realizes_entry_cells
#print axioms Mettapedia.Machines.TIsa.X86LoopEntry.rejects_entry_guard
#print axioms Mettapedia.Machines.TIsa.X86LoopEntry.Controls.outcome
#print axioms Mettapedia.Machines.TIsa.X86LoopEntry.Controls.every_prefix_preserves_stack_memory
#print axioms Mettapedia.Machines.TIsa.X86LoopEntry.Controls.changed_condition_rejected
#print axioms Mettapedia.Machines.TIsa.X86P1LoopEntryCapture.entry_span
#print axioms Mettapedia.Machines.TIsa.X86P1LoopEntryCapture.entry_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1LoopEntryCapture.entry_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1LoopEntryCapture.entry_executes
#print axioms Mettapedia.Machines.TIsa.X86P1LoopEntryCapture.entry_realizes
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.entry_handlers
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.physical_injective
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.entry_writes
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.entry_data
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.entry_step
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.completes
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.reflects
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.transfer_postcondition
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.excess_branch
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.Controls.compiled_bytes
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.Controls.counted_execution
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.Controls.excess_preserves_old_counter
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.Controls.changed_cap_refused
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.Controls.changed_body_refused
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.Controls.unsafe_context_refused
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.destination64
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.operand_qword
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.operand_qword_checked
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.handler_qword_checked
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.fetched_qword_checked
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.handler_qword
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.fetched_qword
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.executes
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.Controls.full_word
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.Controls.high_word_not_truncated
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.Controls.changed_destination_rejected
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.source_instruction
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.tail_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.tail_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.tail_executes
#print axioms Mettapedia.Machines.TIsa.X86AddImmediate.raw_sum_nat
#print axioms Mettapedia.Machines.TIsa.X86AddImmediate.add_carry
#print axioms Mettapedia.Machines.TIsa.X86AddImmediate.handler_add16
#print axioms Mettapedia.Machines.TIsa.X86AddImmediate.fetched_add16
#print axioms Mettapedia.Machines.TIsa.X86AddImmediate.executes_add16
#print axioms Mettapedia.Machines.TIsa.X86AddImmediate.carry_clear
#print axioms Mettapedia.Machines.TIsa.X86AddImmediate.carry_set
#print axioms Mettapedia.Machines.TIsa.X86SubByteImmediate.positive_logext
#print axioms Mettapedia.Machines.TIsa.X86SubByteImmediate.handler
#print axioms Mettapedia.Machines.TIsa.X86SubByteImmediate.fetched
#print axioms Mettapedia.Machines.TIsa.X86SubByteImmediate.result_frame
#print axioms Mettapedia.Machines.TIsa.X86P1QwordBounds.source_guard
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.span_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.span_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.bounds_classifies
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.bounds_agree
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.load_observes
#print axioms Mettapedia.Machines.TIsa.X86QwordZero.handler
#print axioms Mettapedia.Machines.TIsa.X86QwordZero.fetched
#print axioms Mettapedia.Machines.TIsa.X86QwordZero.equal_sense
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.source_instruction
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.captured_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.captured_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.captured_observes
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.source_value
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.resource_step
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.Controls.control
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.Controls.zero_matches
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.Controls.high_word_refuses
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.Controls.changed_width_rejected
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.Controls.test_form_not_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.source_condition
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.captured_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.compare_then_if
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.load_compare_if
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.two_guard_prefix
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.PrefixControls.control
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.PrefixControls.zero_field_matches
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.PrefixControls.high_word_refuses
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.PrefixControls.wrong_tag_refuses
#print axioms Mettapedia.Machines.TIsa.X86PositiveImmediate.sign_slice
#print axioms Mettapedia.Machines.TIsa.X86PositiveImmediate.logext32
#print axioms Mettapedia.Machines.TIsa.X86PositiveImmediate.handler
#print axioms Mettapedia.Machines.TIsa.X86PositiveImmediate.fetched
#print axioms Mettapedia.Machines.TIsa.X86PositiveImmediate.fetched_frame
#print axioms Mettapedia.Machines.TIsa.X86DataStore.memory_operand_rm
#print axioms Mettapedia.Machines.TIsa.X86DataStore.handler64
#print axioms Mettapedia.Machines.TIsa.X86DataStore.write_operand64_checked
#print axioms Mettapedia.Machines.TIsa.X86DataStore.handler64_checked
#print axioms Mettapedia.Machines.TIsa.X86DataStore.fetched64_checked
#print axioms Mettapedia.Machines.TIsa.X86UnalignedWords.Load.executes
#print axioms Mettapedia.Machines.TIsa.X86UnalignedWords.Load.high_word_preserved
#print axioms Mettapedia.Machines.TIsa.X86UnalignedWords.Load.low_word_truncation_rejected
#print axioms Mettapedia.Machines.TIsa.X86UnalignedWords.Store.executes
#print axioms Mettapedia.Machines.TIsa.X86UnalignedWords.Store.enabled_alignment_rejects_success_profile
#print axioms Mettapedia.Machines.TIsa.X86DataStore.fetched64
#print axioms Mettapedia.Machines.TIsa.X86DataStore.store_dword_exact
#print axioms Mettapedia.Machines.TIsa.X86DataStore.handler32
#print axioms Mettapedia.Machines.TIsa.X86DataStore.write_operand32_checked
#print axioms Mettapedia.Machines.TIsa.X86DataStore.handler32_checked
#print axioms Mettapedia.Machines.TIsa.X86DataStore.fetched32_checked
#print axioms Mettapedia.Machines.TIsa.X86UnalignedWords.StoreDword.executes
#print axioms Mettapedia.Machines.TIsa.X86UnalignedWords.StoreDword.suffix_preserved
#print axioms Mettapedia.Machines.TIsa.X86UnalignedWords.StoreDword.qword_effect_rejected
#print axioms Mettapedia.Machines.TIsa.X86UnalignedWords.StoreDword.enabled_alignment_rejects_success_profile
#print axioms Mettapedia.Machines.TIsa.X86DataStore.fetched32
#print axioms Mettapedia.Machines.TIsa.X86DataStore.result_frame
#print axioms Mettapedia.Machines.TIsa.X86DataStore.executes
#print axioms Mettapedia.Machines.TIsa.X86DataStore.byte_readback
#print axioms Mettapedia.Machines.TIsa.X86DataStore.code_preserved
#print axioms Mettapedia.Machines.TIsa.X86DataStore.Controls.control
#print axioms Mettapedia.Machines.TIsa.X86DataStore.Controls.dword_writes_only_low
#print axioms Mettapedia.Machines.TIsa.X86DataStore.Controls.qword_writes_high
#print axioms Mettapedia.Machines.TIsa.X86DataStore.Controls.negative_displacement
#print axioms Mettapedia.Machines.TIsa.X86DataStore.Controls.changed_width_rejected
#print axioms Mettapedia.Machines.TIsa.X86P1StoreCapture.source_instruction
#print axioms Mettapedia.Machines.TIsa.X86P1StoreCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1StoreCapture.tail_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1StoreCapture.tail_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1StoreCapture.tail_executes
#print axioms Mettapedia.Machines.TIsa.X86BoundsArithmetic.native_guard_iff
#print axioms Mettapedia.Machines.TIsa.X86BoundsArithmetic.native_source_agree
#print axioms Mettapedia.Machines.TIsa.X86Bounds.code_length
#print axioms Mettapedia.Machines.TIsa.X86Bounds.move_step
#print axioms Mettapedia.Machines.TIsa.X86Bounds.subtract_step
#print axioms Mettapedia.Machines.TIsa.X86Bounds.add_step
#print axioms Mettapedia.Machines.TIsa.X86Bounds.length_step
#print axioms Mettapedia.Machines.TIsa.X86Bounds.subtract_count_step
#print axioms Mettapedia.Machines.TIsa.X86Bounds.branch_step
#print axioms Mettapedia.Machines.TIsa.X86Bounds.compare_step
#print axioms Mettapedia.Machines.TIsa.X86Bounds.offset_prefix
#print axioms Mettapedia.Machines.TIsa.X86Bounds.borrow_prefix
#print axioms Mettapedia.Machines.TIsa.X86Bounds.range_prefix
#print axioms Mettapedia.Machines.TIsa.X86Bounds.classifies
#print axioms Mettapedia.Machines.TIsa.X86Bounds.source_classifies
#print axioms Mettapedia.Machines.TIsa.X86Bounds.succeeds
#print axioms Mettapedia.Machines.TIsa.X86Bounds.Controls.zero_byte_count
#print axioms Mettapedia.Machines.TIsa.X86Bounds.Controls.positive_byte_count
#print axioms Mettapedia.Machines.TIsa.X86Bounds.Controls.unpatchable_rejected
#print axioms Mettapedia.Machines.TIsa.X86P1StoreCapture.bounds_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1StoreCapture.bounds_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1StoreCapture.boundsContext
#print axioms Mettapedia.Machines.TIsa.X86P1StoreCapture.bounds_classifies
#print axioms Mettapedia.Machines.TIsa.X86P1StoreCapture.store_span_executes
#print axioms Mettapedia.Machines.TIsa.X86P1FieldLoadCapture.source_instruction
#print axioms Mettapedia.Machines.TIsa.X86P1FieldLoadCapture.prefix_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1FieldLoadCapture.load_executes
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.transferFacts
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.immediate_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.store_writes_subset
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.output_alignment
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.stage_executes
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.prefix_extend
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.executes
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.completion_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.completes
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.Controls.control
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.Controls.high_word_retained
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.Controls.cannot_truncate_high_word
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.Controls.control_completes
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.Controls.changed_completion_rejected
#print axioms Mettapedia.Machines.TIsa.X86Bounds.Facts.transport
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.DataFacts.transport
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.Controls.fixture
#print axioms Mettapedia.Machines.TIsa.X86P1SuccessCapture.guardFacts
#print axioms Mettapedia.Machines.TIsa.X86P1SuccessCapture.body_fires
#print axioms Mettapedia.Machines.TIsa.X86P1SuccessCapture.public_fires
#print axioms Mettapedia.Machines.TIsa.X86P1SuccessCapture.Controls.control
#print axioms Mettapedia.Machines.TIsa.X86P1SuccessCapture.Controls.wrong_zero_return_rejected
#print axioms Mettapedia.Machines.TIsa.X86P1RejectionCapture.bytes
#print axioms Mettapedia.Machines.TIsa.X86P1RejectionCapture.handler_executes
#print axioms Mettapedia.Machines.TIsa.X86P1RejectionCapture.body_refuses
#print axioms Mettapedia.Machines.TIsa.X86P1RejectionCapture.public_refuses
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.identity
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.derives_iff
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.output_outside_spill
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.public_classifies
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.public_refines_rule
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.Controls.accepts_zero
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.Controls.high_level_refused
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.Controls.wrong_tag_refused
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.Controls.wrong_conclusion_refused
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.Controls.exact_counts
#print axioms Mettapedia.Machines.TIsa.X86P1PropRefinement.Controls.exact_answers
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.step_iff
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.step_sound
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.step_complete
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.step_rewrite_iff
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.commit_other_data
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.commit_other_control
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.Controls.correct_result
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.Controls.wrong_result
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.Controls.missing_read
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.Controls.missing_opcode
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.Controls.wrong_pc
#print axioms Mettapedia.Machines.TIsa.CheckedAdmission.Controls.observed

#print axioms Mettapedia.Machines.TIsa.X86LogicalWord.calculate
#print axioms Mettapedia.Machines.TIsa.X86LogicalWord.handler
#print axioms Mettapedia.Machines.TIsa.X86LogicalWord.fetched
#print axioms Mettapedia.Machines.TIsa.X86LogicalWord.executes
#print axioms Mettapedia.Machines.TIsa.X86LogicalWord.Controls.runs
#print axioms Mettapedia.Machines.TIsa.X86LogicalWord.Controls.xor_alias
#print axioms Mettapedia.Machines.TIsa.X86LogicalWord.Controls.and_keeps_high_bits
#print axioms Mettapedia.Machines.TIsa.X86LogicalWord.Controls.wrong_opcode_refused
#print axioms Mettapedia.Machines.TIsa.X86LogicalWord.Controls.wrong_destination_refused
#print axioms Mettapedia.Machines.TIsa.X86LogicalLibrary.source_step_iff
#print axioms Mettapedia.Machines.TIsa.X86LogicalLibrary.execute
#print axioms Mettapedia.Machines.TIsa.X86LogicalLibrary.correct
#print axioms Mettapedia.Machines.TIsa.X86LogicalLibrary.source_evaluate_p1
#print axioms Mettapedia.Machines.TIsa.X86LogicalLibrary.compile_wp
#print axioms Mettapedia.Machines.TIsa.X86LogicalLibrary.Controls.mask_then_toggle
#print axioms Mettapedia.Machines.TIsa.X86LogicalLibrary.Controls.wrong_result_refused
#print axioms Mettapedia.Machines.TIsa.X86LogicalLibrary.Controls.changed_opcode_rejected

#print axioms Mettapedia.Machines.TIsa.X86LibrarySum.correct
#print axioms Mettapedia.Machines.TIsa.X86ScalarLibrary.correct
#print axioms Mettapedia.Machines.TIsa.X86Readiness.correct
#print axioms Mettapedia.Machines.TIsa.X86Readiness.code_strengthen
#print axioms Mettapedia.Machines.TIsa.X86Readiness.steps_strengthen
#print axioms Mettapedia.Machines.TIsa.X86Readiness.strengthen_at
#print axioms Mettapedia.Machines.TIsa.X86Readiness.Profile.after_frame
#print axioms Mettapedia.Machines.TIsa.X86Readiness.Profile.alignment_exact
#print axioms Mettapedia.Machines.TIsa.X86Readiness.word_stable
#print axioms Mettapedia.Machines.TIsa.X86Readiness.logical_preserves_ac
#print axioms Mettapedia.Machines.TIsa.X86Readiness.logical_stable
#print axioms Mettapedia.Machines.TIsa.X86Readiness.sum_stable
#print axioms Mettapedia.Machines.TIsa.X86Readiness.scalar_stable
#print axioms Mettapedia.Machines.TIsa.X86Readiness.scalar_correct
#print axioms Mettapedia.Machines.TIsa.X86Readiness.scalar_compile_wp
#print axioms Mettapedia.Machines.TIsa.X86Readiness.Controls.alignment_readback
#print axioms Mettapedia.Machines.TIsa.X86Readiness.Controls.copy_mask_add_profile
#print axioms Mettapedia.Machines.TIsa.X86Readiness.Controls.cleared_ac_rejected
#print axioms Mettapedia.Machines.TIsa.X86ControlFlags.arithmetic_mask
#print axioms Mettapedia.Machines.TIsa.X86ControlFlags.logical_mask
#print axioms Mettapedia.Machines.TIsa.X86ControlFlags.Preserved.refl
#print axioms Mettapedia.Machines.TIsa.X86ControlFlags.Preserved.trans
#print axioms Mettapedia.Machines.TIsa.X86ControlFlags.of_register_frame
#print axioms Mettapedia.Machines.TIsa.X86ControlFlags.masked_ac
#print axioms Mettapedia.Machines.TIsa.X86ControlFlags.ac_preserved
#print axioms Mettapedia.Machines.TIsa.X86ControlFlags.Controls.carry_change_allowed
#print axioms Mettapedia.Machines.TIsa.X86ControlFlags.Controls.alignment_change_rejected
#print axioms Mettapedia.Machines.TIsa.X86RegisterIncrement.executes_control
#print axioms Mettapedia.Machines.TIsa.X86LoopHeader.compare_step_control
#print axioms Mettapedia.Machines.TIsa.X86LoopHeader.executes_control
#print axioms Mettapedia.Machines.TIsa.X86LoopLatch.executes_control
#print axioms Mettapedia.Machines.TIsa.X86CapGate.compare_step_control
#print axioms Mettapedia.Machines.TIsa.X86CapGate.executes_control
#print axioms Mettapedia.Machines.TIsa.X86Zero32.executes_control
#print axioms Mettapedia.Machines.TIsa.X86LoopEntry.gate_step_control
#print axioms Mettapedia.Machines.TIsa.X86LoopEntry.executes_control
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.word_run
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.header_run
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.latch_run
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.body_run
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.iteration_run
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.loop_run
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.entry_run
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.program_run
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.completes_profile
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.excess_profile
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.Controls.counted_profile
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.Controls.excessive_bound_profile
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.Controls.cleared_ac_rejected
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.Controls.changed_cap_refused
#print axioms Mettapedia.Machines.TIsa.X86LoopReadiness.Controls.changed_body_refused

#print axioms Mettapedia.Machines.TIsa.X86MemoryView.span_iff_area
#print axioms Mettapedia.Machines.TIsa.X86MemoryView.wordAt?_known
#print axioms Mettapedia.Machines.TIsa.X86MemoryView.wordAt?_missing
#print axioms Mettapedia.Machines.TIsa.X86MemoryView.readback_nonregister
#print axioms Mettapedia.Machines.TIsa.X86MemoryView.Controls.high_word_read
#print axioms Mettapedia.Machines.TIsa.X86MemoryView.Controls.wrapping_word_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.evaluate_p1
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.step_iff
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.readonly_readback
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.projects_original
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.readback_framed
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.correct
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.source_wp_step
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.compile_wp
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.Controls.double_with_bytes
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.Controls.wrong_result_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.NativeControls.compiled_bytes
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.NativeControls.compiled_steps
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.NativeControls.native_block
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.NativeControls.wrong_native_result_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.NativeControls.changed_descriptor_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.NativeControls.missing_descriptor_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.NativeControls.noncanonical_alias_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryScalarLibrary.NativeControls.changed_opcode_refused

#print axioms Mettapedia.Machines.TIsa.X86MemoryReadback.packed_extract
#print axioms Mettapedia.Machines.TIsa.X86MemoryReadback.wordAt?_eq_some_iff
#print axioms Mettapedia.Machines.TIsa.X86MemoryReadback.field?_bytes
#print axioms Mettapedia.Machines.TIsa.X86MemoryReadback.wordAt?_native_bytes
#print axioms Mettapedia.Machines.TIsa.X86MemoryReadback.wordAt?_narrow_bytes
#print axioms Mettapedia.Machines.TIsa.X86MemoryReadback.byte_observed
#print axioms Mettapedia.Machines.TIsa.X86MemoryReadback.byte_words_observed
#print axioms Mettapedia.Machines.TIsa.X86MemoryReadback.source_load_word
#print axioms Mettapedia.Machines.TIsa.X86MemoryBounds.facts
#print axioms Mettapedia.Machines.TIsa.X86MemoryBounds.bounds_preserves_readback
#print axioms Mettapedia.Machines.TIsa.X86MemoryBounds.source_classifies
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.load_represents
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.captured_load
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.source_firing
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.word_source_and_native
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.truncated_word_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.rejected_bounds
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.source_bounds_failure
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.enabled_at_entry

#print axioms Mettapedia.Machines.TIsa.X86ControlFlags.flags_present
#print axioms Mettapedia.Machines.TIsa.X86Bounds.merged_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.subtract_step_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.subtract_count_step_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.add_step_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.compare_step_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.head_prefix_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.offset_prefix_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.arithmetic_prefix_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.borrow_prefix_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.range_prefix_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.classifies_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.source_classifies_control
#print axioms Mettapedia.Machines.TIsa.X86Bounds.succeeds_control
#print axioms Mettapedia.Machines.TIsa.X86P1FieldLoadCapture.load_executes_control
#print axioms Mettapedia.Machines.TIsa.X86MemoryBounds.source_classifies_profile
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.captured_load_profile
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.word_source_and_native_profile
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.rejected_bounds_profile
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.cleared_ac_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.rejection_cleared_ac_refused
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.test_step_control
#print axioms Mettapedia.Machines.TIsa.X86BranchGate.executes_control
#print axioms Mettapedia.Machines.TIsa.X86Conditional.gate_control
#print axioms Mettapedia.Machines.TIsa.X86Readiness.Profile.after_control
#print axioms Mettapedia.Machines.TIsa.X86Readiness.compatible
#print axioms Mettapedia.Machines.TIsa.X86Readiness.conditional_at
#print axioms Mettapedia.Machines.TIsa.X86Readiness.conditional_wp
#print axioms Mettapedia.Machines.TIsa.X86Readiness.Controls.branch_copy_mask_add_profile
#print axioms Mettapedia.Machines.TIsa.X86Readiness.Controls.branch_cleared_ac_rejected
#print axioms Mettapedia.Machines.TIsa.X86Readiness.Controls.nonboolean_condition_refused
#print axioms Mettapedia.Machines.TIsa.X86Readiness.Controls.branch_opcode_rejected
#print axioms Mettapedia.Machines.TIsa.X86ScalarLibrary.source_evaluate_p1
#print axioms Mettapedia.Machines.TIsa.X86ScalarLibrary.compile_wp
#print axioms Mettapedia.Machines.TIsa.X86ScalarLibrary.conditional_wp
#print axioms Mettapedia.Machines.TIsa.X86ScalarLibrary.Controls.copy_mask_add
#print axioms Mettapedia.Machines.TIsa.X86ScalarLibrary.Controls.wrong_result_refused
#print axioms Mettapedia.Machines.TIsa.X86ScalarLibrary.Controls.changed_opcode_rejected
#print axioms Mettapedia.Machines.TIsa.X86ScalarLibrary.Controls.branch_copy_mask_add
#print axioms Mettapedia.Machines.TIsa.X86ScalarLibrary.Controls.nonboolean_condition_refused

#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackBody.alu_fetched
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackBody.read_and_calculate
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackBody.executes
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackBody.false_return_refused
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackBody.artifact_bytes_exact
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackBody.artifact_body_exact
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackBody.Controls.all_operations
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackBody.Controls.zero_result_is_value
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackBody.Controls.changed_operation_rejected
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackBody.Controls.input_witness
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.canonical_iff_signed
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.narrow_representation
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.area_signed_upper
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.area_signed_upper_strict
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.SharedDataEntry.geometry
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.physicalKey_injective
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.physical_images_disjoint
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.successor_representation
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.physicalKey_offset
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.outside_output
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.Controls.low_geometry
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.Controls.high_stack_returns_to_zero
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.Controls.signed_zero_crossing
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.Controls.unsigned_zero_crossing_refused
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.Controls.low_end_inclusive
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.Controls.stack_end_requires_post_canonical
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.Controls.canonical_keys_distinct
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.Controls.unrestricted_key_alias
#print axioms Mettapedia.Machines.TIsa.X86CanonicalSpan.Controls.empty_area_does_not_admit_base
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackContract.BodyFacts.toInputs
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackContract.executes
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackContract.Controls.inhabited
#print axioms Mettapedia.Machines.TIsa.X86BinaryCallbackContract.Controls.all_operations
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.readback_exact
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.guard_candidate
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.checked_iff
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.observes
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.observed_exact
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.checked_iff_observed
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.observed_resource_step
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.commit_eq_update
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.realized
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.Controls.aliased_native
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.Controls.wrong_result_refused
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.Controls.wrong_point_refused
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.Controls.missing_output_refused
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.Controls.missing_input_refused
#print axioms Mettapedia.Machines.TIsa.X86ScalarProducer.Controls.extra_operand_refused
#print axioms Mettapedia.Machines.TIsa.X86OutcomeTail.executes
#print axioms Mettapedia.Machines.TIsa.X86OutcomeTail.finished_result
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.Controls.fixture_end_unmapped
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.captured_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.executes
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.rejected_prefix
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.load_bounds_invalid
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.public_invalid
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.Controls.end_pointer_returns_invalid
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.Controls.end_pointer_wrong_outcome
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.Controls.changed_handler_displacement
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.Controls.end_pointer_unmapped
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.access_zero_iff
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.access_none_iff
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.captured_failure
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.guarded_transition
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.failure_transition_iff
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.admitted_failure_executes
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.Controls.end_pointer_fires
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.Controls.legal_pointer_refused
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.Controls.missing_capability_refused
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.Controls.wrong_mode_refused
#print axioms Mettapedia.Machines.TIsa.X86P1BoundsFailureSource.Controls.accepted_load_excludes_failure
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

#print axioms Mettapedia.Machines.TIsa.X86SibStore.effective_disp32
#print axioms Mettapedia.Machines.TIsa.X86SibStore.fetch_to_dispatch_sib
#print axioms Mettapedia.Machines.TIsa.X86SibStore.handler32
#print axioms Mettapedia.Machines.TIsa.X86SibStore.fetched32
#print axioms Mettapedia.Machines.TIsa.X86SibStore.executes
#print axioms Mettapedia.Machines.TIsa.X86SibStore.Controls.dword_writes_only_low
#print axioms Mettapedia.Machines.TIsa.X86SibStore.Controls.negative_displacement
#print axioms Mettapedia.Machines.TIsa.X86SibStore.Controls.wrong_value_refused
#print axioms Mettapedia.Machines.TIsa.X86SibStore.Controls.changed_sib_refused
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.source_instruction
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.containing_span
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.tail_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.captured_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.executes

#print axioms Mettapedia.Machines.TIsa.X86MemoryView.wordAt?_congr
#print axioms Mettapedia.Machines.TIsa.X86MemoryView.field?_congr
#print axioms Mettapedia.Machines.TIsa.X86MemoryView.readback_framed
#print axioms Mettapedia.Machines.TIsa.X86MemoryView.readback_store_frame
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.entryFixture
#print axioms Mettapedia.Machines.TIsa.X86MemoryStore.source_store_iff
#print axioms Mettapedia.Machines.TIsa.X86MemoryStore.physical_byte_outside
#print axioms Mettapedia.Machines.TIsa.X86MemoryStore.stored_readback32
#print axioms Mettapedia.Machines.TIsa.X86MemoryStore.store_represents
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.prefix_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.prefix_loaded
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.source_access_fits
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.captured_store_profile
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.source_firing
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.source_and_native
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.written_first_byte
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.wrong_output_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.readonly_represents
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.readonly_store_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.descriptor_alias_changes
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.descriptor_alias_not_protected

#print axioms Mettapedia.Machines.TIsa.X86Bounds.execution_prefix_known
#print axioms Mettapedia.Machines.TIsa.X86Bounds.execution_prefix_frame
#print axioms Mettapedia.Machines.TIsa.X86Bounds.boundsSteps_of_fits
#print axioms Mettapedia.Machines.TIsa.X86Bounds.success_prefix_frame
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.captured_store_profile_prefixes
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.source_progress
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.source_step_iff
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.source_access_address
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.captured_store_wp
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.source_wp
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.wp_and_native
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.impossible_post_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.source_and_native_prefixes
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.omitted_prefix_write_refused
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.execution_prefix_frame
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.image_executes
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.captured_edges
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.source_failure_iff
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.failure_excludes_store
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.invalid_bytes
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.failed_prefix
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.failed_store
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.Controls.source_rejects
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.Controls.rejected_data_unmapped
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.Controls.runs_to_invalid
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.Controls.fired_outcome_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.Controls.changed_handler_delta
#print axioms Mettapedia.Machines.TIsa.X86Assembler.labels_inside
#print axioms Mettapedia.Machines.TIsa.X86Assembler.assemble_correct
#print axioms Mettapedia.Machines.TIsa.X86Assembler.assemble_checked
#print axioms Mettapedia.Machines.TIsa.X86Assembler.assemble_succeeds
#print axioms Mettapedia.Machines.TIsa.X86Assembler.Controls.forward_assembled
#print axioms Mettapedia.Machines.TIsa.X86Assembler.Controls.backward_assembled
#print axioms Mettapedia.Machines.TIsa.X86Assembler.Controls.unknown_label_refused
#print axioms Mettapedia.Machines.TIsa.X86Assembler.Controls.duplicate_label_refused
#print axioms Mettapedia.Machines.TIsa.X86Assembler.Controls.overflow_refused
#print axioms Mettapedia.Machines.TIsa.X86Assembler.Controls.changed_target_byte_refused
#print axioms Mettapedia.Machines.TIsa.X86AssemblerExecution.assembled_jump
#print axioms Mettapedia.Machines.TIsa.X86AssemblerExecution.assembled_conditional
#print axioms Mettapedia.Machines.TIsa.X86AssemblerCapture.trailer_assembled
#print axioms Mettapedia.Machines.TIsa.X86AssemblerCapture.all_trailers
#print axioms Mettapedia.Machines.TIsa.X86AssemblerCapture.invalid_executes
#print axioms Mettapedia.Machines.TIsa.X86AssemblerCapture.Controls.native_jump
#print axioms Mettapedia.Machines.TIsa.X86AssemblerCapture.Controls.wrong_target_refused
#print axioms Mettapedia.Machines.TIsa.X86Assembler.emitAt_append
#print axioms Mettapedia.Machines.TIsa.X86Assembler.emitAt_split
#print axioms Mettapedia.Machines.TIsa.X86Assembler.labelsAt_exact
#print axioms Mettapedia.Machines.TIsa.X86Assembler.label_lookup
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.ofAssembly
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.nativeInput
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.realizes
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.reflects
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.Controls.generated_realization
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.Controls.logical_and_native
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.Controls.colocated_distinct_names
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.Controls.nonboolean_no_source_step
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.Controls.raw_nonboolean_runs
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.Controls.reflection
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.Controls.captured_register
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.Controls.image_branch_is_fused
#print axioms Mettapedia.Machines.TIsa.X86BranchCompiler.Result.next_entry
#print axioms Mettapedia.Machines.TIsa.X86BranchRegion.fallthrough
#print axioms Mettapedia.Machines.TIsa.X86BranchRegion.early_exit
#print axioms Mettapedia.Machines.TIsa.X86BranchRegion.Controls.assembled
#print axioms Mettapedia.Machines.TIsa.X86BranchRegion.Controls.boundaries
#print axioms Mettapedia.Machines.TIsa.X86BranchRegion.Controls.duplicated_boundary_refused
#print axioms Mettapedia.Machines.TIsa.X86BranchRegion.Controls.second_outcomes
#print axioms Mettapedia.Machines.TIsa.X86BranchRegion.Controls.skipped_resource_missing
#print axioms Mettapedia.Machines.TIsa.X86BranchRegion.Controls.second_nonboolean_refused
#print axioms Mettapedia.Machines.TIsa.X86BranchRegion.Controls.early_skips_missing_resource
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.compile?_iff
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.ofCompilation
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Layout.site
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Ready.pointer
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Ready.revalue
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.advance
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.realizes_step
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.reflects_step
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.realizes_path
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.reflects_path
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.source_path_iff
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.realizes_multistep
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.compiled
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.wrong_flow_same_bytes
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.wrong_flow_refused
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.wrong_owner_same_bytes
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.wrong_owner_refused
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.three_native
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.early_native
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.middle_native
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.loop_native
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.missing_active_resource
#print axioms Mettapedia.Machines.TIsa.X86BranchGraph.Controls.raw_execution_without_source_authority
#print axioms Mettapedia.Machines.TIsa.X86WordPrimitive.captured_bytes
#print axioms Mettapedia.Machines.TIsa.X86WordPrimitive.computes
#print axioms Mettapedia.Machines.TIsa.X86WordPrimitive.other_logical
#print axioms Mettapedia.Machines.TIsa.X86WordPrimitive.executes
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.compile?_iff
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.ofCompilation
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Ready.resume
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Node.source_finish
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.realizes_selected
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.source_selected_iff
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.counted_lift
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.counted_erase
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.realizes_counted
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.realizes_multistep
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.reflects_counted
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Controls.compiled
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Controls.missing_live_input_refused
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Controls.missing_live_transfer_refused
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Controls.unreadable_elision_same_bytes
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Controls.unreadable_elision_refused
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Controls.absent_destinations
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Controls.not_all_initialized
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Controls.success
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.Controls.early_exit

#print axioms Mettapedia.Machines.TIsa.X86MaskedFlags.write_flags
#print axioms Mettapedia.Machines.TIsa.X86MaskedFlags.merged_control
#print axioms Mettapedia.Machines.TIsa.X86Shift.left_value
#print axioms Mettapedia.Machines.TIsa.X86Shift.right_value
#print axioms Mettapedia.Machines.TIsa.X86Shift.handler
#print axioms Mettapedia.Machines.TIsa.X86Shift.fetched
#print axioms Mettapedia.Machines.TIsa.X86Shift.result_frame
#print axioms Mettapedia.Machines.TIsa.X86Shift.source_value
#print axioms Mettapedia.Machines.TIsa.X86Shift.source_rejects64
#print axioms Mettapedia.Machines.TIsa.X86Shift.native_masks64
#print axioms Mettapedia.Machines.TIsa.X86Shift.Controls.executes
#print axioms Mettapedia.Machines.TIsa.X86Shift.Controls.shift_left_high_bit
#print axioms Mettapedia.Machines.TIsa.X86Shift.Controls.shift_right_high_bit
#print axioms Mettapedia.Machines.TIsa.X86Shift.Controls.wrong_direction_refused
#print axioms Mettapedia.Machines.TIsa.X86Shift.Controls.oversized_count_executes
#print axioms Mettapedia.Machines.TIsa.X86SignExtension.sign_slice
#print axioms Mettapedia.Machines.TIsa.X86SignExtension.logext
#print axioms Mettapedia.Machines.TIsa.X86Shift.signed_value
#print axioms Mettapedia.Machines.TIsa.X86Shift.Controls.shift_signed_high_bit
#print axioms Mettapedia.Machines.TIsa.X86Shift.Controls.unsigned_answer_refused
#print axioms Mettapedia.Machines.TIsa.X86ShiftBlock.source_evaluate_p1
#print axioms Mettapedia.Machines.TIsa.X86ShiftBlock.lower?_source
#print axioms Mettapedia.Machines.TIsa.X86ShiftBlock.lower?_large_refused
#print axioms Mettapedia.Machines.TIsa.X86ShiftBlock.lower?_protected_refused
#print axioms Mettapedia.Machines.TIsa.X86ShiftBlock.executes_block
#print axioms Mettapedia.Machines.TIsa.X86ShiftBlock.Controls.in_place
#print axioms Mettapedia.Machines.TIsa.X86DataPrimitive.executes
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.ShiftControls.compiled
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.ShiftControls.success
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.ShiftControls.early_exit
#print axioms Mettapedia.Machines.TIsa.X86MixedRegion.ShiftControls.absent_destinations

#print axioms Mettapedia.Machines.TIsa.RowTableInitialization.initialize_ready
#print axioms Mettapedia.Machines.TIsa.RowTableInitialization.initialize_outside
#print axioms Mettapedia.Machines.TIsa.RowTableInitialization.Controls.empty_view_does_not_establish_zero_tail
#print axioms Mettapedia.Machines.TIsa.RowTableInitialization.Controls.shortened_clear_is_incomplete
#print axioms Mettapedia.Machines.TIsa.X86LogicalRecipes.lower?_source
#print axioms Mettapedia.Machines.TIsa.X86LogicalRecipes.correct
#print axioms Mettapedia.Machines.TIsa.X86LogicalRecipes.compile_wp
#print axioms Mettapedia.Machines.TIsa.X86LogicalRecipes.Controls.lowering_guards
#print axioms Mettapedia.Machines.TIsa.X86LogicalRecipes.Controls.copy_first_alias_is_incorrect
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeLogical.lowerCode?_source
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeLogical.compile
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeLogical.compile_live
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeLogical.Controls.admission_controls
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeLogical.Controls.missing_source_operand
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeLogical.Controls.alias_native_bytes
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeLogical.admit?_checks
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeLogical.admitted_source_exec
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeLogical.compile_admitted
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeLogical.Controls.admission_reads_actual_registers
#print axioms Mettapedia.Machines.TIsa.RegisterCodeLowering.admitted_source_exec_on
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeScalar.lower?_source
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeScalar.lower?_roundtrip
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeScalar.compile_admitted_on
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeScalar.compile_admitted
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeScalar.Controls.mixed_source_results
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeScalar.Controls.missing_operand_rejected
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeScalar.Controls.arbitrary_dead_registers
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeScalar.Controls.exact_native_steps
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeScalar.Controls.exact_native_bytes
#print axioms Mettapedia.Machines.TIsa.X86RegisterCodeScalar.Controls.wrong_operation_changes_result
#print axioms Mettapedia.Machines.TIsa.X86P1ScalarReadiness.arithmetic_stable
#print axioms Mettapedia.Machines.TIsa.X86P1ScalarReadiness.shifts_stable
#print axioms Mettapedia.Machines.TIsa.X86P1ScalarReadiness.stable
#print axioms Mettapedia.Machines.TIsa.X86P1ScalarReadiness.compile_wp
#print axioms Mettapedia.Machines.TIsa.X86P1ScalarLibrary.Controls.alignment_enabled_at_entry
#print axioms Mettapedia.Machines.TIsa.X86P1ScalarLibrary.Controls.compiled_aliasing_profile
#print axioms Mettapedia.Machines.TIsa.X86P1ScalarLibrary.Controls.cleared_ac_rejected
#print axioms Mettapedia.Machines.TIsa.X86RowTableMark.source_marks
#print axioms Mettapedia.Machines.TIsa.X86RowTableMark.Controls.published_mark_changes
#print axioms Mettapedia.Machines.TIsa.X86RowTableMark.Controls.unchecked_tail_write_breaks_invariant

#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.Controls.fixture_premise_byte
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.Controls.fixture_premise_suffix_unobserved
#print axioms Mettapedia.Machines.TIsa.X86P1OutputCapture.Controls.fixture_output_unobserved
#print axioms Mettapedia.Machines.TIsa.X86P1SuccessCapture.Controls.entryObservations
#print axioms Mettapedia.Machines.TIsa.X86P1SuccessCapture.Controls.premise_capacity_not_full_backing
#print axioms Mettapedia.Machines.TIsa.X86P1SuccessCapture.Controls.output_not_initially_readable
#print axioms Mettapedia.Machines.TIsa.X86AllowanceCall.Setup.initializes
#print axioms Mettapedia.Machines.TIsa.X86AllowanceCall.Writeback.publishes
#print axioms Mettapedia.Machines.TIsa.X86AllowanceCall.Inputs.saves
#print axioms Mettapedia.Machines.TIsa.X86AllowanceCall.Inputs.enters
#print axioms Mettapedia.Machines.TIsa.X86AllowanceCall.Inputs.returns
#print axioms Mettapedia.Machines.TIsa.X86AllowanceCall.Inputs.executes
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.load_observes
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.located
#print axioms Mettapedia.Machines.TIsa.X86P1LoadCapture.Controls.previous_reject_not_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.Controls.reject_target_is_invalid_input
#print axioms Mettapedia.Machines.TIsa.X86P1QwordLoadCapture.Controls.shifted_reject_not_loaded
#print axioms Mettapedia.Machines.TIsa.X86P1CompareCapture.Controls.no_materialized_boolean
#print axioms Mettapedia.Machines.TIsa.X86P1QwordCompareCapture.Controls.no_materialized_boolean
#print axioms Mettapedia.Machines.TIsa.X86P1IfCapture.arm_starts
#print axioms Mettapedia.Machines.TIsa.X86P1QwordGuardCapture.arm_starts
#print axioms Mettapedia.Machines.TIsa.X86P1RefusedCapture.public_refused
#print axioms Mettapedia.Machines.TIsa.X86P1InvalidCapture.rejected_prefix
#print axioms Mettapedia.Machines.TIsa.X86P1SuccessCapture.Controls.control
#print axioms Mettapedia.Machines.TIsa.X86AssemblerCapture.all_invalid_entries
#print axioms Mettapedia.Machines.TIsa.X86AssemblerCapture.Controls.previous_formula_refused
#print axioms Mettapedia.Machines.TIsa.X86BoundedLoadCapture.reject_targets_invalid
#print axioms Mettapedia.Machines.TIsa.X86BoundedStoreCapture.reject_targets_invalid
#print axioms Mettapedia.Machines.TIsa.X86LoopBottomLatch.executes
#print axioms Mettapedia.Machines.TIsa.X86LoopBottomLatch.realizes
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.latch_then_header
#print axioms Mettapedia.Machines.TIsa.X86P1LoopCapture.former_templates_refused
#print axioms Mettapedia.Machines.TIsa.X86P1LoopEntryCapture.entry_realizes
#print axioms Mettapedia.Machines.TIsa.X86P1LoopEntryCapture.entry_rejects
#print axioms Mettapedia.Machines.TIsa.X86AllowanceCall.saves_match_layout
#print axioms Mettapedia.Machines.TIsa.X86AllowanceCall.restores_match_layout
#print axioms Mettapedia.Machines.TIsa.X86AllowanceCall.exit_not_plain_epilogue
#print axioms Mettapedia.Machines.TIsa.X86IndexedAddress.succeeds
#print axioms Mettapedia.Machines.TIsa.X86IndexedAddress.rejects
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.invalid_entry_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.direct_span
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.guard_span
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.load_span
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.guard_checked
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.guard_succeeds
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.guard_rejects
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.no_prefixed_zero_store
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.guard_not_overflow_form
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.guard_stale_target_refused
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.guard_base_field_refused
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.zero_prefix_absent
#print axioms Mettapedia.Machines.TIsa.X86P1SibStoreCapture.stale_reject_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryFieldLoad.Controls.stale_displacement_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.captured_mov_profile
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.captured_checked_store_profile_prefixes
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.unguarded_direct_store_escapes
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.exit_from_end
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.captured_reject
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.guard_failed
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.Controls.previous_handler_refused
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStore.Controls.guardFixture
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.Controls.guard_runs_to_invalid
#print axioms Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure.Controls.guard_last_index_passes
