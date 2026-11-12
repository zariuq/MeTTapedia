import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace X86Registers

abbrev bit := (BitVec 1)

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

inductive regfp where
  | RFull (_ : String)
  | RSlice (_ : (String × Nat × Nat))
  | RSliceBit (_ : (String × Nat))
  | RField (_ : (String × String))
  deriving Inhabited, BEq, Repr
  open regfp

abbrev regfps := (List regfp)

inductive niafp where
  | NIAFP_successor (_ : Unit)
  | NIAFP_concrete_address (_ : (BitVec 64))
  | NIAFP_indirect_address (_ : Unit)
  deriving Inhabited, BEq, Repr
  open niafp

abbrev niafps := (List niafp)

inductive diafp where
  | DIAFP_none (_ : Unit)
  | DIAFP_concrete (_ : (BitVec 64))
  | DIAFP_reg (_ : regfp)
  deriving Inhabited, BEq, Repr
  open diafp

inductive read_kind where | Read_plain | Read_reserve | Read_acquire | Read_exclusive | Read_exclusive_acquire | Read_stream | Read_ifetch | Read_RISCV_acquire | Read_RISCV_strong_acquire | Read_RISCV_reserved | Read_RISCV_reserved_acquire | Read_RISCV_reserved_strong_acquire | Read_X86_locked
  deriving BEq, Inhabited, Repr
  open read_kind

inductive write_kind where | Write_plain | Write_conditional | Write_release | Write_exclusive | Write_exclusive_release | Write_RISCV_release | Write_RISCV_strong_release | Write_RISCV_conditional | Write_RISCV_conditional_release | Write_RISCV_conditional_strong_release | Write_X86_locked
  deriving BEq, Inhabited, Repr
  open write_kind

inductive a64_barrier_domain where | A64_FullShare | A64_InnerShare | A64_OuterShare | A64_NonShare
  deriving BEq, Inhabited, Repr
  open a64_barrier_domain

inductive a64_barrier_type where | A64_barrier_all | A64_barrier_LD | A64_barrier_ST
  deriving BEq, Inhabited, Repr
  open a64_barrier_type

inductive barrier_kind where
  | Barrier_Sync (_ : Unit)
  | Barrier_LwSync (_ : Unit)
  | Barrier_Eieio (_ : Unit)
  | Barrier_Isync (_ : Unit)
  | Barrier_DMB (_ : (a64_barrier_domain × a64_barrier_type))
  | Barrier_DSB (_ : (a64_barrier_domain × a64_barrier_type))
  | Barrier_ISB (_ : Unit)
  | Barrier_MIPS_SYNC (_ : Unit)
  | Barrier_RISCV_rw_rw (_ : Unit)
  | Barrier_RISCV_r_rw (_ : Unit)
  | Barrier_RISCV_r_r (_ : Unit)
  | Barrier_RISCV_rw_w (_ : Unit)
  | Barrier_RISCV_w_w (_ : Unit)
  | Barrier_RISCV_w_rw (_ : Unit)
  | Barrier_RISCV_rw_r (_ : Unit)
  | Barrier_RISCV_r_w (_ : Unit)
  | Barrier_RISCV_w_r (_ : Unit)
  | Barrier_RISCV_tso (_ : Unit)
  | Barrier_RISCV_i (_ : Unit)
  | Barrier_x86_MFENCE (_ : Unit)
  deriving Inhabited, BEq, Repr
  open barrier_kind

inductive trans_kind where | Transaction_start | Transaction_commit | Transaction_abort
  deriving BEq, Inhabited, Repr
  open trans_kind

inductive cache_op_kind where | Cache_op_D_IVAC | Cache_op_D_ISW | Cache_op_D_CSW | Cache_op_D_CISW | Cache_op_D_ZVA | Cache_op_D_CVAC | Cache_op_D_CVAU | Cache_op_D_CIVAC | Cache_op_I_IALLUIS | Cache_op_I_IALLU | Cache_op_I_IVAU
  deriving BEq, Inhabited, Repr
  open cache_op_kind

inductive instruction_kind where
  | IK_barrier (_ : barrier_kind)
  | IK_mem_read (_ : read_kind)
  | IK_mem_write (_ : write_kind)
  | IK_mem_rmw (_ : (read_kind × write_kind))
  | IK_branch (_ : Unit)
  | IK_trans (_ : trans_kind)
  | IK_simple (_ : Unit)
  | IK_cache_op (_ : cache_op_kind)
  deriving Inhabited, BEq, Repr
  open instruction_kind

abbrev sbits k_n := (BitVec k_n)

inductive exception where
  | Emsg (_ : String)
  | Syscall (_ : Unit)
  deriving Inhabited, BEq, Repr
  open exception

abbrev regtype := (sbits 64)

abbrev rflagsbits := (BitVec 32)

structure struct_paging_entry_no_page_fault_p where
  supervisor_mode_access_type : Int
  deriving BEq, Inhabited, Repr

abbrev ia32e_page_tablesbits := (BitVec 64)

abbrev vex_prefixes := (BitVec 24)

abbrev vex2_byte1 := (BitVec 8)

abbrev vex3_byte1 := (BitVec 8)

abbrev vex3_byte2 := (BitVec 8)

abbrev evex_prefixes := (BitVec 32)

abbrev evex_byte1 := (BitVec 8)

abbrev evex_byte2 := (BitVec 8)

abbrev evex_byte3 := (BitVec 8)

abbrev modr_m := (BitVec 8)

abbrev sib := (BitVec 8)

abbrev cr0bits := (BitVec 32)

abbrev cr3bits := (BitVec 64)

abbrev cr4bits := (BitVec 22)

abbrev cr8bits := (BitVec 4)

abbrev xcr0bits := (BitVec 64)

abbrev ia32_eferbits := (BitVec 12)

abbrev msr_index := Nat

inductive proc_mode where | Mode_64bit | Mode_Compatibility | Mode_Protected | Mode_Real | Mode_SMM
  deriving BEq, Inhabited, Repr
  open proc_mode

abbrev prefixes := (BitVec 52)

abbrev hidden_segment_registerbits := (BitVec 112)

abbrev segment_selectorbits := (BitVec 16)

abbrev interrupt_trap_gate_descriptorbits := (BitVec 128)

abbrev interrupt_trap_gate_descriptor_attributesbits := (BitVec 16)

abbrev gdtr_idtrbits := (BitVec 80)

abbrev code_segment_descriptorbits := (BitVec 64)

abbrev code_segment_descriptor_attributesbits := (BitVec 16)

abbrev data_segment_descriptorbits := (BitVec 64)

abbrev data_segment_descriptor_attributesbits := (BitVec 16)

abbrev system_segment_descriptorbits := (BitVec 128)

abbrev system_segment_descriptor_attributesbits := (BitVec 16)

abbrev call_gate_descriptorbits := (BitVec 128)

abbrev call_gate_descriptor_attributesbits := (BitVec 16)

abbrev ia32e_pml4ebits := (BitVec 64)

abbrev ia32e_pdpte_1gb_pagebits := (BitVec 64)

abbrev ia32e_pdpte_pg_dirbits := (BitVec 64)

abbrev ia32e_pde_2mb_pagebits := (BitVec 64)

abbrev ia32e_pde_pg_tablebits := (BitVec 64)

abbrev ia32e_pte_4k_pagebits := (BitVec 64)

structure struct_wz32 where
  regtype : Int
  deriving BEq, Inhabited, Repr

structure struct_wz64 where
  regtype : Int
  deriving BEq, Inhabited, Repr

structure struct_wz128 where
  regtype : Int
  deriving BEq, Inhabited, Repr

abbrev address_size := Int

abbrev moffset_size := Int

abbrev base_reg_idx := Nat

abbrev seg_reg_idx := Nat

inductive Register : Type where
  | haltAddrReg
  | ssr_hidden_attrs
  | ssr_hidden_limits
  | ssr_hidden_bases
  | ssr_visibles
  | strs
  | zmms
  | seg_hidden_limits
  | seg_hidden_bases
  | seg_hidden_attrs
  | r15
  | r14
  | r13
  | r12
  | r11
  | r10
  | r9
  | r8
  | rbp
  | rsp
  | rdi
  | rsi
  | rdx
  | rcx
  | rbx
  | rax
  | msrs
  | seg_visibles
  | rflags
  | ctrs
  | fault_reg
  | ms_reg
  | log_register_writes
  | marking_view
  | app_view
  | rip
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .haltAddrReg => (BitVec 48)
  | .ssr_hidden_attrs => (Vector (BitVec 16) 2)
  | .ssr_hidden_limits => (Vector (BitVec 32) 2)
  | .ssr_hidden_bases => (Vector (BitVec 64) 2)
  | .ssr_visibles => (Vector (BitVec 16) 2)
  | .strs => (Vector (BitVec 80) 2)
  | .zmms => (Vector (BitVec 512) 32)
  | .seg_hidden_limits => (Vector (BitVec 32) 6)
  | .seg_hidden_bases => (Vector (BitVec 64) 6)
  | .seg_hidden_attrs => (Vector (BitVec 16) 6)
  | .r15 => (BitVec 64)
  | .r14 => (BitVec 64)
  | .r13 => (BitVec 64)
  | .r12 => (BitVec 64)
  | .r11 => (BitVec 64)
  | .r10 => (BitVec 64)
  | .r9 => (BitVec 64)
  | .r8 => (BitVec 64)
  | .rbp => (BitVec 64)
  | .rsp => (BitVec 64)
  | .rdi => (BitVec 64)
  | .rsi => (BitVec 64)
  | .rdx => (BitVec 64)
  | .rcx => (BitVec 64)
  | .rbx => (BitVec 64)
  | .rax => (BitVec 64)
  | .msrs => (Vector (BitVec 64) 7)
  | .seg_visibles => (Vector (BitVec 16) 6)
  | .rflags => (BitVec 32)
  | .ctrs => (Vector (BitVec 64) 17)
  | .fault_reg => Bool
  | .ms_reg => Bool
  | .log_register_writes => Bool
  | .marking_view => Bool
  | .app_view => Bool
  | .rip => (BitVec 64)



abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception



instance : Inhabited (RegisterRef RegisterType (BitVec 32)) where
  default := .Reg rflags
instance : Inhabited (RegisterRef RegisterType (BitVec 48)) where
  default := .Reg haltAddrReg
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg rip
instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg app_view
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 17)) where
  default := .Reg ctrs
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 16) 2)) where
  default := .Reg ssr_visibles
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 32) 2)) where
  default := .Reg ssr_hidden_limits
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 2)) where
  default := .Reg ssr_hidden_bases
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 80) 2)) where
  default := .Reg strs
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 512) 32)) where
  default := .Reg zmms
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 16) 6)) where
  default := .Reg seg_visibles
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 32) 6)) where
  default := .Reg seg_hidden_limits
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 6)) where
  default := .Reg seg_hidden_bases
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 7)) where
  default := .Reg msrs
