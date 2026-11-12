import Mettapedia.Machines.TIsa.X86RegisterRefinement

/-!
# Register encoding fields against the Sail x86 model

REX and ModRM bytes use the direct emitter's arithmetic layout. Their fields
are read by the imported Sail accessors, including the REX extension bits.
These results do not replace instruction fetch, opcode dispatch or execution.
-/

set_option autoImplicit false
set_option maxRecDepth 65536

namespace Mettapedia.Machines.TIsa.X86RegisterEncoding

open _root_.X86Registers

def rex (wide : Bool) (register base : Fin 16) : BitVec 8 :=
  BitVec.ofNat 8 (64 + (if wide then 8 else 0) + 4 * (register.val / 8) + base.val / 8)

def modRM (register base : Fin 16) : BitVec 8 :=
  BitVec.ofNat 8 (192 + 8 * (register.val % 8) + base.val % 8)

theorem register_mode (register base : Fin 16) :
    Functions._get_modr_m_mod (modRM register base) = (3#2) := by
  revert register base
  decide

theorem source_register (wide : Bool) (register base : Fin 16) :
    Functions.reg_index (Functions._get_modr_m_reg (modRM register base))
      (rex wide register base) (2#2) = BitVec.ofNat 4 register.val := by
  revert wide register base
  decide

theorem destination_register (wide : Bool) (register base : Fin 16) :
    Functions.reg_index (Functions._get_modr_m_r_m (modRM register base))
      (rex wide register base) (0#2) = BitVec.ofNat 4 base.val := by
  revert wide register base
  decide

theorem operand_width (wide : Bool) (register base : Fin 16) :
    Functions.logbitp_bits 3 (rex wide register base) = wide := by
  revert wide register base
  decide

namespace Controls

example : [rex true 8 9, (137 : BitVec 8), modRM 8 9] = [77, 137, 193] := by decide

example : Functions.reg_index (Functions._get_modr_m_reg (modRM 8 0)) (rex true 0 8) 2 ≠ 8 := by decide

example : Functions.reg_index (Functions._get_modr_m_r_m (modRM 0 8)) (rex true 8 0) 0 ≠ 8 := by decide

end Controls

end Mettapedia.Machines.TIsa.X86RegisterEncoding
