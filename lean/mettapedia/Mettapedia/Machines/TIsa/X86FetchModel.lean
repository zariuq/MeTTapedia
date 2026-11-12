import Mettapedia.Machines.TIsa.X86EffectiveFetch

/-!
# The pinned Sail x86 instruction-fetch definition

The upstream fetch/decode body is retained. Vector decoders outside this
fragment are ordinary function data without assumed laws; the legacy MOV
path does not invoke them. Shadowed type names are qualified. Host IR
generation is omitted for the fetch definition, leaving kernel checking and
reduction unchanged. Execution and native-byte linkage are separate proofs.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2_000_000

namespace X86Registers

class VectorOpcodeHandlers where
  vex_decode_and_execute : proc_mode → BitVec 48 → BitVec 48 → BitVec 52 →
    BitVec 8 → BitVec 24 → SailM Unit
  evex_decode_and_execute : proc_mode → BitVec 48 → BitVec 48 → BitVec 52 →
    BitVec 8 → BitVec 32 → SailM Unit

end X86Registers

section
variable [X86Registers.MemoryPrimitives] [X86Registers.OtherOpcodeHandlers]
variable [X86Registers.VectorOpcodeHandlers]

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/FetchFunctions.lean.inc"
  sha256 "614abc4a994c442007bf868f7bb4f4a912380d39dae8bb831cb380240946f74d"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]

end
