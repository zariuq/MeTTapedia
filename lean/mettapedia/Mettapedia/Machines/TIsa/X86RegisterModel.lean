import Mettapedia.Machines.TIsa.SailSupport
import Mettapedia.Machines.TIsa.SailInteger

/-!
# Sail-generated x86 general-register semantics

This fragment comes from sail-x86-from-acl2 commit
0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf, sliced with Sail commit
8eb1fb6b5bf9f18c0f89f71e94ff0c5894acd7c1. The complete generated architectural
state and exception types are retained. The accessor, register-field and MOV
handler function graph is sliced; generated emulator initializers are omitted.

The generated unused fake-real import is omitted. The pure diagnostic output
primitive uses Sail's output abstraction; native refinement disables diagnostic
logging. External memory operations remain explicit parameters, with no laws
assumed. The integer AND helper has a checked termination measure. No instruction
fetch, opcode-dispatch or whole-emitter theorem is asserted.
-/

set_option autoImplicit true

namespace X86Registers

def print_bits {width : Nat} (label : String) (value : BitVec width) : Unit :=
  Sail.print (label ++ Sail.BitVec.toFormatted value)

end X86Registers

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/Defs.lean.inc"
  sha256 "e64866f88c88acf12a03805a076db45bf5f635e276352537066fc250627a8d62" imports [Sail]

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/Specialization.lean.inc"
  sha256 "733332f548d7e5b41f92374198a365901eb763f988f16963ff76101e64e61854"
  imports [Sail, X86Registers.Defs]

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/Memory.lean.inc"
  sha256 "a103a2eb873c64223e09235daf2e8cb4079a99978df32c9817af39270d9a6d9e" imports []

section
variable [X86Registers.MemoryPrimitives]

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/Functions.lean.inc"
  sha256 "bd6908d0e3ffad6bd0a993563f522091c21033df318a1d33e7721c1953a79bb1"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]

end
