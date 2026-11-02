import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ProviderCacheExecution

/-! Shared exact-integer and radix-16 library sources, independently of a
consumer language. The namespace checks establish conservative loading;
individual operations retain their separate execution proofs.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWordLibrarySource

open Eval BridgeKit
open scoped ProgramQuotation

def integerSource : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_integer.metta"
  sha256 "b394457d6b4dff17d1aa95528b19e9e8b4ca03d72a6762db120b1fb2618326a0"

def wordSource : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_word16.metta"
  sha256 "0e5628438375df0c2d156a6a82a81dce9e2ed00eb1a077e84286c47952173ade"

def integerLibrary : Library := ⟨ProviderCacheExecution.runtime, integerSource.program, ["gslt:integer:"]⟩
def wordLibrary : Library := ⟨integerLibrary.runtime, wordSource.program, ["gslt:word16:"]⟩
def runtime := wordLibrary.runtime

theorem integer_checked : integerLibrary.check = true := by decide +kernel
theorem word_checked : wordLibrary.check = true := by decide +kernel

#print axioms integer_checked
#print axioms word_checked

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWordLibrarySource
