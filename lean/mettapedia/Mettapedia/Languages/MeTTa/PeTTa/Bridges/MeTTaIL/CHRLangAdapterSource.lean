import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRControllerSource

/-! The CHR package port is ordinary MeTTa over the refined controller. It
reads controller states to record the identifier given to each posted seed
and to expose terminal outcomes; it constructs no controller state. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRLangAdapterSource

open Mettapedia.GSLT.LanguageDef CettaWire
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_chr_lang.metta"
  sha256 "5ed07436126346b824a3ab1efb1df25bba9a430b01bc5028b6641a7d40ae6681"

def library : Library := ⟨CHRControllerSource.runtime, source.program, ["gslt:chr-lang:"]⟩
def runtime := library.runtime

theorem checked : library.check = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRLangAdapterSource
