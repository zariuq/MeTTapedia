import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation

/-! The refined ground CHR machine over plain values, as loaded source. The
check concerns namespace ownership and conservative dispatch. Correspondence
with `Mettapedia.Languages.CHR.Operational` is a separate obligation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineSource

open Mettapedia.GSLT.LanguageDef CettaWire
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_chr_machine.metta"
  sha256 "c5a02c63beab22c6429b422d04145d9f68211dec01367577ec062477e2bfcca3"

def library : Library := ⟨CompleteEmission.runtime, source.program, ["gslt:chr-machine:"]⟩
def runtime := library.runtime

theorem checked : library.check = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineSource
