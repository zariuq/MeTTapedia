import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWordLibrarySource

/-! Actual sequential, mailbox-adapter, actor and portable-dispatch source
libraries loaded in declaration order. Loading checks namespace extension;
actor operations and native-rho services need their own execution proofs.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangControllerSource

open Eval BridgeKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_erlang.metta"
  sha256 "6975ab1774bb205f3fbbb724a82ff4c539269a2c40eb4fecea45ddec5ee61088"

def rhoSource : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_erlang_rho.metta"
  sha256 "623d5fcbd404d8ad592e354c1f1453340373e6b73e627de0d10ae58b9ff5389e"

def actorSource : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_erlang_actors.metta"
  sha256 "259e3a8c0f7d0f4fa25b076573496c68b00fbc4f939fd6bb500f2cf6ec8090e3"

def portableSource : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_erlang_actors_portable.metta"
  sha256 "5798d4ec80b40f207a6a22447e279152e260a4ceb6585b7142944ef0977a79fa"

def library : Library := ⟨IntegerWordLibrarySource.runtime, source.program, ["gslt:er:"]⟩
def rhoLibrary : Library := ⟨library.runtime, rhoSource.program, ["gslt:er-rho:"]⟩
def actorLibrary : Library := ⟨rhoLibrary.runtime, actorSource.program, ["gslt:er-actor:"]⟩
def portableLibrary : Library := ⟨actorLibrary.runtime, portableSource.program,
  ["gslt:er-actor:choices-portable", "gslt:er-actor:continue-portable"]⟩
def runtime := actorLibrary.runtime
def portableRuntime := portableLibrary.runtime

theorem checked : library.check = true := by decide +kernel
theorem rho_checked : rhoLibrary.check = true := by decide +kernel
theorem actor_checked : actorLibrary.check = true := by decide +kernel
theorem portable_checked : portableLibrary.check = true := by decide +kernel

#print axioms checked
#print axioms rho_checked
#print axioms actor_checked
#print axioms portable_checked

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangControllerSource
