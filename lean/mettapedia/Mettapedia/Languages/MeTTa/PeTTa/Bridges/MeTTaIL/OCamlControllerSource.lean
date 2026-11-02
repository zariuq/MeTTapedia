import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWordLibrarySource

/-! Actual OCaml service source loaded over the common provider runtime.
Namespace checks establish conservative library extension; semantic service
and whole-controller claims require their execution theorems separately.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def integerSource : ProgramQuotation.QuotedProgram := IntegerWordLibrarySource.integerSource

def wordSource : ProgramQuotation.QuotedProgram := IntegerWordLibrarySource.wordSource

def source : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_ocaml.metta"
  sha256 "42cf7e581374db1bb6a4a2b99fe60bcd1f81b7264a1615e3b62ca186f496e967"

def integerLibrary : Library := ⟨ProviderCacheExecution.runtime, integerSource.program, ["gslt:integer:"]⟩
def wordLibrary : Library := ⟨integerLibrary.runtime, wordSource.program, ["gslt:word16:"]⟩
def library : Library := ⟨wordLibrary.runtime, source.program, ["gslt:ml:"]⟩
def runtime := library.runtime

theorem integer_checked : integerLibrary.check = true := by decide +kernel
theorem word_checked : wordLibrary.check = true := by decide +kernel
theorem checked : library.check = true := by decide +kernel

theorem pack1_returns (state : State) (name : String) (item : Term) :
    PureReturns runtime [] state (apply "gslt:ml:pack1" [encoded (.string name), encoded item]) state
      (encoded (.application "PApp" [.string name, encodeList id [item]])) := by
  metta_call checked
  metta_eval with checked unfolding [encodeList]

theorem pack2_returns (state : State) (name : String) (first second : Term) :
    PureReturns runtime [] state (apply "gslt:ml:pack2" [encoded (.string name), encoded first, encoded second]) state
      (encoded (.application "PApp" [.string name, encodeList id [first, second]])) := by
  metta_call checked
  metta_eval with checked unfolding [encodeList]

#print axioms checked
#print axioms pack1_returns
#print axioms pack2_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource
