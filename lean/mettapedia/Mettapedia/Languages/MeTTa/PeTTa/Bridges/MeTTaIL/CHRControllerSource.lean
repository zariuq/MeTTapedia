import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation

/-! Literal CHR controller sources over the shared runtime. The check theorems
below concern namespace ownership and conservative dispatch. Local execution
laws concern actual loaded source; whole-controller adequacy is separate. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRControllerSource

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def integerSource : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_integer.metta"
  sha256 "b394457d6b4dff17d1aa95528b19e9e8b4ca03d72a6762db120b1fb2618326a0"

def source : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_chr.metta"
  sha256 "dcd322f7ef4560a1ca15f58c934a2bf1f7c96553532900b484f7e81cea30509e"

def integerLibrary : Library := ⟨CompleteEmission.runtime, integerSource.program, ["gslt:integer:"]⟩
def library : Library := ⟨integerLibrary.runtime, source.program, ["gslt:chr:"]⟩
def runtime := library.runtime

theorem integer_checked : integerLibrary.check = true := by decide +kernel
theorem checked : library.check = true := by decide +kernel

def environmentTerm (bindings : List (String × Term)) : Term :=
  encodeList (fun (name, value) => .application "Binding" [.string name, value]) bindings

def lookup (name : String) : List (String × Term) → Option Term
  | [] => none
  | (other, value) :: rest => if name == other then some value else lookup name rest

theorem lookup_returns (state : State) (name : String) (bindings : List (String × Term)) :
    PureReturns runtime [] state
      (apply "gslt:chr:lookup" [encoded (.string name), encoded (environmentTerm bindings)]) state
      (encoded (encodeOption id (lookup name bindings))) := by
  induction bindings with
  | nil =>
      metta_call checked
      metta_eval with checked unfolding [environmentTerm, lookup, encodeOption]
  | cons binding rest ih =>
      rcases binding with ⟨other, value⟩
      by_cases same : name = other
      · subst other
        metta_call checked
        metta_eval with checked unfolding [environmentTerm, lookup, encodeOption]
      · have unequal : (name == other) = false := beq_eq_false_iff_ne.mpr same
        simp only [lookup, unequal, Bool.false_eq_true, if_false]
        metta_call checked
        metta_eval [ih] with checked unfolding [environmentTerm, lookup, encodeOption, same]

#print axioms lookup_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRControllerSource
