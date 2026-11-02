import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16NibbleExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16WordStep

/-! The shared word helper uses the compiler's canonical little-endian
digits and its exact vector wrapper.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16Wire

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax

def digitsTerm (number : Nat) : Term := encodeList Word16NibbleExecution.nibble (Nat.digits 16 number)
def vectorTerm (number : Nat) : Term := .application "PCollection"
  [.string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec", digitsTerm number, .symbol "RNone"]

theorem vector_exact (number : Nat) : vectorTerm number = InferenceCettaWire.encodePattern
    (ModuleFormat.Radix16Word.encode number) := by
  simp only [vectorTerm, digitsTerm, ModuleFormat.Radix16Word.encode, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map, Function.comp_def]
  rfl

theorem zero_digits : digitsTerm 0 = .symbol "LNil" := by
  simp only [digitsTerm, Nat.digits_zero, encodeList]

theorem step_digits (number : Nat) (positive : 0 < number) :
    digitsTerm number = .application "LCons" [Word16NibbleExecution.nibble (number % 16), digitsTerm (number / 16)] := by
  simp only [digitsTerm, ModuleFormat.Radix16Word.digits_step number positive, encodeList]

#print axioms vector_exact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16Wire
