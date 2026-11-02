import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerEncode
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerDecode

/-! Public integer construction and readback have exact completed
observations under the loaded OCaml runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerObservation

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

theorem encode_exact (state : State) (number : Int) (after : State) (answers input output : List Atom) :
    Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:integer" [integer number])}
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (OCamlIntegerWire.datum number)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff runtime [] state state _ _
    (OCamlIntegerEncode.integer_returns state number) after answers input output

theorem decode_exact (state : State) (number : Int) (after : State) (answers input output : List Atom) :
    Runs runtime {state := state, control := (.evaluate []
      (apply "gslt:ml:integer-value" [encoded (OCamlIntegerWire.datum number)]))}
      (.complete after answers input output) ↔
      after = state ∧ answers = [.expression [.symbol "Some", integer number]] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff runtime [] state state _ _
    (OCamlIntegerDecode.value_returns state number) after answers input output

#print axioms encode_exact
#print axioms decode_exact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerObservation
