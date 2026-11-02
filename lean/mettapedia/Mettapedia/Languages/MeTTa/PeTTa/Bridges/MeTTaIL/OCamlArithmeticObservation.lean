import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerArithmetic

/-! Completed arithmetic helper runs have one exact answer and preserve
the store and I/O. Source correspondence is supplied separately by the
operator mapping and exact result codec.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticObservation

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlIntegerArithmetic

theorem exact_observation (state : State) (operator : Operator) (left right : Int)
    (after : State) (answers input output : List Atom) :
    Runs runtime {state := state, control := (.evaluate []
      (apply "gslt:ml:integer-binary" [encoded (.string (name operator)),
        encoded (OCamlIntegerWire.datum left), encoded (OCamlIntegerWire.datum right)]))}
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (OCamlIntegerResult.result (compute operator left right))] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff runtime [] state state _ _
    (binary_returns state operator left right) after answers input output

#print axioms exact_observation

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticObservation
