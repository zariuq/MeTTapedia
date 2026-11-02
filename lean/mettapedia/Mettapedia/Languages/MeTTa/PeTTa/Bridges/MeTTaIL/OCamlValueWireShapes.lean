import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlByteExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlResultServices

/-! Outer value shapes expose the existing codec without unfolding captured
environments or recursive fields during execution proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlValueWireShapes

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open OCamlCompareWire

theorem integer_exact (number : Int) : valueTerm (.literal (.integer number)) = OCamlIntegerWire.datum number :=
  (OCamlIntegerWire.datum_exact number).symm

theorem boolean_exact (flag : Bool) : valueTerm (.literal (.boolean flag)) = OCamlResultServices.booleanTerm flag := by
  cases flag <;> simp only [valueTerm, value, literal, node, OCamlResultServices.booleanTerm,
    InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]

theorem unit_exact : valueTerm (.literal .unit) = .application "PApp" [.string "MlUnit", .symbol "LNil"] := by
  simp only [valueTerm, value, literal, node, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]

theorem nil_exact : valueTerm (.literal .nil) = .application "PApp" [.string "MlNil", .symbol "LNil"] := by
  simp only [valueTerm, value, literal, node, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]

theorem string_exact (bytes : List UInt8) : valueTerm (.literal (.string bytes)) =
    .application "PApp" [.string "MlString", encodeList id [.application "PCollection"
      [.string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec", encodeList OCamlByteExecution.byteTerm bytes, .symbol "RNone"]]] := by
  simp only [valueTerm, value, literal, node, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq,
    InferenceCettaWire.encodeCollectionType, InferenceCettaWire.encodeRest]
  have same : encodeList InferenceCettaWire.encodePattern (bytes.map byteCode) = encodeList OCamlByteExecution.byteTerm bytes := by
    rw [encodeList_map]
    congr 1
    funext byte
    exact (OCamlByteExecution.byte_exact byte).symm
  convert congrArg (fun terms => Term.application "PApp" [Term.string "MlString",
    Term.application "LCons" [Term.application "PCollection" [Term.string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec", terms,
      Term.symbol "RNone"], Term.symbol "LNil"]]) same using 1
  rfl

theorem closure_exact (function : OCaml.FunctionRef) (captured : List OCaml.Value) :
    ∃ fields : Term, valueTerm (.closure function captured) = .application "PApp" [.string "MlClosure", fields] := by
  cases function <;> simp only [valueTerm, value, node, InferenceCettaWire.encodePattern]
  all_goals exact ⟨_, rfl⟩

theorem outer_shape (actual : OCaml.Value) :
    ∃ name fields, valueTerm actual = .application "PApp" [.string name, fields] := by
  cases actual with
  | literal datum =>
    cases datum with
    | integer n => rw [integer_exact]; exact ⟨"MlInteger", _, rfl⟩
    | boolean flag => rw [boolean_exact]; exact ⟨_, _, rfl⟩
    | unit => exact ⟨_, _, unit_exact⟩
    | nil => exact ⟨_, _, nil_exact⟩
    | string bytes => exact ⟨_, _, string_exact bytes⟩
  | tuple fields => rw [value_tuple]; exact ⟨_, _, rfl⟩
  | cons head tail => rw [value_cons]; exact ⟨_, _, rfl⟩
  | variant typeId constructor fields => rw [value_variant]; exact ⟨_, _, rfl⟩
  | closure function captured => obtain ⟨fields, same⟩ := closure_exact function captured; exact ⟨_, fields, same⟩

#print axioms string_exact
#print axioms closure_exact
#print axioms outer_shape

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlValueWireShapes
