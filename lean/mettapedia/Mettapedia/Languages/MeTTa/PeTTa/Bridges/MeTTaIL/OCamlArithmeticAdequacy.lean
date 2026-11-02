import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticPrimitive
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveRows

/-! Exact completed public arithmetic observations preserve and reflect
the independent source result, including its source result encoding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticAdequacy

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlIntegerArithmetic

def call (operator : Operator) (left right : Int) : Atom :=
  apply "gslt:ml:primitive"
    [encoded (InferenceCettaWire.encodePattern (primitive (OCamlArithmeticSource.source operator))),
     encoded (InferenceCettaWire.encodePattern (valueList [.literal (.integer left), .literal (.integer right)]))]

def resultTerm (result : OCaml.Result) : Term :=
  .application "Some" [InferenceCettaWire.encodePattern (primitiveResult result)]

theorem exact_source_result (state : State) (operator : Operator) (left right : Int) (result : OCaml.Result) :
    Runs runtime {state := state, control := .evaluate [] (call operator left right)}
      (.complete state [encoded (resultTerm result)] [] []) ↔
      (OCamlArithmeticSource.source operator).eval [.literal (.integer left), .literal (.integer right)] = .ok result := by
  have execution := OCamlArithmeticPrimitive.primitive_returns state operator left right
  have exact := pure_returns_derivation_iff runtime [] state state _ _ execution state [encoded (resultTerm result)] [] []
  rw [OCamlIntegerResult.result_exact] at exact
  have source := OCamlArithmeticSource.source_evaluates operator left right
  rw [source]
  constructor
  · intro completed
    have answer := (exact.mp completed).2.1
    have wireSame := CettaWireAtom.encode_injective _ _ (List.cons.inj answer).1
    have patternSame := InferenceCettaWire.encodePattern_injective (List.cons.inj (Term.application.inj wireSame).2).1
    have resultSame := primitiveResult_injective patternSame
    exact congrArg Except.ok resultSame.symm
  · intro same
    have resultSame := Except.ok.inj same
    subst result
    exact exact.mpr ⟨rfl, rfl, rfl, rfl⟩

#print axioms exact_source_result

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticAdequacy
