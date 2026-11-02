import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticAdequacy

/-! An independently evaluated source result and an actual loaded service
execution compose into preservation and reflection over encoded results.
The two premises remain separate proof obligations for each primitive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveReflection

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

def call (operator : OCaml.Primitive) (arguments : List OCaml.Value) : Atom :=
  apply "gslt:ml:primitive" [encoded (InferenceCettaWire.encodePattern (primitive operator)),
    encoded (InferenceCettaWire.encodePattern (valueList arguments))]

theorem result_iff (state : State) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (expected actual : OCaml.Result) (evaluated : operator.eval arguments = .ok expected)
    (computed : PureReturns runtime [] state (call operator arguments) state
      (encoded (OCamlArithmeticAdequacy.resultTerm expected))) :
    Runs runtime {state := state, control := .evaluate [] (call operator arguments)}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm actual)] [] []) ↔
      operator.eval arguments = .ok actual := by
  have exact := pure_returns_derivation_iff runtime [] state state _ _ computed state
    [encoded (OCamlArithmeticAdequacy.resultTerm actual)] [] []
  rw [evaluated]
  constructor
  · intro completed
    have answer := (exact.mp completed).2.1
    have wireSame := CettaWireAtom.encode_injective _ _ (List.cons.inj answer).1
    have patternSame := InferenceCettaWire.encodePattern_injective (List.cons.inj (Term.application.inj wireSame).2).1
    exact congrArg Except.ok (primitiveResult_injective patternSame).symm
  · intro same
    have resultSame := Except.ok.inj same
    subst actual
    exact exact.mpr ⟨rfl, rfl, rfl, rfl⟩

#print axioms result_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveReflection
