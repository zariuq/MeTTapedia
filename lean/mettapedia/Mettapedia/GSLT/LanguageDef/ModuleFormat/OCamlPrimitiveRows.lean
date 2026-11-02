import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveReturn
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlValueReading
import Mettapedia.OSLF.MeTTaIL.ProviderAppend

/-! Primitive cache rows retain source evaluation evidence independently
of their provider typing. Reuse of a row cannot authorize another result.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def primitiveRow (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result) : GeneralPremise.ProviderRow :=
  ⟨"ml-primitive", [primitive operator, valueList arguments, primitiveResult result]⟩

def PrimitiveRowsSound (snapshot : GeneralPremise.ProviderSnapshot) : Prop :=
  ∀ operator arguments result, primitiveRow operator arguments result ∈ snapshot.rows →
    operator.eval arguments = .ok result

theorem primitive_injective : Function.Injective primitive := by
  intro first second same
  cases first <;> cases second <;> simp_all [primitive, node]

theorem primitiveResult_injective : Function.Injective primitiveResult := by
  intro first second same
  cases first with
  | ok first =>
    cases second with
    | ok second => exact congrArg Except.ok (value_injective (List.cons.inj (Pattern.apply.inj same).2).1)
    | error second => simp [primitiveResult, node] at same
  | error first =>
    cases second with
    | ok second => simp [primitiveResult, node] at same
    | error second =>
      cases first <;> cases second <;> simp_all [primitiveResult, fault, node]

theorem primitiveRow_injective {first second : OCaml.Primitive} {left right : List OCaml.Value}
    {one two : OCaml.Result} (same : primitiveRow first left one = primitiveRow second right two) :
    first = second ∧ left = right ∧ one = two := by
  have fields := List.cons.inj (congrArg GeneralPremise.ProviderRow.values same)
  have rest := List.cons.inj fields.2
  refine ⟨primitive_injective fields.1, ?_, primitiveResult_injective (List.cons.inj rest.2).1⟩
  have linkedSame : values (left.map value) = values (right.map value) := by simpa only [valueList_as_values] using rest.1
  exact List.map_injective_iff.mpr value_injective (values_injective linkedSame)

theorem initial_primitive_rows_sound : PrimitiveRowsSound provider := by
  intro operator arguments result member
  cases member

theorem append_primitive_sound (table : GeneralPremise.ProviderSnapshot) (operator : OCaml.Primitive)
    (arguments : List OCaml.Value) (result : OCaml.Result) (sound : PrimitiveRowsSound table)
    (evaluated : operator.eval arguments = .ok result) :
    PrimitiveRowsSound (GeneralPremise.ProviderAppend.appendRows table [primitiveRow operator arguments result]) := by
  intro other actuals answer present
  rcases (GeneralPremise.ProviderAppend.row_membership table [primitiveRow operator arguments result]
    (primitiveRow other actuals answer)).mp present with old | fresh
  · exact sound other actuals answer old
  · have same := List.mem_singleton.mp fresh
    obtain ⟨rfl, rfl, rfl⟩ := primitiveRow_injective same
    exact evaluated

theorem cached_primitive_authorized (table : GeneralPremise.ProviderSnapshot) (program : OCaml.Program)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result) (rest : OCaml.Continuation)
    (sound : PrimitiveRowsSound table) (present : primitiveRow operator arguments result ∈ table.rows) :
    OCaml.finishBuild program (.primitive operator) arguments rest = .ok (finishPrimitive result rest) :=
  finish_primitive_source program operator arguments result rest (sound operator arguments result present)

#print axioms primitiveRow_injective
#print axioms append_primitive_sound
#print axioms cached_primitive_authorized

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
