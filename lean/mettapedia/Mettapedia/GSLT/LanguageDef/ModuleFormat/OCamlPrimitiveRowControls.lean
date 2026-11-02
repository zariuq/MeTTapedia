import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveRowTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderMeaning

/-! A well-typed provider row can still assert a wrong answer. Source
meaning rejects it, while valid value and fault rows retain their evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

private def inputs : List OCaml.Value := [.literal (.integer 2), .literal (.integer 3)]
private def five : OCaml.Result := .ok (.literal (.integer 5))
private def six : OCaml.Result := .ok (.literal (.integer 6))

theorem correct_answer_sound : PrimitiveRowsSound
    (GeneralPremise.ProviderAppend.appendRows provider [primitiveRow .add inputs five]) :=
  append_primitive_sound provider .add inputs five initial_primitive_rows_sound (by rfl)

theorem wrong_answer_typed :
    GeneralPremise.checkRow baseLanguage (fun _ => none) []
      ⟨"ml-primitive", [.base "MlPrimitive", .base "MlValues", .base "MlPrimitiveResult"], [.input, .input, .output]⟩
      (primitiveRow .add inputs six) = true := primitive_row_checked baseLanguage rfl (fun _ => none) .add inputs six

theorem wrong_answer_unsound : ¬ PrimitiveRowsSound
    (GeneralPremise.ProviderAppend.appendRows provider [primitiveRow .add inputs six]) := by
  intro sound
  have evaluated := sound .add inputs six
    ((GeneralPremise.ProviderAppend.row_membership provider [primitiveRow .add inputs six]
      (primitiveRow .add inputs six)).mpr (Or.inr (List.mem_singleton_self _)))
  have wrong : OCaml.Primitive.eval .add inputs ≠ .ok six := by simp [OCaml.Primitive.eval, inputs, six, OCaml.wrapInteger, OCaml.integerHalf, OCaml.integerModulus]
  exact wrong evaluated

theorem division_fault_sound : PrimitiveRowsSound
    (GeneralPremise.ProviderAppend.appendRows provider
      [primitiveRow .divide [.literal (.integer 7), .literal (.integer 0)] (.error .divisionByZero)]) :=
  append_primitive_sound provider .divide _ _ initial_primitive_rows_sound (by rfl)

#print axioms correct_answer_sound
#print axioms wrong_answer_typed
#print axioms wrong_answer_unsound
#print axioms division_fault_sound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
