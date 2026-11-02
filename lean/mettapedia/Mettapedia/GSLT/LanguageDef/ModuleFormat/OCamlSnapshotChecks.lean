import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedValidation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedLanguage

/-! The fixed O0 profile has an empty ambient context, a well-formed
initial provider, no reflective declarations and no set decomposition.
These are actual snapshot checks, independent of generated-rule admission.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

theorem initial_free_context_checked (prepared : Prepared) : checkFreeContext (snapshot prepared) = true := by
  simp [checkFreeContext, snapshot]

theorem initial_provider_checked (prepared : Prepared) :
    GeneralPremise.checkProviderClosed prepared.compiled (snapshot prepared).free provider = true := by
  simp only [GeneralPremise.checkProviderClosed, provider, List.all_cons, List.all_nil, Bool.and_true]
  decide +kernel

theorem initial_reflection_checked (prepared : Prepared) :
    Reflection.validate prepared.compiled permissions.reflection = [] := by
  simp [permissions, Reflection.validate, Reflection.ReflectionProfile.empty]

theorem prepared_set_free (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) : prepared.compiled.usesCollection .hashSet = false := by
  have terms := (prepare_readback program prepared built).2.2.1
  unfold LanguageDef.usesCollection
  rw [terms]
  decide +kernel

theorem prepared_set_decomposition (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) : setDecompositionFree (snapshot prepared) permissions = true := by
  simp only [setDecompositionFree, snapshot, prepared_set_free program prepared built, Bool.not_false, Bool.true_or]

theorem prepared_no_equations (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) : selectedEquations (snapshot prepared) permissions = [] := by
  have empty : baseLanguage.equations = [] := by rfl
  simp only [selectedEquations, snapshot, prepared_equations program prepared built, empty,
    List.zipIdx_nil, List.filter_nil, List.flatMap_nil]

#print axioms initial_free_context_checked
#print axioms initial_provider_checked
#print axioms initial_reflection_checked
#print axioms prepared_set_free
#print axioms prepared_set_decomposition
#print axioms prepared_no_equations

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
