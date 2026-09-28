import Mettapedia.GSLT.Topos.ConstructivePresheafDependentResultFamilies
import Mettapedia.Languages.Agda.Structural.AdministrativeLocalFunctionPredicates

/-!
# Native application into dependent result objects

At each local domain/codomain annotation, a natively typed function determines
an actual dependent section over supported arguments. The result carries its
raw term and native typing support at the argument-instantiated codomain.
No converse from arbitrary sections to Agda terms is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

noncomputable def nativeDependentResults : localArguments.toFunctor.Elements ⥤ Type :=
  resultFamily localArguments localResults

noncomputable def nativeDependentFunctions : FunctionBase ⥤ Type :=
  dependentFunctions localArguments.toFunctor nativeDependentResults

theorem localApplication_into_results (X : FunctionBase)
    (argument function : localTerms.obj X)
    (argumentTyped : argument ∈ localArguments.obj X)
    (functionTyped : function ∈ localFunctions.obj X) :
    (argument, localApplication.app X (argument,function)) ∈ localResults.obj X :=
  local_typed_application_preserves_predicates X ⟨argumentTyped,functionTyped⟩

noncomputable def nativeApplicationSections :
    NatTrans localFunctions.toFunctor nativeDependentFunctions :=
  supportedDependentFunction localApplication localArguments localFunctions localResults
    localApplication_into_results

theorem nativeApplicationSections_value {X Y : FunctionBase} (step : X ⟶ Y)
    (function : localFunctions.obj X) (argument : localArguments.obj Y) :
    ((nativeApplicationSections.app X function).app Y step argument).val =
      Statics.app ((terms .term).map step.val function.val) argument.val := rfl

theorem nativeApplicationSections_typed {X Y : FunctionBase} (step : X ⟶ Y)
    (function : localFunctions.obj X) (argument : localArguments.obj Y) :
    Nonempty (CoreDerivation (Statics.typed Y.1.unop.val.val.2
      ((nativeApplicationSections.app X function).app Y step argument).val
      (Y.2.2.instantiate argument.val).code)) :=
  ((nativeApplicationSections.app X function).app Y step argument).property

theorem nativeApplicationSections_reindex {X Y : FunctionBase} (step : X ⟶ Y)
    (function : localFunctions.obj X) :
    nativeApplicationSections.app Y (localFunctions.toFunctor.map step function) =
      DependentSection.restrict localArguments.toFunctor nativeDependentResults step
        (nativeApplicationSections.app X function) :=
  congrArg (fun h => h function) (nativeApplicationSections.naturality step)

theorem nativeApplicationSections_result_naturality
    {X Y Z : FunctionBase} (first : X ⟶ Y) (later : Y ⟶ Z)
    (function : localFunctions.obj X) (argument : localArguments.obj Y) :
    nativeDependentResults.map (argumentMap localArguments.toFunctor later argument)
      ((nativeApplicationSections.app X function).app Y first argument) =
    (nativeApplicationSections.app X function).app Z (first ≫ later)
      (localArguments.toFunctor.map later argument) :=
  (nativeApplicationSections.app X function).naturality later first argument

#print axioms nativeApplicationSections
#print axioms nativeApplicationSections_typed
#print axioms nativeApplicationSections_result_naturality

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf
