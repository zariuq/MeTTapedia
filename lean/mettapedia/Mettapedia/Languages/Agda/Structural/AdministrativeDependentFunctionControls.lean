import Mettapedia.Languages.Agda.Structural.AdministrativeDependentFunctionPredicates
import Mettapedia.Languages.Agda.Structural.AdministrativePresheafControls

/-!
# A universe-indexed result predicate

The formed context assumes a function of type `(X : Set 1) → X`. It is not
asserted to have a closed inhabitant. Applying its context variable to two
different type-denoting terms produces the corresponding different raw
result annotations, with actual native typing evidence in both cases.

The dependent body uses the new bound variable. A NoAbs body instead retains
its ambient type independently of the argument.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.DependentControls

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

noncomputable def universeDomain : ParameterSection where
  app X := TypeCat.ofHom (fun _ => Statics.universeType X.unop.val.val.1 1)
  naturality _ _ _ := rfl

noncomputable def boundCodomain : BodySection where
  app _ := TypeCat.ofHom (fun _ => .bind ⟨1, .var .zero⟩)
  naturality _ _ _ := rfl

abbrev empty := AdministrativeStatics.Controls.empty
abbrev domain := AdministrativeStatics.Controls.domain
abbrev domainContext := AdministrativeStatics.Controls.extended
def functionType : Statics.TypeParameter 0 :=
  Statics.piType domain (.bind ⟨1, .var .zero⟩)
def functionContext : Statics.RawContext 1 := empty.snoc functionType.code

noncomputable def functionFormation : CoreDerivation (Statics.formed empty functionType.code) :=
  administrativeOperations.piFormed (A := domain) (B := .bind ⟨1, .var .zero⟩)
    AdministrativeStatics.Controls.domainFormed
    (Derivation.core (.formation domainContext 1 (.var .zero))
      (consEvidence CoreDerivation AdministrativeStatics.Controls.newestTyped (noEvidence CoreDerivation)))

noncomputable def functionContextFormation : CoreDerivation (Statics.context functionContext) :=
  administrativeOperations.extend (includeCanonical Statics.Derivation.empty) functionFormation

noncomputable def functionWorld : Base :=
  Opposite.op ⟨⟨⟨1, functionContext⟩, ⟨functionContextFormation⟩⟩⟩

noncomputable def functionVariableTyping : CoreDerivation
    (Statics.typed functionContext (.var .zero)
      ((dependentArrowSection universeDomain boundCodomain).app functionWorld PUnit.unit)) :=
  Derivation.core (.variable functionContext .zero)
    (consEvidence CoreDerivation functionContextFormation (noEvidence CoreDerivation))

theorem function_variable_internal :
    applicationFunction.app functionWorld (.var .zero) ∈
      (dependentFunctionPredicate (inhabitants (parameterType universeDomain))
        (dependentResults boundCodomain)).obj functionWorld :=
  typed_dependent_function_internal universeDomain boundCodomain functionWorld
    ⟨functionVariableTyping⟩

def firstArgument : Statics.RawTm 1 := Statics.universeTerm 0
def secondArgument : Statics.RawTm 1 := eliminate firstArgument nil

noncomputable def firstArgumentTyping : CoreDerivation
    (Statics.typed functionContext firstArgument (Statics.universeType 1 1).code) :=
  Derivation.core (.sort functionContext 0)
    (consEvidence CoreDerivation functionContextFormation (noEvidence CoreDerivation))

noncomputable def secondArgumentTyping : CoreDerivation
    (Statics.typed functionContext secondArgument (Statics.universeType 1 1).code) :=
  Derivation.elimination firstArgumentTyping (Derivation.nil functionContext _)

theorem first_result_typed :
    (firstArgument, Statics.app (n := 1) (.var .zero) firstArgument) ∈
      (dependentResults boundCodomain).obj functionWorld :=
  function_variable_internal functionWorld (𝟙 functionWorld) firstArgument ⟨firstArgumentTyping⟩

theorem second_result_typed :
    (secondArgument, Statics.app (n := 1) (.var .zero) secondArgument) ∈
      (dependentResults boundCodomain).obj functionWorld :=
  function_variable_internal functionWorld (𝟙 functionWorld) secondArgument ⟨secondArgumentTyping⟩

theorem first_result_annotation :
    ((boundCodomain.app functionWorld PUnit.unit).instantiate firstArgument).code =
      el (set (levelClosed 1)) firstArgument := rfl

theorem second_result_annotation :
    ((boundCodomain.app functionWorld PUnit.unit).instantiate secondArgument).code =
      el (set (levelClosed 1)) secondArgument := rfl

theorem dependent_result_annotations_differ :
    ((boundCodomain.app functionWorld PUnit.unit).instantiate firstArgument).code ≠
      ((boundCodomain.app functionWorld PUnit.unit).instantiate secondArgument).code := by
  intro same
  cases same

theorem nonbinding_result_does_not_vary :
    (Statics.TypeBody.noBind (Statics.universeType 1 0)).instantiate firstArgument =
      (Statics.TypeBody.noBind (Statics.universeType 1 0)).instantiate secondArgument :=
  (Statics.TypeBody.instantiate_noBind _ firstArgument).trans
    (Statics.TypeBody.instantiate_noBind _ secondArgument).symm

theorem forgetting_argument_dependency_changes_annotation :
    ((boundCodomain.app functionWorld PUnit.unit).instantiate secondArgument).code ≠
      ((boundCodomain.app functionWorld PUnit.unit).instantiate firstArgument).code :=
  Ne.symm dependent_result_annotations_differ

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.DependentControls
