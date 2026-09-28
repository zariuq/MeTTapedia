import Mettapedia.Languages.Agda.Structural.AdministrativeDependentFunctionPredicates
import Mettapedia.GSLT.Topos.ConstructivePresheafFamilies

/-!
# Dependent application over local Agda annotations

The base for functions is the category of elements of domain/codomain
parameters. A world carries its actual parameters, including free variables;
an arrow substitutes both parameters along an admitted context substitution.
No extension of those parameters to global natural sections is required.

Typing implies the internal, future-arrow application predicate over this
base. This remains an implication about raw syntax and native typing support,
not an identification of conversion classes or a converse typing criterion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

/-- Native inhabitants at any local annotated type over a formed context. -/
noncomputable def inhabitantsByType : (terms .type).Elements ⥤ Type :=
  supportedFamily typed

theorem inhabitantsByType_formed (X : (terms .type).Elements)
    (inhabitant : inhabitantsByType.obj X) : X.2 ∈ formed.obj X.1 := by
  obtain ⟨typing⟩ := inhabitant.property
  exact ⟨CoreDerivation.typingFormation typing⟩

noncomputable def functionParameters : Base ⥤ Type :=
  FunctorToTypes.prod typeParameters typeBodies

abbrev FunctionBase := functionParameters.Elements

noncomputable def localTerms : FunctionBase ⥤ Type :=
  overElements functionParameters (terms .term)

noncomputable def domainProposal : NatTrans
    (FunctorToTypes.prod functionParameters (terms .term)) proposals where
  app _ := TypeCat.ofHom (fun pair => (pair.1.1.code, pair.2))
  naturality _ _ _ := rfl

noncomputable def functionProposal : NatTrans
    (FunctorToTypes.prod functionParameters (terms .term)) proposals where
  app _ := TypeCat.ofHom (fun pair => ((Statics.piType pair.1.1 pair.1.2).code, pair.2))
  naturality X Y substitution := by
    apply ConcreteCategory.hom_ext
    intro pair
    apply Prod.ext
    · exact congrArg Statics.TypeParameter.code
        (Statics.substitute_piType substitution.unop.val pair.1.1 pair.1.2).symm
    · rfl

noncomputable def localArguments : Subfunctor localTerms :=
  familyPredicate (preimage domainProposal typed)

noncomputable def localFunctions : Subfunctor localTerms :=
  familyPredicate (preimage functionProposal typed)

/-- The result keeps both its parameter and the argument used to instantiate it. -/
noncomputable def parameterizedResults :
    Subfunctor (FunctorToTypes.prod functionParameters
      (FunctorToTypes.prod (terms .term) (terms .term))) where
  obj X := {pair | Nonempty (CoreDerivation (Statics.typed X.unop.val.val.2 pair.2.2
    (pair.1.2.instantiate pair.2.1).code))}
  map {X Y} substitution := by
    rintro pair ⟨typing⟩
    obtain ⟨evidence⟩ := substitution.unop.property
    have image := CoreDerivation.substitution typing Y.unop.val.val.2
      substitution.unop.val evidence
    have naturalType := congrArg Statics.TypeParameter.code
      (Statics.TypeBody.instantiate_substitute substitution.unop.val pair.1.2 pair.2.1)
    exact ⟨(congrArg (fun A => CoreDerivation
      (Statics.typed Y.unop.val.val.2 (bind substitution.unop.val pair.2.2) A)) naturalType).mpr image⟩

noncomputable def localResults :
    Subfunctor (FunctorToTypes.prod localTerms localTerms) :=
  familyPredicate parameterizedResults

noncomputable def localApplication : NatTrans
    (FunctorToTypes.prod localTerms localTerms) localTerms where
  app _ := TypeCat.ofHom (fun pair => Statics.app pair.2 pair.1)
  naturality _ _ _ := rfl

noncomputable def localApplicationFunction :
    NatTrans localTerms (functions localTerms localTerms) :=
  curryFunction localApplication

theorem local_typed_application_preserves_predicates :
    productPredicate localArguments localFunctions ≤
      preimage (operationWithArgument localApplication) localResults := by
  intro X pair member
  obtain ⟨argument⟩ := member.1
  obtain ⟨function⟩ := member.2
  exact ⟨Derivation.core (.application X.1.unop.val.val.2 X.2.1 X.2.2 pair.2 pair.1)
    (consEvidence CoreDerivation function
      (consEvidence CoreDerivation argument (noEvidence CoreDerivation)))⟩

/-- Every local Pi typing supplies a future-arrow internal function predicate. -/
theorem local_typed_function_internal :
    localFunctions ≤ preimage localApplicationFunction
      (dependentFunctionPredicate localArguments localResults) :=
  (curry_preserves_dependent_predicates_iff localApplication _ _ _).2
    local_typed_application_preserves_predicates

theorem localApplicationFunction_apply (X Y : FunctionBase) (substitution : X ⟶ Y)
    (function : localTerms.obj X) (argument : localTerms.obj Y) :
    (localApplicationFunction.app X function).app Y substitution argument =
      Statics.app ((terms .term).map substitution.val function) argument := rfl

/-- Apply the internal predicate along any parameter-respecting substitution. -/
theorem local_typed_function_application {X Y : FunctionBase} (substitution : X ⟶ Y)
    (function : localTerms.obj X) (argument : localTerms.obj Y)
    (functionTyped : Nonempty (CoreDerivation
      (Statics.typed X.1.unop.val.val.2 function (Statics.piType X.2.1 X.2.2).code)))
    (argumentTyped : Nonempty (CoreDerivation
      (Statics.typed Y.1.unop.val.val.2 argument Y.2.1.code))) :
    Nonempty (CoreDerivation (Statics.typed Y.1.unop.val.val.2
      (Statics.app ((terms .term).map substitution.val function) argument)
      (Y.2.2.instantiate argument).code)) :=
  local_typed_function_internal X functionTyped Y substitution argument argumentTyped

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf
