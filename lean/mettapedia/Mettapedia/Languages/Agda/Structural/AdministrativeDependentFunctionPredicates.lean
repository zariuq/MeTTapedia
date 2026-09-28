import Mettapedia.Languages.Agda.Structural.AdministrativeFunctionPredicates
import Mettapedia.GSLT.Topos.ConstructivePresheafDependentPredicates

/-!
# Dependent Agda application as an internal function predicate

Type parameters and binding/nonbinding codomain bodies carry their existing
generic substitution actions. Natural sections of these presheaves give
domain and codomain families. A result pair is accepted by its actual native
typing tree at the codomain instantiated with that pair's argument.

The dependent application rule proves the internal predicate after every
supported substitution. This neither replaces static typing by a behavioral
test nor constructs dependent product objects for arbitrary slice categories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

noncomputable def typeParameters : Base ⥤ Type where
  obj X := Statics.TypeParameter X.unop.val.val.1
  map substitution := TypeCat.ofHom (fun A => A.substitute substitution.unop.val)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro A
    exact Statics.TypeParameter.substitute_identity A
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro A
    exact (Statics.TypeParameter.substitute_comp A first.unop.val second.unop.val).symm

noncomputable def typeBodies : Base ⥤ Type where
  obj X := Statics.TypeBody X.unop.val.val.1
  map substitution := TypeCat.ofHom (fun B => B.substitute substitution.unop.val)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro B
    exact Statics.TypeBody.substitute_identity B
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro B
    exact (Statics.TypeBody.substitute_comp B first.unop.val second.unop.val).symm

abbrev ParameterSection := NatTrans one typeParameters
abbrev BodySection := NatTrans one typeBodies

noncomputable def parameterType (domain : ParameterSection) : TypeSection where
  app X := TypeCat.ofHom (fun _ => (domain.app X PUnit.unit).code)
  naturality X Y substitution := by
    apply ConcreteCategory.hom_ext
    intro value
    have naturally := congrArg (fun h : one.obj X ⟶ typeParameters.obj Y => h PUnit.unit)
      (domain.naturality substitution)
    exact congrArg Statics.TypeParameter.code naturally

noncomputable def dependentArrowSection (domain : ParameterSection) (codomain : BodySection) :
    TypeSection where
  app X := TypeCat.ofHom (fun _ =>
    (Statics.piType (domain.app X PUnit.unit) (codomain.app X PUnit.unit)).code)
  naturality X Y substitution := by
    apply ConcreteCategory.hom_ext
    intro value
    have domainNatural := congrArg (fun h : one.obj X ⟶ typeParameters.obj Y => h PUnit.unit)
      (domain.naturality substitution)
    have codomainNatural := congrArg (fun h : one.obj X ⟶ typeBodies.obj Y => h PUnit.unit)
      (codomain.naturality substitution)
    change domain.app Y PUnit.unit = (domain.app X PUnit.unit).substitute substitution.unop.val
      at domainNatural
    change codomain.app Y PUnit.unit = (codomain.app X PUnit.unit).substitute substitution.unop.val
      at codomainNatural
    exact (congrArg₂ (fun A B => (Statics.piType A B).code) domainNatural codomainNatural).trans
      (congrArg Statics.TypeParameter.code
        (Statics.substitute_piType substitution.unop.val
          (domain.app X PUnit.unit) (codomain.app X PUnit.unit)).symm)

noncomputable def dependentResults (codomain : BodySection) :
    Subfunctor (FunctorToTypes.prod (terms .term) (terms .term)) where
  obj X := {pair | Nonempty (CoreDerivation
    (Statics.typed X.unop.val.val.2 pair.2
      ((codomain.app X PUnit.unit).instantiate pair.1).code))}
  map {X Y} substitution := by
    rintro pair ⟨typing⟩
    obtain ⟨evidence⟩ := substitution.unop.property
    have image := CoreDerivation.substitution typing Y.unop.val.val.2
      substitution.unop.val evidence
    have naturally := congrArg (fun h : one.obj X ⟶ typeBodies.obj Y => h PUnit.unit)
      (codomain.naturality substitution)
    change codomain.app Y PUnit.unit = (codomain.app X PUnit.unit).substitute substitution.unop.val
      at naturally
    have typeNatural := (congrArg (fun B : Statics.TypeBody Y.unop.val.val.1 =>
      (B.instantiate (bind substitution.unop.val pair.1)).code) naturally).trans
        (congrArg Statics.TypeParameter.code
          (Statics.TypeBody.instantiate_substitute substitution.unop.val
            (codomain.app X PUnit.unit) pair.1))
    exact ⟨(congrArg (fun A => CoreDerivation
      (Statics.typed Y.unop.val.val.2 (bind substitution.unop.val pair.2) A)) typeNatural).mpr image⟩

theorem typed_dependent_application_preserves_predicates
    (domain : ParameterSection) (codomain : BodySection) :
    productPredicate (inhabitants (parameterType domain))
      (inhabitants (dependentArrowSection domain codomain)) ≤
        preimage (operationWithArgument application) (dependentResults codomain) := by
  intro X pair member
  obtain ⟨argument⟩ := member.1
  obtain ⟨function⟩ := member.2
  exact ⟨Derivation.core (.application X.unop.val.val.2
    (domain.app X PUnit.unit) (codomain.app X PUnit.unit) pair.2 pair.1)
    (consEvidence CoreDerivation function
      (consEvidence CoreDerivation argument (noEvidence CoreDerivation)))⟩

theorem typed_dependent_function_internal (domain : ParameterSection) (codomain : BodySection) :
    inhabitants (dependentArrowSection domain codomain) ≤
      preimage applicationFunction
        (dependentFunctionPredicate (inhabitants (parameterType domain)) (dependentResults codomain)) :=
  (curry_preserves_dependent_predicates_iff application _ _ _).2
    (typed_dependent_application_preserves_predicates domain codomain)

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf
