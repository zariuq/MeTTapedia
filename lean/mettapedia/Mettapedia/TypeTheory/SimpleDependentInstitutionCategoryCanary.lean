import Mettapedia.Logic.InstitutionCategory
import Mettapedia.TypeTheory.SimpleDependentInstitutionBridge

/-!
# Heterogeneous-atlas canary for the simple-to-dependent route

The constant-family institution comorphism is an actual arrow between two
objects whose native signature categories differ.  It cannot be inverted:
a two-sided inverse would put every dependent family in the constant-family
image, contradicting the checked varying-Boolean-family discriminator.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SimpleDependentInstitutionCategoryCanary

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.Logic
open Mettapedia.TypeTheory.SimpleDependentInstitutionBridge
open Mettapedia.TypeTheory.SetFamilyChangeOfBaseAdjunction

universe u

/-- The contextual simple predicate institution as one heterogeneous atlas
object. -/
def simpleObject (Index : Type u) : InstitutionCategory.Object where
  Signature := CategoryTheory.Cat.of (Type u)
  logic := simpleInstitution Index

/-- The indexed-family predicate institution as a different atlas object. -/
def dependentObject (Index : Type u) : InstitutionCategory.Object where
  Signature := CategoryTheory.Cat.of (FamilyOver Index)
  logic := dependentInstitution Index

/-- Constant-family inclusion is a genuine heterogeneous institution arrow. -/
def simpleDependentRoute (Index : Type u) :
    simpleObject Index ⟶ dependentObject Index :=
  simpleToDependent Index

@[simp]
theorem simpleDependentRoute_mapSignature (Index : Type u) :
    (simpleDependentRoute Index).mapSignature = constantFamilyOver Index :=
  rfl

/-- Negative control: at two context points the heterogeneous route has no
strict retraction onto the whole dependent institution.  Such a retraction
would represent the varying Boolean family as a constant family. -/
theorem simpleDependentRoute_no_retraction :
    ¬ ∃ backward : dependentObject Bool ⟶ simpleObject Bool,
      CategoryTheory.CategoryStruct.comp backward (simpleDependentRoute Bool) =
        CategoryTheory.CategoryStruct.id (dependentObject Bool) := by
  rintro ⟨backward, rightInverse⟩
  have signatureInverse := congrArg
    Institution.Comorphism.mapSignature rightInverse
  have atVarying := congrArg
    (fun functor : CategoryTheory.Functor (FamilyOver Bool) (FamilyOver Bool) =>
      functor.obj boolVaryingFamily)
    signatureInverse
  have constantEquality :
      (constantFamilyOver Bool).obj
          (backward.mapSignature.obj boolVaryingFamily) =
        boolVaryingFamily := by
    change (constantFamilyOver Bool).obj
        (backward.mapSignature.obj boolVaryingFamily) =
      boolVaryingFamily at atVarying
    exact atVarying
  apply boolVaryingFamily_not_in_essentialImage
  exact ⟨backward.mapSignature.obj boolVaryingFamily,
    ⟨CategoryTheory.eqToIso constantEquality⟩⟩

/-- In particular, the simple-to-dependent route has no strict two-sided
inverse in the heterogeneous institution category. -/
theorem simpleDependentRoute_not_invertible :
    ¬ ∃ backward : dependentObject Bool ⟶ simpleObject Bool,
      CategoryTheory.CategoryStruct.comp (simpleDependentRoute Bool) backward =
          CategoryTheory.CategoryStruct.id (simpleObject Bool) ∧
        CategoryTheory.CategoryStruct.comp backward (simpleDependentRoute Bool) =
          CategoryTheory.CategoryStruct.id (dependentObject Bool) := by
  rintro ⟨backward, _leftInverse, rightInverse⟩
  exact simpleDependentRoute_no_retraction ⟨backward, rightInverse⟩

/-- The positive and negative controls together: the simple fragment embeds
as a composable route, but the dependent bubble contains genuinely new
signatures. -/
theorem simpleDependent_is_proper_atlas_route :
    Nonempty (simpleObject Bool ⟶ dependentObject Bool) ∧
      ¬ ∃ backward : dependentObject Bool ⟶ simpleObject Bool,
        CategoryTheory.CategoryStruct.comp (simpleDependentRoute Bool) backward =
            CategoryTheory.CategoryStruct.id (simpleObject Bool) ∧
          CategoryTheory.CategoryStruct.comp backward (simpleDependentRoute Bool) =
            CategoryTheory.CategoryStruct.id (dependentObject Bool) :=
  ⟨⟨simpleDependentRoute Bool⟩, simpleDependentRoute_not_invertible⟩

#print axioms simpleDependentRoute
#print axioms simpleDependentRoute_mapSignature
#print axioms simpleDependentRoute_no_retraction
#print axioms simpleDependentRoute_not_invertible
#print axioms simpleDependent_is_proper_atlas_route

end Mettapedia.TypeTheory.SimpleDependentInstitutionCategoryCanary
