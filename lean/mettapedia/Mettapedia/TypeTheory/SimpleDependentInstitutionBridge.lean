import Mettapedia.Logic.PredicateInstitution
import Mettapedia.TypeTheory.SetFamilyChangeOfBaseAdjunction
import Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-!
# A model-valued simple-to-dependent institution bridge

Fix a context/index type.  The contextual simple side uses one value type at
every index; the dependent side admits an independently varying family.  Both
sides receive their model-valued institutions from total-space carrier
functors, and the constant-family inclusion induces an institution
comorphism.

This is a semantic comparison specimen, not a claim that the predicate
institutions below are complete presentations of Church simple type theory or
Martin-Lof dependent type theory.  Its content is the exact boundary needed
by a later native-theory route:

* satisfaction and semantic consequence transport along constant families;
* the signature translation is faithful;
* over a context with two points it is not full; and
* a genuinely varying family lies outside its essential image.

Thus dependent typing is not a tax on every theory.  The simple route is
exact on its image, while dependency is required precisely for objects whose
fibres cannot be uniformly represented by one value type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SimpleDependentInstitutionBridge

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.Logic
open Mettapedia.Logic.PredicateInstitution
open Mettapedia.TypeTheory.SetFamilyChangeOfBaseAdjunction
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

universe u

/-- Contextual simple values: a value type is interpreted at every point of
the fixed context. -/
def simpleCarrier (Index : Type u) :
    CategoryTheory.Functor (Type u) (Type u) :=
  (constantFamilyOver Index).comp (totalSpace Index)

/-- Dependent values are elements of the total space of an indexed family. -/
def dependentCarrier (Index : Type u) :
    CategoryTheory.Functor (FamilyOver Index) (Type u) :=
  totalSpace Index

/-- Predicate semantics for the contextual simple fragment. -/
def simpleInstitution (Index : Type u) :=
  PredicateInstitution.ofCarrier (simpleCarrier Index)

/-- Predicate semantics for indexed dependent families. -/
def dependentInstitution (Index : Type u) :=
  PredicateInstitution.ofCarrier (dependentCarrier Index)

/-- The carrier map is definitionally the identity: a contextual simple
value and the total-space value of its constant family retain the same index
and payload. -/
def constantCarrierMap (Index : Type u) :
    simpleCarrier Index ⟶
      (constantFamilyOver Index).comp (dependentCarrier Index) :=
  CategoryTheory.CategoryStruct.id (simpleCarrier Index)

/-- Constant-family inclusion as a full institution comorphism. -/
def simpleToDependent (Index : Type u) :
    Institution.Comorphism (simpleInstitution Index)
      (dependentInstitution Index) :=
  PredicateInstitution.comorphism
    (simpleCarrier Index) (dependentCarrier Index)
    (constantFamilyOver Index) (constantCarrierMap Index)

/-- The satisfaction square for the simple-to-dependent route is exact. -/
theorem satisfaction_iff
    (Index Value : Type u)
    (model : Set (Sigma fun _ : Index => Value))
    (sentence : Sigma fun _ : Index => Value) :
    (dependentInstitution Index).satisfies
        ((simpleToDependent Index).mapSignature.obj Value)
        (CategoryTheory.Discrete.mk model)
        ((simpleToDependent Index).mapSentence.app Value sentence) ↔
      (simpleInstitution Index).satisfies Value
        (((simpleToDependent Index).mapModel.app
          (Opposite.op Value)).toFunctor.obj
            (CategoryTheory.Discrete.mk model))
        sentence :=
  (simpleToDependent Index).satisfaction_condition Value
    (CategoryTheory.Discrete.mk model) sentence

/-- Every simple predicate model is the reduct of the same predicate on its
constant-family carrier.  This is the model-coverage premise that turns the
satisfaction square into consequence reflection. -/
theorem simpleToDependent_coversModels (Index : Type u) :
    (simpleToDependent Index).CoversModels := by
  intro _value sourceModel
  exact ⟨sourceModel, rfl⟩

/-- Semantic consequence is preserved and reflected on the constant-family
image.  This is the exact sense in which the simply typed fragment remains a
conservative mathematical bubble inside the dependent family semantics. -/
theorem entails_iff_constantFamily
    (Index Value : Type u)
    (premises : Set (Sigma fun _ : Index => Value))
    (conclusion : Sigma fun _ : Index => Value) :
    (simpleInstitution Index).Entails Value premises conclusion ↔
      (dependentInstitution Index).Entails
        ((simpleToDependent Index).mapSignature.obj Value)
        (Set.image
          ((simpleToDependent Index).mapSentence.app Value) premises)
        ((simpleToDependent Index).mapSentence.app Value conclusion) :=
  Institution.Comorphism.entails_mapped_iff_of_coversModels
    (simpleToDependent Index)
    (simpleToDependent_coversModels Index)
    Value premises conclusion

/-- When the context is inhabited, constant-family translation loses no
uniform map between value types. -/
@[reducible]
def signatureTranslationFaithful (Index : Type u) [Nonempty Index] :
    (simpleToDependent Index).mapSignature.Faithful :=
  Canary.constantFamilyOverFaithful Index

/-! ## A genuine-dependency falsifier -/

/-- The small family with a singleton false fibre and a Boolean true fibre,
viewed as a dependent signature. -/
def boolVaryingFamily : FamilyOver Bool :=
  ⟨varyingBoolFamily⟩

/-- An isomorphism from a constant family would make every varying fibre
equivalent to one common type. -/
theorem constantIso_gives_uniform_fibres
    (Value : Type) (isomorphism :
      (constantFamilyOver Bool).obj Value ≅ boolVaryingFamily) :
    ∀ index, Nonempty (varyingBoolFamily index ≃ Value) := by
  intro index
  refine ⟨{
    toFun := isomorphism.inv.app index
    invFun := isomorphism.hom.app index
    left_inv := ?_
    right_inv := ?_ }⟩
  · intro value
    have equality := congrArg
      (fun morphism => FamilyOver.Hom.app morphism index value)
      isomorphism.inv_hom_id
    simpa only [boolVaryingFamily, FamilyOver.comp_app,
      FamilyOver.id_app] using equality
  · intro value
    have equality := congrArg
      (fun morphism => FamilyOver.Hom.app morphism index value)
      isomorphism.hom_inv_id
    simpa only [constantFamilyOver, FamilyOver.comp_app,
      FamilyOver.id_app] using equality

/-- Negative control: the varying Boolean family is not isomorphic to any
constant-family signature.  The dependent institution therefore has
strictly more objects than the contextual simple image. -/
theorem boolVaryingFamily_not_in_essentialImage :
    ¬ ∃ Value : Type,
      Nonempty ((constantFamilyOver Bool).obj Value ≅ boolVaryingFamily) := by
  rintro ⟨Value, ⟨isomorphism⟩⟩
  exact varyingBoolFamily_not_constant
    ⟨Value, constantIso_gives_uniform_fibres Value isomorphism⟩

/-- The full boundary at two context points: the institution route preserves
satisfaction and has a faithful signature map, but that map is neither full
nor essentially surjective. -/
theorem bool_simple_dependent_boundary :
    (simpleToDependent Bool).mapSignature.Faithful ∧
      ¬ (simpleToDependent Bool).mapSignature.Full ∧
      ¬ ∃ Value : Type,
        Nonempty ((simpleToDependent Bool).mapSignature.obj Value ≅
          boolVaryingFamily) :=
  ⟨signatureTranslationFaithful Bool,
    Canary.bool_constant_faithful_not_full.2,
    boolVaryingFamily_not_in_essentialImage⟩

#print axioms simpleToDependent
#print axioms satisfaction_iff
#print axioms simpleToDependent_coversModels
#print axioms entails_iff_constantFamily
#print axioms signatureTranslationFaithful
#print axioms constantIso_gives_uniform_fibres
#print axioms boolVaryingFamily_not_in_essentialImage
#print axioms bool_simple_dependent_boundary

end Mettapedia.TypeTheory.SimpleDependentInstitutionBridge
