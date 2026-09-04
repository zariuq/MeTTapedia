import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mettapedia.GSLT.Core.ContextualFamilyPresheaf
import Mettapedia.TypeTheory.SetFamilyTypeOverEssentialImage

/-!
# Change of base for indexed set families

For a fixed index type `Index`, the category `FamilyOver Index` has
families `Index → Type` as objects and fibrewise functions as morphisms.  It is
the vertical, identity-on-index part of the varying-base `IndexedFamily`
category used by the contextual-family presheaf, rather than a second name for
that total category.
There are three standard functors

```text
  totalSpace ⊣ constantFamilyOver ⊣ sectionSpace.
```

The left adjunction is dependent-sum currying and the right adjunction is
dependent-product currying.  These adjunctions are distinct from the live
simple-to-dependent CwF inclusion.  Over a context with more than one point,
ordinary functions between the values of two constant families are uniform,
whereas a displayed map in the simply typed fibre may depend on the context.
Consequently, `constantFamilyOver Bool` is faithful but not full, while
the contextual CwF inclusion is fully faithful.

The module also identifies `FamilyOver Index` fully faithfully with the
fixed-context fibre of the set-families CwF.  Thus the distinction is not an
artifact of a weak family category: it is exactly a distinction between two
source hom-sets.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SetFamilyChangeOfBaseAdjunction

open CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.SetFamilyComprehensionMap
open Mettapedia.TypeTheory.SetFamilyTypeOverEssentialImage

universe u

/-! ## The vertical category of families over a fixed discrete base -/

/-- A type family over a fixed index type. -/
@[ext]
structure FamilyOver (Index : Type u) where
  fibre : Index → Type u

namespace FamilyOver

/-- A morphism of indexed families acts independently in every fibre. -/
@[ext]
structure Hom {Index : Type u} (source target : FamilyOver Index) where
  app : ∀ index, source.fibre index → target.fibre index

instance {Index : Type u} : CategoryTheory.Category.{u} (FamilyOver Index) where
  Hom := Hom
  id family := ⟨fun _ value => value⟩
  comp first second :=
    ⟨fun index value => second.app index (first.app index value)⟩
  id_comp morphism := by
    ext index value
    rfl
  comp_id morphism := by
    ext index value
    rfl
  assoc first second third := by
    ext index value
    rfl

@[simp]
theorem id_app {Index : Type u} (family : FamilyOver Index)
    (index : Index) (value : family.fibre index) :
    Hom.app (𝟙 family) index value = value :=
  rfl

@[simp]
theorem comp_app {Index : Type u} {first second third : FamilyOver Index}
    (left : first ⟶ second) (right : second ⟶ third)
    (index : Index) (value : first.fibre index) :
    Hom.app (left ≫ right) index value =
      right.app index (left.app index value) :=
  rfl

end FamilyOver

variable {Index : Type u}

/-- Include the fixed-base vertical family category into the varying-base
category used by the CwF family presheaf. -/
def toVaryingBaseIndexedFamily (Index : Type u) :
    FamilyOver Index ⥤
      Mettapedia.GSLT.Core.ContextualLadder.IndexedFamily.{u, u} where
  obj family :=
    { Index := Index
      Fibre := family.fibre }
  map morphism :=
    { onIndex := id
      onFibre := morphism.app }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The vertical inclusion loses no fixed-index fibre maps. -/
@[reducible]
def toVaryingBaseIndexedFamilyFaithful (Index : Type u) :
    (toVaryingBaseIndexedFamily Index).Faithful where
  map_injective := by
    intro source target first second sameImage
    have fibreEquality : first.app = second.app := by
      change
        ({ onIndex := id
           onFibre := first.app } :
          Mettapedia.GSLT.Core.ContextualLadder.IndexedFamily.Hom
            ((toVaryingBaseIndexedFamily Index).obj source)
            ((toVaryingBaseIndexedFamily Index).obj target)) =
        { onIndex := id
          onFibre := second.app } at sameImage
      injection sameImage
    apply FamilyOver.Hom.ext
    exact fibreEquality

/-! ## Total space, constant family, and section space -/

/-- Send a family to its dependent total space. -/
def totalSpace (Index : Type u) : FamilyOver Index ⥤ Type u where
  obj family := Sigma family.fibre
  map morphism := TypeCat.ofHom fun point =>
    ⟨point.1, morphism.app point.1 point.2⟩
  map_id family := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext point
    rcases point with ⟨index, value⟩
    rfl
  map_comp first second := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext point
    rcases point with ⟨index, value⟩
    rfl

/-- Regard one type as the same fibre at every index. -/
def constantFamilyOver (Index : Type u) : Type u ⥤ FamilyOver Index where
  obj valueType := ⟨fun _ => valueType⟩
  map function := ⟨fun _ => function⟩
  map_id valueType := by
    apply FamilyOver.Hom.ext
    funext index value
    rfl
  map_comp first second := by
    apply FamilyOver.Hom.ext
    funext index value
    rfl

/-- Send a family to its type of global sections. -/
def sectionSpace (Index : Type u) : FamilyOver Index ⥤ Type u where
  obj family := ∀ index, family.fibre index
  map morphism := TypeCat.ofHom fun globalSection index =>
    morphism.app index (globalSection index)
  map_id family := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext globalSection index
    rfl
  map_comp first second := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext globalSection index
    rfl

/-! ## The adjoint triple -/

/-- Maps out of a total space are the same as fibrewise maps into a constant
family. -/
def totalConstantHomEquiv (family : FamilyOver Index) (target : Type u) :
    ((totalSpace Index).obj family ⟶ target) ≃
      (family ⟶ (constantFamilyOver Index).obj target) where
  toFun function := ⟨fun index value => function ⟨index, value⟩⟩
  invFun morphism := TypeCat.ofHom fun point =>
    morphism.app point.1 point.2
  left_inv function := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext point
    rcases point with ⟨index, value⟩
    rfl
  right_inv morphism := by
    apply FamilyOver.Hom.ext
    funext index value
    rfl

/-- The dependent total-space functor is left adjoint to the constant-family
functor. -/
def totalSpaceAdjunction (Index : Type u) :
    totalSpace Index ⊣ constantFamilyOver Index :=
  CategoryTheory.Adjunction.mkOfHomEquiv {
    homEquiv := totalConstantHomEquiv
    homEquiv_naturality_left_symm := by
      intro source target valueType familyMap constantMap
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      funext point
      rcases point with ⟨index, value⟩
      rfl
    homEquiv_naturality_right := by
      intro family source target function valueMap
      apply FamilyOver.Hom.ext
      funext index value
      rfl }

/-- Fibrewise maps from a constant family are the same as maps into the
dependent section space. -/
def constantSectionHomEquiv (source : Type u) (family : FamilyOver Index) :
    ((constantFamilyOver Index).obj source ⟶ family) ≃
      (source ⟶ (sectionSpace Index).obj family) where
  toFun morphism := TypeCat.ofHom fun value index => morphism.app index value
  invFun function := ⟨fun index value => function value index⟩
  left_inv morphism := by
    apply FamilyOver.Hom.ext
    funext index value
    rfl
  right_inv function := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value index
    rfl

/-- The constant-family functor is left adjoint to dependent sections. -/
def constantSectionAdjunction (Index : Type u) :
    constantFamilyOver Index ⊣ sectionSpace Index :=
  CategoryTheory.Adjunction.mkOfHomEquiv {
    homEquiv := constantSectionHomEquiv
    homEquiv_naturality_left_symm := by
      intro source target family valueMap sectionMap
      apply FamilyOver.Hom.ext
      funext index value
      rfl
    homEquiv_naturality_right := by
      intro source first second constantMap familyMap
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      funext value index
      rfl }

/-! ## Exact connection to the set-families CwF fibre -/

/-- A fibrewise family map induces its display map over the unchanged base. -/
def toTypeOver (Index : Type u) :
    FamilyOver Index ⥤ TypeOver (familiesCwf.{u}) Index where
  obj family := ⟨family.fibre⟩
  map morphism := displayMap morphism.app
  map_id family := by
    apply TypeOver.Hom.ext
    funext point
    rcases point with ⟨index, value⟩
    rfl
  map_comp first second := by
    apply TypeOver.Hom.ext
    funext point
    rcases point with ⟨index, value⟩
    rfl

/-- The fixed-index family category is not a lossy proxy for the dependent
fibre: every display map over the identity base is recovered fibrewise. -/
def toTypeOverFullyFaithful (Index : Type u) :
    (toTypeOver Index).FullyFaithful where
  preimage morphism := ⟨fibreMapOfDisplayHom morphism⟩
  map_preimage morphism := by
    apply TypeOver.Hom.ext
    exact (displayHom_substitution_eq_totalMap morphism).symm
  preimage_map morphism := by
    apply FamilyOver.Hom.ext
    funext index value
    rfl

/-- On objects, the ordinary constant-family functor and the live
simple-to-dependent CwF inclusion select the same dependent family. -/
theorem constant_object_agrees_with_contextual_inclusion
    (Index valueType : Type u) :
    (toTypeOver Index).obj ((constantFamilyOver Index).obj valueType) =
      (simpleToDependentTypeFunctor Index).obj
        (⟨valueType⟩ : TypeOver (SimpleFamiliesCwf.{u}) Index) :=
  rfl

/-! ## Positive and negative controls for fullness -/

namespace Canary

/-- A displayed map between constant Boolean families whose value is the
current observer/index.  It cannot arise from one uniform function. -/
def observerIndexedArrow :
    (constantFamilyOver Bool).obj PUnit ⟶
      (constantFamilyOver Bool).obj Bool :=
  ⟨fun observer _ => observer⟩

/-- The observer-indexed arrow is not the constant-family image of any
ordinary function. -/
theorem observerIndexedArrow_not_in_uniform_image :
    ¬ ∃ function : PUnit ⟶ Bool,
      (constantFamilyOver Bool).map function = observerIndexedArrow := by
  rintro ⟨function, imageEquality⟩
  have atFalse := congrArg
    (fun morphism => morphism.app false PUnit.unit) imageEquality
  have atTrue := congrArg
    (fun morphism => morphism.app true PUnit.unit) imageEquality
  change function PUnit.unit = false at atFalse
  change function PUnit.unit = true at atTrue
  exact Bool.false_ne_true (atFalse.symm.trans atTrue)

/-- A nonempty index lets one recover a uniform map by inspecting any one
fibre, so the constant-family functor is faithful. -/
@[reducible]
def constantFamilyOverFaithful (Index : Type u) [Nonempty Index] :
    (constantFamilyOver Index).Faithful where
  map_injective := by
    intro source target first second sameImage
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    let index : Index := Classical.choice (inferInstance : Nonempty Index)
    exact congrArg
      (fun morphism => FamilyOver.Hom.app morphism index value) sameImage

/-- Over two observers, constant families are faithful but not full. -/
theorem bool_constant_faithful_not_full :
    (constantFamilyOver Bool).Faithful ∧
      ¬ (constantFamilyOver Bool).Full := by
  refine ⟨constantFamilyOverFaithful Bool, ?_⟩
  intro full
  rcases full.map_surjective observerIndexedArrow with
    ⟨function, imageEquality⟩
  exact observerIndexedArrow_not_in_uniform_image
    ⟨function, imageEquality⟩

/-- In contrast, the contextual simple-to-dependent inclusion is fully
faithful at the same Boolean context.  The difference is that its source
morphisms may already depend on the context. -/
def contextualInclusionFullyFaithfulAtBool :
    (simpleToDependentTypeFunctor Bool).FullyFaithful :=
  simpleToDependentTypeFunctorFullyFaithful Bool

/-- The two facts coexist: ordinary constant diagrams are not full, while
the contextual CwF inclusion on the same objects is fully faithful. -/
theorem hom_set_boundary_at_two_observers :
    (¬ (constantFamilyOver Bool).Full) ∧
      Nonempty (simpleToDependentTypeFunctor Bool).FullyFaithful :=
  ⟨bool_constant_faithful_not_full.2,
    ⟨contextualInclusionFullyFaithfulAtBool⟩⟩

end Canary

#print axioms totalSpaceAdjunction
#print axioms constantSectionAdjunction
#print axioms toVaryingBaseIndexedFamilyFaithful
#print axioms toTypeOverFullyFaithful
#print axioms Canary.observerIndexedArrow_not_in_uniform_image
#print axioms Canary.bool_constant_faithful_not_full
#print axioms Canary.hom_set_boundary_at_two_observers

end Mettapedia.TypeTheory.SetFamilyChangeOfBaseAdjunction
