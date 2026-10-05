import Mettapedia.TypeTheory.DisplayedPresheafSliceSubstitution
import Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Dependent products on presheaf slices

The same right-Kan construction used for category-indexed dependent
families supplies dependent products along every natural map of small
presheaves. The family--slice equivalence identifies its left adjoint with
the actual slice pullback. Thus these are dependent products in the
codomain semantics, with natural abstraction/application and beta/eta laws.

Dependent sums are the existing slice composition functors. Together the
two adjunctions give `Sigma_f ⊣ f* ⊣ Pi_f`, retaining arbitrary type-valued
fibres rather than replacing them by predicates of inhabitation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafDependentAdjunction

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafSlice DisplayedPresheafSliceSubstitution

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Face.{u, u, u} C}

/-- Right Kan extension is right adjoint to the existing family substitution. -/
noncomputable def familyAdjunction (f : Q ⟶ P) :
    reindexFunctor f ⊣ f.mapElements.ran :=
  f.mapElements.ranAdjunction (Type u)

/-- Recovering a slice's family, substituting, and taking its total space
is naturally the chosen slice pullback. -/
noncomputable def pullbackAsFamilies (f : Q ⟶ P) :
    (fibreFunctor P ⋙ reindexFunctor f) ⋙ totalFunctor Q ≅ Over.pullback f :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (fibreFunctor P) (substitutionIso f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (counitIso P) (Over.pullback f) ≪≫
    Functor.leftUnitor _

/-- The dependent product retains the full family of natural dependent
functions. Its construction uses the existing right-Kan functor. -/
noncomputable def dependentProduct (f : Q ⟶ P) : Over Q ⥤ Over P :=
  fibreFunctor Q ⋙ f.mapElements.ran ⋙ totalFunctor P

/-- Dependent function abstraction and application over presheaf slices. -/
noncomputable def dependentAdjunction (f : Q ⟶ P) :
    Over.pullback f ⊣ dependentProduct f :=
  (((equivalence P).symm.toAdjunction.comp (familyAdjunction f)).comp
    (equivalence Q).toAdjunction).ofNatIsoLeft (pullbackAsFamilies f)

/-- Application is the counit at an arbitrary dependent codomain. -/
noncomputable def evaluation (f : Q ⟶ P) (B : Over Q) :
    (Over.pullback f).obj ((dependentProduct f).obj B) ⟶ B :=
  (dependentAdjunction f).counit.app B

/-- Abstraction is the adjoint transpose of a map over the extended base. -/
noncomputable def transpose (f : Q ⟶ P) {A : Over P} {B : Over Q}
    (body : (Over.pullback f).obj A ⟶ B) :
    A ⟶ (dependentProduct f).obj B :=
  (dependentAdjunction f).homEquiv A B body

/-- Applying an abstraction recovers the entire original slice morphism. -/
theorem beta (f : Q ⟶ P) {A : Over P} {B : Over Q}
    (body : (Over.pullback f).obj A ⟶ B) :
    (Over.pullback f).map (transpose f body) ≫ evaluation f B = body := by
  change ((dependentAdjunction f).homEquiv A B).symm
    ((dependentAdjunction f).homEquiv A B body) = body
  exact Equiv.symm_apply_apply _ body

/-- A dependent function is recovered from its evaluation body. -/
theorem eta (f : Q ⟶ P) {A : Over P} {B : Over Q}
    (function : A ⟶ (dependentProduct f).obj B) :
    transpose f ((Over.pullback f).map function ≫ evaluation f B) = function := by
  change (dependentAdjunction f).homEquiv A B
    (((dependentAdjunction f).homEquiv A B).symm function) = function
  exact Equiv.apply_symm_apply _ function

/-- The transpose is the unique dependent function with its stated body. -/
theorem transpose_unique (f : Q ⟶ P) {A : Over P} {B : Over Q}
    (body : (Over.pullback f).obj A ⟶ B)
    (function : A ⟶ (dependentProduct f).obj B)
    (computes : (Over.pullback f).map function ≫ evaluation f B = body) :
    function = transpose f body := by
  rw [← computes, eta]

/-- The actual codomain semantics has both dependent adjunctions along
every map: composition is Sigma, pullback is substitution, and the
transported right Kan extension is Pi. -/
noncomputable def adjointTriple (f : Q ⟶ P) :
    (Over.map f ⊣ Over.pullback f) ×
      (Over.pullback f ⊣ dependentProduct f) :=
  ⟨Over.mapPullbackAdj f, dependentAdjunction f⟩

/-- Product along an identity is the identity, by uniqueness of right
adjoints to the actual identity pullback comparison. -/
noncomputable def dependentProductId (P : Face.{u, u, u} C) :
    dependentProduct (𝟙 P) ≅ 𝟭 (Over P) :=
  Adjunction.rightAdjointUniq
    ((dependentAdjunction (𝟙 P)).ofNatIsoLeft Over.pullbackId)
    (Adjunction.id (C := Over P))

/-- Iterated dependent products agree with product along the composite
base map, with the comparison fixed by their adjunctions. -/
noncomputable def dependentProductComp {R : Face.{u, u, u} C}
    (f : R ⟶ Q) (g : Q ⟶ P) :
    dependentProduct (f ≫ g) ≅ dependentProduct f ⋙ dependentProduct g :=
  Adjunction.rightAdjointUniq
    ((dependentAdjunction (f ≫ g)).ofNatIsoLeft (Over.pullbackComp f g))
    ((dependentAdjunction g).comp (dependentAdjunction f))

end Mettapedia.TypeTheory.PresheafDependentAdjunction
