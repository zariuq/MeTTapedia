import Mettapedia.TypeTheory.DisplayedPresheafSliceSubstitution
import Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Successor-ambient native codomain adjunctions

The context category remains at the original bound, while the presheaf
parameters and arbitrary dependent codomains inhabit its successor universe.
The actual family--slice and substitution comparisons transport right Kan
extension to dependent products along every natural map in this ambient.

This optional host profile uses Mathlib's chosen limits, right extensions,
and functor/slice category interfaces. Their external classical dependency
is not an axiom of a native language or a proof that material member fibres
have a small bound. Original-bound member comparisons are separate proofs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceWiderPresheafNativeAdjunction

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafSlice DisplayedPresheafSliceSubstitution

universe u

variable {C : Type u} [Category.{u} C]
variable {P Q : Face.{u, u, u + 1} C}

noncomputable def familyAdjunction (change : Q ⟶ P) :
    reindexFunctor change ⊣ change.mapElements.ran :=
  change.mapElements.ranAdjunction (Type (u + 1))

noncomputable def pullbackAsFamilies (change : Q ⟶ P) :
    (fibreFunctor P ⋙ reindexFunctor change) ⋙ totalFunctor Q ≅ Over.pullback change :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (fibreFunctor P) (substitutionIso change) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (counitIso P) (Over.pullback change) ≪≫
    Functor.leftUnitor _

noncomputable def dependentProduct (change : Q ⟶ P) : Over Q ⥤ Over P :=
  fibreFunctor Q ⋙ change.mapElements.ran ⋙ totalFunctor P

noncomputable def dependentAdjunction (change : Q ⟶ P) :
    Over.pullback change ⊣ dependentProduct change :=
  (((equivalence P).symm.toAdjunction.comp (familyAdjunction change)).comp
    (equivalence Q).toAdjunction).ofNatIsoLeft (pullbackAsFamilies change)

noncomputable def evaluation (change : Q ⟶ P) (body : Over Q) :
    (Over.pullback change).obj ((dependentProduct change).obj body) ⟶ body :=
  (dependentAdjunction change).counit.app body

noncomputable def transpose (change : Q ⟶ P) {parameters : Over P} {body : Over Q}
    (operation : (Over.pullback change).obj parameters ⟶ body) :
    parameters ⟶ (dependentProduct change).obj body :=
  (dependentAdjunction change).homEquiv parameters body operation

theorem beta (change : Q ⟶ P) {parameters : Over P} {body : Over Q}
    (operation : (Over.pullback change).obj parameters ⟶ body) :
    (Over.pullback change).map (transpose change operation) ≫ evaluation change body = operation := by
  change ((dependentAdjunction change).homEquiv parameters body).symm
    ((dependentAdjunction change).homEquiv parameters body operation) = operation
  exact Equiv.symm_apply_apply _ operation

theorem eta (change : Q ⟶ P) {parameters : Over P} {body : Over Q}
    (operation : parameters ⟶ (dependentProduct change).obj body) :
    transpose change ((Over.pullback change).map operation ≫ evaluation change body) = operation := by
  change (dependentAdjunction change).homEquiv parameters body
    (((dependentAdjunction change).homEquiv parameters body).symm operation) = operation
  exact Equiv.apply_symm_apply _ operation

theorem transpose_unique (change : Q ⟶ P) {parameters : Over P} {body : Over Q}
    (operation : (Over.pullback change).obj parameters ⟶ body)
    (candidate : parameters ⟶ (dependentProduct change).obj body)
    (computes : (Over.pullback change).map candidate ≫ evaluation change body = operation) :
    candidate = transpose change operation := by
  rw [← computes, eta]

noncomputable def adjointTriple (change : Q ⟶ P) :
    (Over.map change ⊣ Over.pullback change) ×
      (Over.pullback change ⊣ dependentProduct change) :=
  ⟨Over.mapPullbackAdj change, dependentAdjunction change⟩

noncomputable def dependentProductId (P : Face.{u, u, u + 1} C) :
    dependentProduct (𝟙 P) ≅ 𝟭 (Over P) :=
  Adjunction.rightAdjointUniq
    ((dependentAdjunction (𝟙 P)).ofNatIsoLeft Over.pullbackId)
    (Adjunction.id (C := Over P))

noncomputable def dependentProductComp {R : Face.{u, u, u + 1} C}
    (earlier : R ⟶ Q) (later : Q ⟶ P) :
    dependentProduct (earlier ≫ later) ≅ dependentProduct earlier ⋙ dependentProduct later :=
  Adjunction.rightAdjointUniq
    ((dependentAdjunction (earlier ≫ later)).ofNatIsoLeft (Over.pullbackComp earlier later))
    ((dependentAdjunction later).comp (dependentAdjunction earlier))

end Mettapedia.TypeTheory.HostChoiceWiderPresheafNativeAdjunction
