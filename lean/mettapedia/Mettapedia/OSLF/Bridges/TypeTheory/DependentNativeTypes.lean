import Mettapedia.OSLF.PresheafNativeType.InternalLanguage
import Mettapedia.TypeTheory.DisplayedPresheafSlicePi
import Mettapedia.TypeTheory.DisplayedPresheafSliceSigma
import Mettapedia.TypeTheory.DisplayedPresheafSupport
import Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution
import Mettapedia.TypeTheory.PresheafDependentBaseChange

/-!
# Dependent native types through the shared presheaf family model

The existing CwF's dependent families and terms interpret into NTT's
codomain semantics by the family--slice equivalence. Its substitution
agrees with NTT's chosen Cartesian lift, and its sums/products agree with
slice composition and the right adjoint to pullback. Image formation is
the existing predicate support, so witness retention and propositional
observation remain distinct operations.

This joins the dependent operations relevant to NTT Propositions 20 and 22.
It does not assert a generated-syntax initiality theorem, the full logical
slice pseudofunctor, or the all-toposes 2-functor of Theorem 23.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.DependentNativeTypes

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice DisplayedPresheafSliceSubstitution
open Mettapedia.OSLF.PresheafNativeType
open Mettapedia.GSLT.Topos

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Face.{u, u, u} C}

/-- The shared CwF's substituted comprehension is NTT's actual chosen
Cartesian lift, up to the canonical isomorphism over the new context. -/
noncomputable def nativeCartesianLiftIso (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P) :
    Arrow.mk (totalProjection (reindexDisplayed f A)) ≅
      def21_cartesianLift (Arrow.mk (totalProjection A)) f :=
  Arrow.isoMk (totalReindexMap_isPullback f A).flip.isoPullback (Iso.refl Q)
    (by
      change (totalReindexMap_isPullback f A).flip.isoPullback.hom ≫
        pullback.snd (totalProjection A) f =
          totalProjection (reindexDisplayed f A) ≫ 𝟙 Q
      rw [Category.comp_id]
      exact (totalReindexMap_isPullback f A).flip.isoPullback_hom_snd)

/-- The comparison also identifies the morphism into the original
dependent type; both the context map and evidence map are retained. -/
theorem nativeCartesianLiftIso_morphism (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P) :
    (nativeCartesianLiftIso f A).hom ≫
      def21_cartesianLiftMorphism (Arrow.mk (totalProjection A)) f =
      Arrow.homMk (totalReindexMap f A) f (totalReindexMap_square f A) := by
  apply Arrow.hom_ext
  · exact (totalReindexMap_isPullback f A).flip.isoPullback_hom_fst
  · change (𝟙 Q) ≫ f = f
    exact Category.id_comp f

/-- The native context map has dependent sums and products on complete
slice objects, strengthening its separate predicate quantifier package. -/
noncomputable def nativeDependentAdjoints
    (context : PresheafDepCtx.{u, u, u} (C := C)) :
    (Over.map context.f ⊣ Over.pullback context.f) ×
      (Over.pullback context.f ⊣
        PresheafDependentAdjunction.dependentProduct context.f) :=
  PresheafDependentAdjunction.adjointTriple context.f

/-- Native dependent products commute with context substitution along
the actual CwF comprehension square. The entire proof family is retained. -/
noncomputable def nativeProductSubstitutionIso (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P) :
    PresheafDependentAdjunction.dependentProduct (totalProjection A) ⋙
        Over.pullback f ≅
      Over.pullback (totalReindexMap f A) ⋙
        PresheafDependentAdjunction.dependentProduct
          (totalProjection (reindexDisplayed f A)) :=
  PresheafDependentBaseChange.piBaseChange (totalReindexMap_isPullback f A).flip

/-- The image of native comprehension agrees with the existing support
predicate of the proof-relevant family. -/
theorem nativeImage_eq_support (A : DisplayedFamily.{u, u, u, u} P) :
    objectPredicate
        (ImageComprehension.imageFunctor.obj (Arrow.mk (totalProjection A))) =
      support A := by
  change Subfunctor.range (totalProjection A) = support A
  exact (DisplayedPresheafSupport.support_eq_comprehension_range A).symm

end Mettapedia.OSLF.Bridges.TypeTheory.DependentNativeTypes
