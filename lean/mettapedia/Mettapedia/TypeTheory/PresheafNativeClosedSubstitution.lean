import Mettapedia.TypeTheory.PresheafNativeLogicalAction

/-!
# Closed slice semantics of native context substitution

Each native display object is its actual comprehension map. Display arrows
are the complete commuting substitutions of those maps. This gives a fully
faithful and essentially surjective functor to the actual presheaf slice.
The native reindexing functor commutes with slice pullback on complete arrows,
through the selected comprehension pullback comparison. Consequently the
existing closed pullback and its evaluation law apply to these native
specifications and actual substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativeClosedSubstitution

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafSliceSubstitution DisplayedPresheafCwf ContextualLocalUniverses
open NativeLocalTheoryTransformation

universe u
variable {C : Type u} [Category.{u} C]

def toSlice (P : Cᵒᵖ ⥤ Type u) :
    TypeOver (nativeLocalModel C).toCwf P ⥤ Over P where
  obj A := Over.mk (totalProjection A.val.decoded)
  map arrow := Over.homMk arrow.substitution arrow.over
  map_id _ := Over.OverMorphism.ext rfl
  map_comp _ _ := Over.OverMorphism.ext rfl

/-- The complete contextual substitution is exactly the slice arrow,
including both coordinates of every supplied comprehension receipt. -/
theorem toSlice_map {P : Cᵒᵖ ⥤ Type u}
    {A B : TypeOver (nativeLocalModel C).toCwf P} (arrow : A ⟶ B) :
    ((toSlice P).map arrow).left = arrow.substitution := rfl

def fullyFaithful (P : Cᵒᵖ ⥤ Type u) : (toSlice P).FullyFaithful where
  preimage arrow := ⟨arrow.left, Over.w arrow⟩
  map_preimage _ := Over.OverMorphism.ext rfl
  preimage_map _ := TypeOver.Hom.ext rfl

instance essentiallySurjective (P : Cᵒᵖ ⥤ Type u) : (toSlice P).EssSurj where
  mem_essImage X :=
    ⟨⟨LocalType.present ((fibreFunctor P).obj X)⟩, ⟨(counitIso P).app X⟩⟩

instance isEquivalence (P : Cᵒᵖ ⥤ Type u) : (toSlice P).IsEquivalence where
  faithful := (fullyFaithful P).faithful
  full := (fullyFaithful P).full

noncomputable def sliceEquivalence (P : Cᵒᵖ ⥤ Type u) :
    TypeOver (nativeLocalModel C).toCwf P ≌ Over P := (toSlice P).asEquivalence

/-- Finite products are transported through the actual, fully faithful
native comprehension equivalence. -/
instance native_finiteProducts (P : Cᵒᵖ ⥤ Type u) :
    HasFiniteProducts (TypeOver (nativeLocalModel C).toCwf P) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (toSlice P)

noncomputable instance native_cartesian (P : Cᵒᵖ ⥤ Type u) :
    CartesianMonoidalCategory (TypeOver (nativeLocalModel C).toCwf P) :=
  CartesianMonoidalCategory.ofHasFiniteProducts

/-- Native display specifications are cartesian closed, with the
exponential structure transported from the actual presheaf slice. -/
noncomputable instance native_closed (P : Cᵒᵖ ⥤ Type u) :
    MonoidalClosed (TypeOver (nativeLocalModel C).toCwf P) :=
  cartesianClosedOfEquiv (sliceEquivalence P).symm

noncomputable instance toSlice_closed (P : Cᵒᵖ ⥤ Type u) :
    MonoidalClosedFunctor (toSlice P) :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts (toSlice P)
    (sliceEquivalence P).symm.toAdjunction

noncomputable def displayExponentialComparison (P : Cᵒᵖ ⥤ Type u)
    (A B : TypeOver (nativeLocalModel C).toCwf P) :
    (toSlice P).obj ((ihom A).obj B) ≅
      (ihom ((toSlice P).obj A)).obj ((toSlice P).obj B) :=
  asIso ((expComparison (toSlice P) A).natTrans.app B)

/-- The native exponential is related to the actual slice exponential
by its canonical comparison, including evaluation rather than only
an equality of available carrier types. -/
theorem displayExponential_evaluation (P : Cᵒᵖ ⥤ Type u)
    (A B : TypeOver (nativeLocalModel C).toCwf P) :
    MonoidalCategory.whiskerLeft ((toSlice P).obj A)
        (displayExponentialComparison P A B).hom ≫
      (ihom.ev ((toSlice P).obj A)).app ((toSlice P).obj B) =
      inv (CartesianMonoidalCategory.prodComparison
        (toSlice P) A ((ihom A).obj B)) ≫
        (toSlice P).map ((ihom.ev A).app B) :=
  expComparison_ev (toSlice P) A B

variable {P Q : Cᵒᵖ ⥤ Type u}

noncomputable def reindexObjectIso (substitution : Q ⟶ P)
    (A : TypeOver (nativeLocalModel C).toCwf P) :
    (toSlice Q).obj (TypeOver.reindexObject substitution A) ≅
      (Over.pullback substitution).obj ((toSlice P).obj A) :=
  reindexTotalIso substitution A.val.decoded

theorem extensionSubstitution_as_total (substitution : Q ⟶ P)
    (A : TypeOver (nativeLocalModel C).toCwf P) :
    TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf) substitution A.val =
      totalReindexMap substitution A.val.decoded := rfl

attribute [local irreducible] TypeOver.reindexArrow TypeOver.extensionSubstitution

theorem reindex_arrow_square (substitution : Q ⟶ P)
    {A B : TypeOver (nativeLocalModel C).toCwf P} (arrow : A ⟶ B) :
    (TypeOver.reindexArrow substitution arrow).substitution ≫
        totalReindexMap substitution B.val.decoded =
      totalReindexMap substitution A.val.decoded ≫ arrow.substitution := by
  have square := TypeOver.extensionSubstitution_naturality
    (C := (nativeLocalModel C).toCwf) substitution arrow
  change (TypeOver.reindexArrow substitution arrow).substitution ≫
    TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf) substitution B.val =
      TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf)
        substitution A.val ≫ arrow.substitution at square
  have first := congrArg (fun operation =>
    (TypeOver.reindexArrow substitution arrow).substitution ≫ operation)
      (extensionSubstitution_as_total substitution B)
  have last := congrArg (fun operation => operation ≫ arrow.substitution)
    (extensionSubstitution_as_total substitution A)
  exact first.symm.trans (square.trans last)

theorem reindex_arrow_over (substitution : Q ⟶ P)
    {A B : TypeOver (nativeLocalModel C).toCwf P} (arrow : A ⟶ B) :
    (TypeOver.reindexArrow substitution arrow).substitution ≫
        totalProjection (reindexDisplayed substitution B.val.decoded) =
      totalProjection (reindexDisplayed substitution A.val.decoded) :=
  (TypeOver.reindexArrow (C := (nativeLocalModel C).toCwf) substitution arrow).over

set_option backward.isDefEq.respectTransparency false in
/-- This comparison is natural in every complete native display arrow;
it does not assume that a supplied evidence map is invertible. -/
noncomputable def reindexingIso (substitution : Q ⟶ P) :
    TypeOver.reindexFunctor (C := (nativeLocalModel C).toCwf) substitution ⋙ toSlice Q ≅
      toSlice P ⋙ Over.pullback substitution := by
  refine NatIso.ofComponents (reindexObjectIso substitution) ?_
  intro A B arrow
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change
      (((TypeOver.reindexArrow substitution arrow).substitution ≫
        (reindexTotalIso substitution B.val.decoded).hom.left) ≫ _) =
      (((reindexTotalIso substitution A.val.decoded).hom.left ≫
        ((Over.pullback substitution).map ((toSlice P).map arrow)).left) ≫ _)
    simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    change (TypeOver.reindexArrow substitution arrow).substitution ≫
      (reindexTotalIso substitution B.val.decoded).hom.left ≫
        pullback.fst (totalProjection B.val.decoded) substitution =
      (reindexTotalIso substitution A.val.decoded).hom.left ≫
        pullback.fst (totalProjection A.val.decoded) substitution ≫ arrow.substitution
    rw [reindexTotalIso_hom_fst, ← Category.assoc, reindexTotalIso_hom_fst]
    exact reindex_arrow_square substitution arrow
  · change
      (((TypeOver.reindexArrow substitution arrow).substitution ≫
        (reindexTotalIso substitution B.val.decoded).hom.left) ≫ _) =
      (((reindexTotalIso substitution A.val.decoded).hom.left ≫
        ((Over.pullback substitution).map ((toSlice P).map arrow)).left) ≫ _)
    simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd]
    change (TypeOver.reindexArrow substitution arrow).substitution ≫
      (reindexTotalIso substitution B.val.decoded).hom.left ≫
        pullback.snd (totalProjection B.val.decoded) substitution =
      (reindexTotalIso substitution A.val.decoded).hom.left ≫
        pullback.snd (totalProjection A.val.decoded) substitution
    rw [reindexTotalIso_hom_snd, reindexTotalIso_hom_snd]
    exact reindex_arrow_over substitution arrow

noncomputable def nativeExponentialComparison (substitution : Q ⟶ P)
    (A B : TypeOver (nativeLocalModel C).toCwf P) :
    (PresheafClosedComprehension.substitution substitution).obj
        ((ihom ((toSlice P).obj A)).obj ((toSlice P).obj B)) ≅
      (ihom ((PresheafClosedComprehension.substitution substitution).obj ((toSlice P).obj A))).obj
        ((PresheafClosedComprehension.substitution substitution).obj ((toSlice P).obj B)) :=
  PresheafClosedComprehension.exponentialComparison substitution ((toSlice P).obj A) ((toSlice P).obj B)

/-- Actual slice evaluation applies to the native display interpretations;
the preceding natural isomorphism identifies their native substitution. -/
theorem nativeExponential_evaluation (substitution : Q ⟶ P)
    (A B : TypeOver (nativeLocalModel C).toCwf P) :
    MonoidalCategory.whiskerLeft
        ((PresheafClosedComprehension.substitution substitution).obj ((toSlice P).obj A))
        (nativeExponentialComparison substitution A B).hom ≫
      (ihom.ev ((PresheafClosedComprehension.substitution substitution).obj ((toSlice P).obj A))).app
        ((PresheafClosedComprehension.substitution substitution).obj ((toSlice P).obj B)) =
      inv (CartesianMonoidalCategory.prodComparison
        (PresheafClosedComprehension.substitution substitution)
          ((toSlice P).obj A) ((ihom ((toSlice P).obj A)).obj ((toSlice P).obj B))) ≫
        (PresheafClosedComprehension.substitution substitution).map
          ((ihom.ev ((toSlice P).obj A)).app ((toSlice P).obj B)) :=
  PresheafClosedComprehension.exponential_evaluation substitution ((toSlice P).obj A) ((toSlice P).obj B)

end Mettapedia.TypeTheory.PresheafNativeClosedSubstitution
