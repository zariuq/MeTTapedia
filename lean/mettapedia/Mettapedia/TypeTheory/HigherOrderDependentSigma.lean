import Mettapedia.CategoryTheory.FibrationAdjunctionTwoCategory
import Mettapedia.TypeTheory.HigherOrderDependentSigmaStructure

/-!
# Higher-order dependent sum profiles in the adjunction two-category

The object profile has full closed comprehension for kinds and types,
connected by a fibred reflection over their common base. Quantification
and strong sums concern the actual display projections, and substitution
uses their canonical Beck--Chevalley mates. A terminal kind displays the
base of an actual generic type object. Arbitrary models need not have
preordered fibres or monic displays; predicates give a logical instance.

The full object sub-bicategory keeps every ambient invertible right square
and compatible endpoint cell. Invertibility of the canonical left mate
remains a separate strong-map property. Completeness of the total
categories is not required of an arbitrary elementary-topos language.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.HigherOrderDependentSigma

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open Mettapedia.CategoryTheory
open Mettapedia.CategoryTheory.FibrationTwoCategory

universe u v p f h

set_option linter.checkUnivs false in
abbrev Profile (object : FibrationAdjunctionTwoCategory.{u,v}) :=
  HigherOrderDependentSigmaStructure.Profile.{u,v,p,f,h} object

set_option linter.checkUnivs false in
/-- Only objects are restricted. The ambient maps and cells are retained
without adding a left-mate invertibility condition. -/
abbrev Theory := {object : FibrationAdjunctionTwoCategory.{u,v} //
  Nonempty (Profile.{u,v,p,f,h} object)}

set_option linter.checkUnivs false in
abbrev TwoCategory :=
  InducedBicategory FibrationAdjunctionTwoCategory.{u,v}
    (fun object : Theory.{u,v,p,f,h} => object.val)

def forget : StrictPseudofunctor TwoCategory.{u,v,p,f,h}
    FibrationAdjunctionTwoCategory.{u,v} := InducedBicategory.forget

instance localFaithful (source target : TwoCategory.{u,v,p,f,h}) :
    (forget.mapFunctor source target).Faithful where
  map_injective same := InducedBicategory.hom₂_ext same

instance localFull (source target : TwoCategory.{u,v,p,f,h}) :
    (forget.mapFunctor source target).Full where
  map_surjective change := ⟨⟨change⟩, rfl⟩

def Strong {source target : TwoCategory.{u,v,p,f,h}} (route : source ⟶ target) : Prop :=
  AdjunctionTwoCategory.Strong route.hom

theorem strong_identity (source : TwoCategory.{u,v,p,f,h}) :
    Strong (𝟙 source : source ⟶ source) :=
  AdjunctionTwoCategory.strong_identity source.val

theorem strong_composition {source middle target : TwoCategory.{u,v,p,f,h}}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (firstStrong : Strong first) (secondStrong : Strong second) :
    Strong (first ≫ second) :=
  AdjunctionTwoCategory.strong_composition first.hom second.hom firstStrong secondStrong

end Mettapedia.TypeTheory.HigherOrderDependentSigma
