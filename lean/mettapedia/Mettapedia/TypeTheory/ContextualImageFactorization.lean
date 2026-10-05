import Mettapedia.TypeTheory.ContextualKernelQuotients

/-!
# Natural images, pullbacks and explicit small-cover transport

Kernel quotients supply the regular image: their natural embedding has
exactly the original map's range, and factors through every other injective
factorization by constructed quotient elimination. The literal range
subfunctor retains existence of original occurrences, without selecting one.

Actual pullback fibres are explicitly equivalent to the original map's
corresponding fibres. Small enumeration data transport along that inverse,
so this precise fibre-cover predicate is pullback stable. No uniform cover,
section or Collection capability is selected from pointwise existence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualImageFactorization

open CategoryTheory ContextualWitnessCover ContextualKernelQuotients

universe u v w z t
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B)

def image : D ⥤ Type w where
  obj point := {value : B.obj point // ∃ argument, operation.app point argument = value}
  map {first second} step := TypeCat.ofHom fun value =>
    ⟨B.map step value.val, by
      obtain ⟨argument, same⟩ := value.property
      exact ⟨A.map step argument, (operation.naturality step argument).symm.trans
        (congrArg (B.map step) same)⟩⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Subtype.ext (B.map_id_apply point value.val)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Subtype.ext (B.map_comp_apply first second value.val)

def imageProjection : NaturalHom A (image operation) where
  app point argument := ⟨operation.app point argument, ⟨argument, rfl⟩⟩
  naturality step argument := Subtype.ext (operation.naturality step argument)

def imageInclusion : NaturalHom (image operation) B where
  app _ := Subtype.val
  naturality _ _ := rfl

theorem imageProjection_surjective (point : D) :
    Function.Surjective ((imageProjection operation).app point) := by
  intro value
  obtain ⟨argument, same⟩ := value.property
  exact ⟨argument, Subtype.ext same⟩

theorem imageInclusion_injective (point : D) :
    Function.Injective ((imageInclusion operation).app point) :=
  fun _ _ same => Subtype.ext same

theorem image_factorization : (imageProjection operation).comp (imageInclusion operation) = operation := by
  apply NaturalHom.ext
  intro _ _
  rfl

def quotientToImage : NaturalHom (quotient operation) (image operation) where
  app point value := ⟨(embedding operation).app point value,
    (embedding_image operation point _).mp ⟨value, rfl⟩⟩
  naturality step value := Subtype.ext ((embedding operation).naturality step value)

theorem quotientToImage_injective (point : D) :
    Function.Injective ((quotientToImage operation).app point) := by
  intro first second same
  exact embedding_injective operation point (congrArg Subtype.val same)

theorem quotientToImage_surjective (point : D) :
    Function.Surjective ((quotientToImage operation).app point) := by
  intro value
  obtain ⟨argument, same⟩ := value.property
  exact ⟨(projection operation).app point argument, Subtype.ext same⟩

theorem quotient_image_square :
    (projection operation).comp (quotientToImage operation) = imageProjection operation := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem quotient_image_embedding :
    (quotientToImage operation).comp (imageInclusion operation) = embedding operation := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem monoCompatible {Z : D ⥤ Type z} (first : NaturalHom A Z) (second : NaturalHom Z B)
    (injective : ∀ point, Function.Injective (second.app point))
    (factors : first.comp second = operation) : Respects operation first := by
  intro point left right same
  apply injective point
  have leftSquare := congrArg (fun map : NaturalHom A B => map.app point left) factors
  have rightSquare := congrArg (fun map : NaturalHom A B => map.app point right) factors
  exact leftSquare.trans (same.trans rightSquare.symm)

def factorThroughMono {Z : D ⥤ Type z} (first : NaturalHom A Z) (second : NaturalHom Z B)
    (injective : ∀ point, Function.Injective (second.app point))
    (factors : first.comp second = operation) : NaturalHom (quotient operation) Z :=
  descend operation first (monoCompatible operation first second injective factors)

theorem factorThroughMono_projection {Z : D ⥤ Type z} (first : NaturalHom A Z)
    (second : NaturalHom Z B) (injective : ∀ point, Function.Injective (second.app point))
    (factors : first.comp second = operation) :
    (projection operation).comp (factorThroughMono operation first second injective factors) = first :=
  descend_factorization operation first _

theorem factorThroughMono_embedding {Z : D ⥤ Type z} (first : NaturalHom A Z)
    (second : NaturalHom Z B) (injective : ∀ point, Function.Injective (second.app point))
    (factors : first.comp second = operation) :
    (factorThroughMono operation first second injective factors).comp second = embedding operation := by
  apply NaturalHom.ext
  intro point value
  refine Quotient.inductionOn value fun argument => ?_
  exact congrArg (fun map : NaturalHom A B => map.app point argument) factors

theorem factorThroughMono_unique {Z : D ⥤ Type z} (first : NaturalHom A Z)
    (second : NaturalHom Z B) (injective : ∀ point, Function.Injective (second.app point))
    (factors : first.comp second = operation) (candidate : NaturalHom (quotient operation) Z)
    (over : candidate.comp second = embedding operation) :
    candidate = factorThroughMono operation first second injective factors := by
  apply NaturalHom.ext
  intro point value
  apply injective point
  exact (congrArg (fun map : NaturalHom (quotient operation) B => map.app point value) over).trans
    (congrArg (fun map : NaturalHom (quotient operation) B => map.app point value)
      (factorThroughMono_embedding operation first second injective factors)).symm

section BaseRestriction

variable {E : Type t} [Category.{t} E] (change : E ⥤ D)

def restrict (family : D ⥤ Type v) : E ⥤ Type v where
  obj point := family.obj (change.obj point)
  map step := family.map (change.map step)
  map_id point := by rw [change.map_id, family.map_id]
  map_comp first second := by rw [change.map_comp, family.map_comp]

def restrictHom : NaturalHom (restrict change A) (restrict change B) where
  app point := operation.app (change.obj point)
  naturality step value := operation.naturality (change.map step) value

theorem quotient_restriction : quotient (restrictHom operation change) = restrict change (quotient operation) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem projection_restriction_value (point : E) (argument : A.obj (change.obj point)) :
    (projection (restrictHom operation change)).app point argument =
      (projection operation).app (change.obj point) argument := rfl

theorem embedding_restriction_value (point : E)
    (value : (quotient (restrictHom operation change)).obj point) :
    (embedding (restrictHom operation change)).app point value =
      (embedding operation).app (change.obj point) value := rfl

theorem image_restriction : image (restrictHom operation change) = restrict change (image operation) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

end BaseRestriction

section Pullbacks

variable {Z : D ⥤ Type z} (change : NaturalHom Z B)

def pullback : D ⥤ Type (max v z) where
  obj point := {pair : A.obj point × Z.obj point // operation.app point pair.1 = change.app point pair.2}
  map step := TypeCat.ofHom fun pair =>
    ⟨(A.map step pair.val.1, Z.map step pair.val.2),
      (operation.naturality step pair.val.1).symm.trans
        ((congrArg (B.map step) pair.property).trans (change.naturality step pair.val.2))⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro pair
    exact Subtype.ext (Prod.ext (A.map_id_apply point pair.val.1) (Z.map_id_apply point pair.val.2))
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro pair
    exact Subtype.ext (Prod.ext (A.map_comp_apply first second pair.val.1)
      (Z.map_comp_apply first second pair.val.2))

def pullbackFirst : NaturalHom (pullback operation change) A where
  app _ pair := pair.val.1
  naturality _ _ := rfl

def pullbackSecond : NaturalHom (pullback operation change) Z where
  app _ pair := pair.val.2
  naturality _ _ := rfl

theorem pullback_square : (pullbackFirst operation change).comp operation =
    (pullbackSecond operation change).comp change := by
  apply NaturalHom.ext
  intro _ pair
  exact pair.property

def pullbackPair {R : D ⥤ Type t} (left : NaturalHom R A) (right : NaturalHom R Z)
    (square : left.comp operation = right.comp change) : NaturalHom R (pullback operation change) where
  app point value := ⟨(left.app point value, right.app point value),
    congrArg (fun map : NaturalHom R B => map.app point value) square⟩
  naturality step value := Subtype.ext (Prod.ext (left.naturality step value) (right.naturality step value))

theorem pullbackPair_first {R : D ⥤ Type t} (left : NaturalHom R A) (right : NaturalHom R Z)
    (square : left.comp operation = right.comp change) :
    (pullbackPair operation change left right square).comp (pullbackFirst operation change) = left := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem pullbackPair_second {R : D ⥤ Type t} (left : NaturalHom R A) (right : NaturalHom R Z)
    (square : left.comp operation = right.comp change) :
    (pullbackPair operation change left right square).comp (pullbackSecond operation change) = right := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem pullbackPair_unique {R : D ⥤ Type t} (left : NaturalHom R A) (right : NaturalHom R Z)
    (square : left.comp operation = right.comp change) (candidate : NaturalHom R (pullback operation change))
    (leftLaw : candidate.comp (pullbackFirst operation change) = left)
    (rightLaw : candidate.comp (pullbackSecond operation change) = right) :
    candidate = pullbackPair operation change left right square := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  exact Prod.ext (congrArg (fun map : NaturalHom R A => map.app point value) leftLaw)
    (congrArg (fun map : NaturalHom R Z => map.app point value) rightLaw)

abbrev Fibre (point : D) (value : B.obj point) :=
  {argument : A.obj point // operation.app point argument = value}

def pullbackFibreEquiv (point : D) (value : Z.obj point) :
    Fibre (pullbackSecond operation change) point value ≃ Fibre operation point (change.app point value) where
  toFun receipt := ⟨receipt.val.val.1,
    receipt.val.property.trans (congrArg (change.app point) receipt.property)⟩
  invFun receipt := ⟨⟨(receipt.val, value), receipt.property⟩, rfl⟩
  left_inv receipt := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl receipt.property.symm
  right_inv receipt := Subtype.ext rfl

theorem pullback_image_iff (point : D) (value : Z.obj point) :
    (∃ receipt, (pullbackSecond operation change).app point receipt = value) ↔
      ∃ argument, operation.app point argument = change.app point value := by
  constructor
  · rintro ⟨receipt, same⟩
    exact ⟨receipt.val.1, receipt.property.trans (congrArg (change.app point) same)⟩
  · rintro ⟨argument, same⟩
    exact ⟨⟨(argument, value), same⟩, rfl⟩

def imagePullbackForward : NaturalHom (image (pullbackSecond operation change))
    (pullback (imageInclusion operation) change) where
  app point value := ⟨(⟨change.app point value.val,
    (pullback_image_iff operation change point value.val).mp value.property⟩, value.val), rfl⟩
  naturality step value := Subtype.ext (Prod.ext (Subtype.ext (change.naturality step value.val)) rfl)

def imagePullbackBackward : NaturalHom (pullback (imageInclusion operation) change)
    (image (pullbackSecond operation change)) where
  app point value := ⟨value.val.2, by
    apply (pullback_image_iff operation change point value.val.2).mpr
    obtain ⟨argument, same⟩ := value.val.1.property
    exact ⟨argument, same.trans value.property⟩⟩
  naturality _ _ := Subtype.ext rfl

theorem imagePullback_left (point : D) (value : (image (pullbackSecond operation change)).obj point) :
    (imagePullbackBackward operation change).app point
      ((imagePullbackForward operation change).app point value) = value := Subtype.ext rfl

theorem imagePullback_right (point : D) (value : (pullback (imageInclusion operation) change).obj point) :
    (imagePullbackForward operation change).app point
      ((imagePullbackBackward operation change).app point value) = value :=
  Subtype.ext (Prod.ext (Subtype.ext value.property.symm) rfl)

/-- The actual image of the pullback is the pullback of the image, with
constructed natural inverse maps. No original occurrence is recovered. -/
def imagePullbackEquiv (point : D) : (image (pullbackSecond operation change)).obj point ≃
    (pullback (imageInclusion operation) change).obj point where
  toFun := (imagePullbackForward operation change).app point
  invFun := (imagePullbackBackward operation change).app point
  left_inv := imagePullback_left operation change point
  right_inv := imagePullback_right operation change point

theorem imagePullback_inclusion :
    (imagePullbackForward operation change).comp (pullbackSecond (imageInclusion operation) change) =
      imageInclusion (pullbackSecond operation change) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem pullback_surjective (surjective : ∀ point, Function.Surjective (operation.app point))
    (point : D) : Function.Surjective ((pullbackSecond operation change).app point) := by
  intro value
  exact (pullback_image_iff operation change point value).mpr (surjective point (change.app point value))

end Pullbacks

structure Enumeration (X : Type v) where
  Carrier : Type u
  value : Carrier → X
  covered : Function.Surjective value

namespace Enumeration

variable {X : Type v} {Y : Type w}

def transport (same : X ≃ Y) (enumeration : Enumeration.{u, v} X) : Enumeration.{u, w} Y where
  Carrier := enumeration.Carrier
  value code := same (enumeration.value code)
  covered value := by
    obtain ⟨code, represents⟩ := enumeration.covered (same.symm value)
    exact ⟨code, (congrArg same represents).trans (same.apply_symm_apply value)⟩

end Enumeration

def SmallFibres : Prop := ∀ point value, Nonempty (Enumeration.{u, v} (Fibre operation point value))

def pullbackFibreEnumeration {Z : D ⥤ Type z} (change : NaturalHom Z B) (point : D) (value : Z.obj point)
    (enumeration : Enumeration.{u, v} (Fibre operation point (change.app point value))) :
    Enumeration.{u, max v z} (Fibre (pullbackSecond operation change) point value) :=
  enumeration.transport (pullbackFibreEquiv operation change point value).symm

theorem pullbackFibreEnumeration_iff {Z : D ⥤ Type z} (change : NaturalHom Z B)
    (point : D) (value : Z.obj point) :
    Nonempty (Enumeration.{u, max v z} (Fibre (pullbackSecond operation change) point value)) ↔
      Nonempty (Enumeration.{u, v} (Fibre operation point (change.app point value))) :=
  ⟨fun ⟨enumeration⟩ => ⟨enumeration.transport (pullbackFibreEquiv operation change point value)⟩,
    fun ⟨enumeration⟩ => ⟨pullbackFibreEnumeration operation change point value enumeration⟩⟩

/-- Pullback stability is proved for this exact receipt-cover predicate.
It neither selects a uniform cover nor establishes other small-map axioms. -/
theorem smallFibres_pullback {Z : D ⥤ Type z} (change : NaturalHom Z B)
    (small : SmallFibres operation) : SmallFibres (pullbackSecond operation change) := by
  intro point value
  exact (pullbackFibreEnumeration_iff operation change point value).mpr (small point (change.app point value))

/-- In a commuting triangle with a pointwise-surjective first map, the
original fibre codes enumerate the second map's fibre by mapping each
authored receipt forward. Only the covering proof uses existence of an
original receipt; the enumeration function selects none. -/
def coveredFibreEnumeration {Z : D ⥤ Type z} (cover : NaturalHom A Z)
    (remaining : NaturalHom Z B) (square : cover.comp remaining = operation)
    (surjective : ∀ point, Function.Surjective (cover.app point))
    (point : D) (value : B.obj point)
    (enumeration : Enumeration.{u, v} (Fibre operation point value)) :
    Enumeration.{u, z} (Fibre remaining point value) where
  Carrier := enumeration.Carrier
  value code := ⟨cover.app point (enumeration.value code).val,
    (congrArg (fun map : NaturalHom A B => map.app point (enumeration.value code).val) square).trans
      (enumeration.value code).property⟩
  covered receipt := by
    obtain ⟨argument, represents⟩ := surjective point receipt.val
    let original : Fibre operation point value := ⟨argument,
      (congrArg (fun map : NaturalHom A B => map.app point argument) square).symm.trans
        ((congrArg (remaining.app point) represents).trans receipt.property)⟩
    obtain ⟨code, same⟩ := enumeration.covered original
    refine ⟨code, Subtype.ext ?_⟩
    exact (congrArg (fun entry : Fibre operation point value => cover.app point entry.val) same).trans
      represents

theorem coveredFibreEnumeration_value {Z : D ⥤ Type z} (cover : NaturalHom A Z)
    (remaining : NaturalHom Z B) (square : cover.comp remaining = operation)
    (surjective : ∀ point, Function.Surjective (cover.app point))
    (point : D) (value : B.obj point)
    (enumeration : Enumeration.{u, v} (Fibre operation point value)) (code : enumeration.Carrier) :
    ((coveredFibreEnumeration operation cover remaining square surjective point value enumeration).value code).val =
      cover.app point (enumeration.value code).val := rfl

/-- Descent through a cover for the precise fixed-bound receipt-cover
predicate. This is distinct from pullback stability. -/
theorem smallFibres_covered_quotient {Z : D ⥤ Type z} (cover : NaturalHom A Z)
    (remaining : NaturalHom Z B) (square : cover.comp remaining = operation)
    (surjective : ∀ point, Function.Surjective (cover.app point))
    (small : SmallFibres operation) : SmallFibres remaining := by
  intro point value
  obtain ⟨enumeration⟩ := small point value
  exact ⟨coveredFibreEnumeration operation cover remaining square surjective point value enumeration⟩

theorem smallFibres_quotient_embedding (small : SmallFibres operation) :
    SmallFibres (embedding operation) :=
  smallFibres_covered_quotient operation (projection operation) (embedding operation)
    (factorization operation) (projection_surjective operation) small

theorem smallFibres_imageInclusion (small : SmallFibres operation) :
    SmallFibres (imageInclusion operation) :=
  smallFibres_covered_quotient operation (imageProjection operation) (imageInclusion operation)
    (image_factorization operation) (imageProjection_surjective operation) small

structure SmallCover (family : D ⥤ Type v) where
  carrier : D ⥤ Type u
  map : NaturalHom carrier family
  covered : ∀ point, Function.Surjective (map.app point)

def quotientSmallCover (cover : SmallCover.{u, v} A) : SmallCover.{u, v} (quotient operation) where
  carrier := cover.carrier
  map := cover.map.comp (projection operation)
  covered point value := by
    refine Quotient.inductionOn value fun argument => ?_
    obtain ⟨code, same⟩ := cover.covered point argument
    exact ⟨code, congrArg ((projection operation).app point) same⟩

def imageSmallCover (cover : SmallCover.{u, v} A) : SmallCover.{u, w} (image operation) where
  carrier := cover.carrier
  map := cover.map.comp (imageProjection operation)
  covered point value := by
    obtain ⟨argument, same⟩ := value.property
    obtain ⟨code, represented⟩ := cover.covered point argument
    refine ⟨code, Subtype.ext ?_⟩
    exact (congrArg (operation.app point) represented).trans same

end Mettapedia.TypeTheory.ContextualImageFactorization
