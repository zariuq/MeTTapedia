import Mettapedia.TypeTheory.ContextualWitnessCover
import Mathlib.Data.Quot

/-!
# Constructed contextual kernel quotients

The context and arrows are small, while the argument functors may live in
independent wider universes. Each quotient identifies exactly the values
identified by a declared natural map. Restrictions map actual quotient
classes, and every compatible natural operation descends by quotient
elimination. No representative or inverse of a surjection is selected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualKernelQuotients

open CategoryTheory ContextualWitnessCover

universe u v w z
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B)

def kernel (point : D) : Setoid (A.obj point) where
  r first second := operation.app point first = operation.app point second
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem kernel_restriction {first second : D} (step : first ⟶ second)
    {left right : A.obj first} (same : (kernel operation first).r left right) :
    (kernel operation second).r (A.map step left) (A.map step right) :=
  (operation.naturality step left).symm.trans
    ((congrArg (B.map step) same).trans (operation.naturality step right))

def quotient : D ⥤ Type v where
  obj point := Quotient (kernel operation point)
  map {first second} step := TypeCat.ofHom
    (Quotient.map (sa := kernel operation first) (sb := kernel operation second)
      (A.map step) (fun {_ _} same => kernel_restriction operation step same))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    refine Quotient.inductionOn value fun argument => ?_
    exact congrArg (Quotient.mk (kernel operation point)) (A.map_id_apply point argument)
  map_comp {first _middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    refine Quotient.inductionOn value fun argument => ?_
    exact congrArg (Quotient.mk (kernel operation last))
      (A.map_comp_apply earlier later argument)

def projection : NaturalHom A (quotient operation) where
  app point := Quotient.mk (kernel operation point)
  naturality _ _ := rfl

theorem projection_restriction {first second : D} (step : first ⟶ second)
    (argument : A.obj first) :
    (quotient operation).map step ((projection operation).app first argument) =
      (projection operation).app second (A.map step argument) := rfl

theorem projection_surjective (point : D) : Function.Surjective ((projection operation).app point) := by
  intro value
  exact Quotient.inductionOn value fun argument => ⟨argument, rfl⟩

theorem projection_eq_iff (point : D) (first second : A.obj point) :
    (projection operation).app point first = (projection operation).app point second ↔
      operation.app point first = operation.app point second :=
  ⟨fun same => Quotient.exact same,
    fun same => Quotient.sound (s := kernel operation point) same⟩

def Respects {Z : D ⥤ Type z} (other : NaturalHom A Z) : Prop :=
  ∀ point {first second}, operation.app point first = operation.app point second →
    other.app point first = other.app point second

def descend {Z : D ⥤ Type z} (other : NaturalHom A Z) (compatible : Respects operation other) :
    NaturalHom (quotient operation) Z where
  app point := Quotient.lift (other.app point) (fun _ _ same => compatible point same)
  naturality {first second} step value := by
    refine Quotient.inductionOn value fun argument => ?_
    exact other.naturality step argument

theorem descend_beta {Z : D ⥤ Type z} (other : NaturalHom A Z)
    (compatible : Respects operation other) (point : D) (argument : A.obj point) :
    (descend operation other compatible).app point ((projection operation).app point argument) =
      other.app point argument := rfl

theorem descend_factorization {Z : D ⥤ Type z} (other : NaturalHom A Z)
    (compatible : Respects operation other) :
    (projection operation).comp (descend operation other compatible) = other := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem projection_respects {Z : D ⥤ Type z} (other : NaturalHom (quotient operation) Z) :
    Respects operation ((projection operation).comp other) := by
  intro point first second same
  exact congrArg (other.app point) (Quotient.sound (s := kernel operation point) same)

theorem descend_unique {Z : D ⥤ Type z} (other : NaturalHom A Z)
    (compatible : Respects operation other) (candidate : NaturalHom (quotient operation) Z)
    (factors : (projection operation).comp candidate = other) :
    candidate = descend operation other compatible := by
  apply NaturalHom.ext
  intro point value
  refine Quotient.inductionOn value fun argument => ?_
  exact congrArg (fun map : NaturalHom A Z => map.app point argument) factors

theorem projection_epi {Z : D ⥤ Type z} (first second : NaturalHom (quotient operation) Z)
    (same : (projection operation).comp first = (projection operation).comp second) : first = second := by
  apply NaturalHom.ext
  intro point value
  refine Quotient.inductionOn value fun argument => ?_
  exact congrArg (fun map : NaturalHom A Z => map.app point argument) same

def universalHomEquiv (Z : D ⥤ Type z) :
    NaturalHom (quotient operation) Z ≃ {other : NaturalHom A Z // Respects operation other} where
  toFun other := ⟨(projection operation).comp other, projection_respects operation other⟩
  invFun other := descend operation other.val other.property
  left_inv other := (descend_unique operation ((projection operation).comp other)
    (projection_respects operation other) other rfl).symm
  right_inv other := Subtype.ext (descend_factorization operation other.val other.property)

theorem descends_iff {Z : D ⥤ Type z} (other : NaturalHom A Z) :
    (∃ factor : NaturalHom (quotient operation) Z, (projection operation).comp factor = other) ↔
      Respects operation other := by
  constructor
  · rintro ⟨factor, rfl⟩
    exact projection_respects operation factor
  · intro compatible
    exact ⟨descend operation other compatible, descend_factorization operation other compatible⟩

def embedding : NaturalHom (quotient operation) B :=
  descend operation operation (fun _ _ _ same => same)

theorem factorization : (projection operation).comp (embedding operation) = operation :=
  descend_factorization operation operation (fun _ _ _ same => same)

theorem embedding_beta (point : D) (argument : A.obj point) :
    (embedding operation).app point ((projection operation).app point argument) =
      operation.app point argument := rfl

theorem embedding_injective (point : D) : Function.Injective ((embedding operation).app point) := by
  intro first second
  refine Quotient.inductionOn₂ first second fun left right same => ?_
  exact Quotient.sound (s := kernel operation point) same

theorem embedding_mono {Z : D ⥤ Type z} (first second : NaturalHom Z (quotient operation))
    (same : first.comp (embedding operation) = second.comp (embedding operation)) : first = second := by
  apply NaturalHom.ext
  intro point value
  exact embedding_injective operation point
    (congrArg (fun map : NaturalHom Z B => map.app point value) same)

theorem embedding_image (point : D) (value : B.obj point) :
    (∃ quotientValue, (embedding operation).app point quotientValue = value) ↔
      ∃ argument, operation.app point argument = value := by
  constructor
  · rintro ⟨quotientValue, same⟩
    exact Quotient.inductionOn quotientValue (fun argument same => ⟨argument, same⟩) same
  · rintro ⟨argument, same⟩
    exact ⟨(projection operation).app point argument, same⟩

theorem section_kernel_iff (first second : A.sections) :
    (projection operation).mapSection first = (projection operation).mapSection second ↔
      operation.mapSection first = operation.mapSection second := by
  constructor
  · intro same
    apply Subtype.ext
    funext point
    exact (projection_eq_iff operation point (first.val point) (second.val point)).mp
      (congrArg (fun term : (quotient operation).sections => term.val point) same)
  · intro same
    apply Subtype.ext
    funext point
    exact (projection_eq_iff operation point (first.val point) (second.val point)).mpr
      (congrArg (fun term : B.sections => term.val point) same)

theorem section_factorization (term : A.sections) :
    (embedding operation).mapSection ((projection operation).mapSection term) = operation.mapSection term := by
  apply Subtype.ext
  funext point
  exact embedding_beta operation point (term.val point)

def kernelPair : D ⥤ Type v where
  obj point := {pair : A.obj point × A.obj point // operation.app point pair.1 = operation.app point pair.2}
  map step := TypeCat.ofHom fun pair =>
    ⟨(A.map step pair.val.1, A.map step pair.val.2), kernel_restriction operation step pair.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro pair
    apply Subtype.ext
    exact Prod.ext (A.map_id_apply point pair.val.1) (A.map_id_apply point pair.val.2)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro pair
    apply Subtype.ext
    exact Prod.ext (A.map_comp_apply first second pair.val.1) (A.map_comp_apply first second pair.val.2)

def kernelFirst : NaturalHom (kernelPair operation) A where
  app _ pair := pair.val.1
  naturality _ _ := rfl

def kernelSecond : NaturalHom (kernelPair operation) A where
  app _ pair := pair.val.2
  naturality _ _ := rfl

theorem coequalizes : (kernelFirst operation).comp (projection operation) =
    (kernelSecond operation).comp (projection operation) := by
  apply NaturalHom.ext
  intro point pair
  exact Quotient.sound (s := kernel operation point) pair.property

theorem kernelPair_compatibility_iff {Z : D ⥤ Type z} (other : NaturalHom A Z) :
    (kernelFirst operation).comp other = (kernelSecond operation).comp other ↔ Respects operation other := by
  constructor
  · intro same point first second identified
    exact congrArg (fun map : NaturalHom (kernelPair operation) Z =>
      map.app point ⟨(first, second), identified⟩) same
  · intro compatible
    apply NaturalHom.ext
    intro point pair
    exact compatible point pair.property

/-- The projection is a genuine coequalizer of its constructed kernel pair,
expressed in cross-universe natural maps with actual factor data and uniqueness. -/
theorem coequalizer_universal {Z : D ⥤ Type z} (other : NaturalHom A Z)
    (equalized : (kernelFirst operation).comp other = (kernelSecond operation).comp other) :
    ∃! factor : NaturalHom (quotient operation) Z, (projection operation).comp factor = other := by
  let compatible := (kernelPair_compatibility_iff operation other).mp equalized
  refine ⟨descend operation other compatible, descend_factorization operation other compatible, ?_⟩
  intro candidate factors
  exact descend_unique operation other compatible candidate factors

end Mettapedia.TypeTheory.ContextualKernelQuotients
