import Mettapedia.TypeTheory.ContextualSmallMapConstructions
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFamilies

/-!
# Actual contextual covers retaining enumeration data

The local cover has every authored local fibre enumeration as a generator,
followed by an actual terminal context arrow. Its natural projection covers
the parameter family directly from pointwise small-fibre existence. Local
rows form a commuting natural triangle with small projection fibres. Their
old receipt values need not cover new arguments introduced by restriction.

The future cover retains enumeration data for every future of its generator.
The terminal arrow then reads the actual enumeration of the current fibre.
The literal pullback has uniformly authored small enumerations, and its
top map is covering whenever the parameter projection is covering. The
required future-data existence is stated separately from local existence.

Both generators can inhabit larger universes. No enumeration is selected
from a nonemptiness proof, no cover is asserted to have a chosen inverse,
and these constructions do not establish internal Collection or realignment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualEnumerationCovers

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualSmallMapConstructions
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafBaseChange

universe u v w
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B)

abbrev LocalGenerator := Σ point : D, Σ value : B.obj point,
  Enumeration.{u, v} (Fibre operation point value)

def localFamily : D ⥤ Type (max (u + 1) v w) where
  obj point := Σ generator : LocalGenerator operation, generator.1 ⟶ point
  map step := TypeCat.ofHom (fun receipt => ⟨receipt.1, receipt.2 ≫ step⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg (Sigma.mk receipt.1) (Category.comp_id receipt.2)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg (Sigma.mk receipt.1) (Category.assoc receipt.2 earlier later).symm

def localProjection : NaturalHom (localFamily operation) B where
  app _ receipt := B.map receipt.2 receipt.1.2.1
  naturality step receipt := (B.map_comp_apply receipt.2 step receipt.1.2.1).symm

def localSeed (point : D) (value : B.obj point)
    (enumeration : Enumeration.{u, v} (Fibre operation point value)) : (localFamily operation).obj point :=
  ⟨⟨point, value, enumeration⟩, 𝟙 point⟩

theorem localSeed_value (point : D) (value : B.obj point)
    (enumeration : Enumeration.{u, v} (Fibre operation point value)) :
    (localProjection operation).app point (localSeed operation point value enumeration) = value :=
  B.map_id_apply point value

/-- All local enumeration data are retained as possible generators. The
covering proof chooses none as a Type-valued function of the parameters. -/
theorem localProjection_surjective (small : SmallFibres operation) (point : D) :
    Function.Surjective ((localProjection operation).app point) := by
  intro value
  obtain ⟨enumeration⟩ := small point value
  exact ⟨localSeed operation point value enumeration, localSeed_value operation point value enumeration⟩

def localRows : D ⥤ Type (max (u + 1) v w) where
  obj point := Σ generator : LocalGenerator operation,
    generator.2.2.Carrier × (generator.1 ⟶ point)
  map step := TypeCat.ofHom (fun row => ⟨row.1, (row.2.1, row.2.2 ≫ step)⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro row
    exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl (Category.comp_id row.2.2)))
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro row
    exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl (Category.assoc row.2.2 earlier later).symm))

def localRowsProjection : NaturalHom (localRows operation) (localFamily operation) where
  app _ row := ⟨row.1, row.2.2⟩
  naturality _ _ := rfl

def localRowsReadout : NaturalHom (localRows operation) A where
  app _ row := A.map row.2.2 (row.1.2.2.value row.2.1).val
  naturality step row := (A.map_comp_apply row.2.2 step (row.1.2.2.value row.2.1).val).symm

theorem local_triangle : (localRowsReadout operation).comp operation =
    (localRowsProjection operation).comp (localProjection operation) := by
  apply NaturalHom.ext
  intro point row
  exact (operation.naturality row.2.2 (row.1.2.2.value row.2.1).val).symm.trans
    (congrArg (B.map row.2.2) (row.1.2.2.value row.2.1).property)

def localToPullback : NaturalHom (localRows operation) (pullback operation (localProjection operation)) :=
  pullbackPair operation (localProjection operation) (localRowsReadout operation) (localRowsProjection operation)
    (local_triangle operation)

def localRowsEnumeration (point : D) (receipt : (localFamily operation).obj point) :
    Enumeration.{u, max (u + 1) v w} (Fibre (localRowsProjection operation) point receipt) where
  Carrier := receipt.1.2.2.Carrier
  value code := ⟨⟨receipt.1, (code, receipt.2)⟩, rfl⟩
  covered := by
    rcases receipt with ⟨generator, arrow⟩
    rintro ⟨⟨other, code, otherArrow⟩, same⟩
    obtain ⟨generators, arrows⟩ := Sigma.mk.inj same
    cases generators
    have arrowsEq := eq_of_heq arrows
    cases arrowsEq
    exact ⟨code, Subtype.ext rfl⟩

theorem localRows_smallFibres : SmallFibres (localRowsProjection operation) :=
  fun point receipt => ⟨localRowsEnumeration operation point receipt⟩

theorem localSeed_original_fibre_covered (point : D) (value : B.obj point)
    (enumeration : Enumeration.{u, v} (Fibre operation point value))
    (argument : Fibre operation point value) :
    ∃ row : (localRows operation).obj point,
      (localRowsProjection operation).app point row = localSeed operation point value enumeration ∧
        (localRowsReadout operation).app point row = argument.val := by
  obtain ⟨code, same⟩ := enumeration.covered argument
  refine ⟨⟨⟨point, value, enumeration⟩, (code, 𝟙 point)⟩, rfl, ?_⟩
  exact (A.map_id_apply point (enumeration.value code).val).trans (congrArg Subtype.val same)

/-- Actual authored enumeration data for all future fibres of one parameter.
This is stronger input than pointwise nonemptiness of separate enumerations. -/
abbrev FutureEnumerations (point : D) (value : B.obj point) :=
  (future : Future.Objects point) →
    Enumeration.{u, v} (Fibre operation future.1 (B.map future.2 value))

abbrev FutureGenerator := Σ point : D, Σ value : B.obj point, FutureEnumerations operation point value

def futureFamily : D ⥤ Type (max (u + 1) v w) where
  obj point := Σ generator : FutureGenerator operation, generator.1 ⟶ point
  map step := TypeCat.ofHom (fun receipt => ⟨receipt.1, receipt.2 ≫ step⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg (Sigma.mk receipt.1) (Category.comp_id receipt.2)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg (Sigma.mk receipt.1) (Category.assoc receipt.2 earlier later).symm

def futureProjection : NaturalHom (futureFamily operation) B where
  app _ receipt := B.map receipt.2 receipt.1.2.1
  naturality step receipt := (B.map_comp_apply receipt.2 step receipt.1.2.1).symm

def futureSeed (point : D) (value : B.obj point) (enumerations : FutureEnumerations operation point value) :
    (futureFamily operation).obj point := ⟨⟨point, value, enumerations⟩, 𝟙 point⟩

theorem futureProjection_surjective
    (covered : ∀ point value, Nonempty (FutureEnumerations operation point value)) (point : D) :
    Function.Surjective ((futureProjection operation).app point) := by
  intro value
  obtain ⟨enumerations⟩ := covered point value
  exact ⟨futureSeed operation point value enumerations, B.map_id_apply point value⟩

def currentEnumeration (point : D) (receipt : (futureFamily operation).obj point) :
    Enumeration.{u, v} (Fibre operation point ((futureProjection operation).app point receipt)) :=
  receipt.1.2.2 ⟨point, receipt.2⟩

abbrev futurePullback := pullback operation (futureProjection operation)

def pulledEnumerations : UniformEnumerations (pullbackSecond operation (futureProjection operation)) :=
  fun point receipt => pullbackFibreEnumeration operation (futureProjection operation) point receipt
    (currentEnumeration operation point receipt)

theorem futurePullback_smallFibres : SmallFibres (pullbackSecond operation (futureProjection operation)) :=
  fun point receipt => ⟨pulledEnumerations operation point receipt⟩

theorem future_triangle :
    (pullbackFirst operation (futureProjection operation)).comp operation =
      (pullbackSecond operation (futureProjection operation)).comp (futureProjection operation) :=
  pullback_square operation (futureProjection operation)

/-- The literal pullback covers the original domain when the constructed
future-data parameter projection covers. No section is obtained. -/
theorem futureTop_surjective
    (covered : ∀ point value, Nonempty (FutureEnumerations operation point value)) (point : D) :
    Function.Surjective ((pullbackFirst operation (futureProjection operation)).app point) := by
  intro argument
  obtain ⟨receipt, same⟩ := futureProjection_surjective operation covered point (operation.app point argument)
  exact ⟨⟨(argument, receipt), same.symm⟩, rfl⟩

def fibrePredicate (point : D) (value : B.obj point) : CoveredFuturePowerFamilies.Predicate A point where
  holds argument := operation.app argument.1.1 argument.2 = B.map argument.1.2 value
  closed {first second} step available := by
    have triangle := congrArg (fun arrow => B.map arrow value) step.1.2
    exact (congrArg (operation.app second.1.1) step.2).symm.trans
      ((operation.naturality step.1.1 first.2).symm.trans
        ((congrArg (B.map step.1.1) available).trans
          ((B.map_comp_apply first.1.2 step.1.1 value).symm.trans triangle)))

def futurePowerEnumeration (point : D) (value : B.obj point)
    (enumerations : FutureEnumerations operation point value) :
    CoveredFuturePowerFamilies.Enumeration (fibrePredicate operation point value) where
  Carrier future := (enumerations future).Carrier
  value future code := ((enumerations future).value code).val
  covered future argument := by
    constructor
    · intro member
      obtain ⟨code, same⟩ := (enumerations future).covered ⟨argument, member⟩
      exact ⟨code, congrArg Subtype.val same⟩
    · rintro ⟨code, same⟩
      exact (congrArg (operation.app future.1) same).symm.trans ((enumerations future).value code).property

def futureEnumerationsOfPower (point : D) (value : B.obj point)
    (enumeration : CoveredFuturePowerFamilies.Enumeration (fibrePredicate operation point value)) :
    FutureEnumerations operation point value := fun future => {
  Carrier := enumeration.Carrier future
  value code := ⟨enumeration.value future code, (enumeration.covered future _).mpr ⟨code, rfl⟩⟩
  covered argument := by
    obtain ⟨code, same⟩ := (enumeration.covered future argument.val).mp argument.property
    exact ⟨code, Subtype.ext same⟩ }

theorem futureData_iff_coveredPower (point : D) (value : B.obj point) :
    Nonempty (FutureEnumerations operation point value) ↔
      Nonempty (CoveredFuturePowerFamilies.Enumeration (fibrePredicate operation point value)) :=
  ⟨fun ⟨enumerations⟩ => ⟨futurePowerEnumeration operation point value enumerations⟩,
    fun ⟨enumeration⟩ => ⟨futureEnumerationsOfPower operation point value enumeration⟩⟩

/-- The actual fibre relation has a natural covered-power classifier under
the exact future-cover condition. Local existential smallness is separate. -/
def fibreClassifier (covered : ∀ point value, Nonempty (FutureEnumerations operation point value)) :
    NaturalHom B (CoveredFuturePowerFamilies.family A) where
  app point value := ⟨fibrePredicate operation point value,
    (futureData_iff_coveredPower operation point value).mp (covered point value)⟩
  naturality step value := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro argument
    change operation.app argument.1.1 argument.2 = B.map (step ≫ argument.1.2) value ↔
      operation.app argument.1.1 argument.2 = B.map argument.1.2 (B.map step value)
    rw [B.map_comp_apply]

end Mettapedia.TypeTheory.ContextualEnumerationCovers
