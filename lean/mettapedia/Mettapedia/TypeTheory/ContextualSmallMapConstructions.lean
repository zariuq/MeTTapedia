import Mettapedia.TypeTheory.ContextualImageFactorization

/-!
# Constructed fixed-bound contextual fibre operations

The small-fibre predicate uses actual surjective small receipt carriers,
which can have duplicates. Identities and binary coproducts have constructed
enumerations, even when their functor fibres inhabit larger universes.
Composition constructs a dependent sum of an outer receipt and a receipt
from the authored enumeration of its actual inner fibre.

The composition construction takes enumeration data for the inner fibres.
Pointwise existence is not used to select that function. The optional host
comparison is kept in a separate module. These finite constructions do not
assert all small-map axioms or internal Collection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallMapConstructions

open CategoryTheory ContextualWitnessCover ContextualImageFactorization

universe u v w z t s
variable {D : Type u} [Category.{u} D]

def identity (A : D ⥤ Type v) : NaturalHom A A where
  app _ := id
  naturality _ _ := rfl

def identityEnumeration (A : D ⥤ Type v) (point : D) (value : A.obj point) :
    Enumeration.{u, v} (Fibre (identity A) point value) where
  Carrier := PUnit.{u + 1}
  value _ := ⟨value, rfl⟩
  covered receipt := ⟨PUnit.unit, Subtype.ext receipt.property.symm⟩

theorem identity_smallFibres (A : D ⥤ Type v) : SmallFibres (identity A) :=
  fun point value => ⟨identityEnumeration A point value⟩

abbrev UniformEnumerations {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B) :=
  ∀ point value, Enumeration.{u, v} (Fibre operation point value)

variable {A : D ⥤ Type v} {B : D ⥤ Type w} {C : D ⥤ Type z}
variable (first : NaturalHom A B) (second : NaturalHom B C)

/-- The inner enumeration is authored at the actual value represented by
each outer receipt. No inverse of either receipt map is used. -/
def compositionEnumeration (point : D) (value : C.obj point)
    (outer : Enumeration.{u, w} (Fibre second point value))
    (inner : ∀ middle, Enumeration.{u, v} (Fibre first point middle)) :
    Enumeration.{u, v} (Fibre (first.comp second) point value) where
  Carrier := Σ outerCode : outer.Carrier, (inner (outer.value outerCode).val).Carrier
  value code := ⟨((inner (outer.value code.1).val).value code.2).val,
    (congrArg (second.app point) ((inner (outer.value code.1).val).value code.2).property).trans
      (outer.value code.1).property⟩
  covered receipt := by
    let middle : Fibre second point value := ⟨first.app point receipt.val, receipt.property⟩
    obtain ⟨outerCode, same⟩ := outer.covered middle
    have baseEq : (outer.value outerCode).val = first.app point receipt.val := congrArg Subtype.val same
    let original : Fibre first point (outer.value outerCode).val := ⟨receipt.val, baseEq.symm⟩
    obtain ⟨innerCode, represented⟩ := (inner (outer.value outerCode).val).covered original
    have valueEq : ((inner (outer.value outerCode).val).value innerCode).val = receipt.val :=
      congrArg (fun entry : Fibre first point (outer.value outerCode).val => entry.val) represented
    exact ⟨⟨outerCode, innerCode⟩, Subtype.ext valueEq⟩

theorem compositionEnumeration_value (point : D) (value : C.obj point)
    (outer : Enumeration.{u, w} (Fibre second point value))
    (inner : ∀ middle, Enumeration.{u, v} (Fibre first point middle))
    (code : (compositionEnumeration first second point value outer inner).Carrier) :
    ((compositionEnumeration first second point value outer inner).value code).val =
      ((inner (outer.value code.1).val).value code.2).val := rfl

def composeEnumerations (inner : UniformEnumerations first) (outer : UniformEnumerations second) :
    UniformEnumerations (first.comp second) :=
  fun point value => compositionEnumeration first second point value (outer point value) (inner point)

/-- Constructive composition uses inner enumeration data and only
propositional existence of the one required outer enumeration. -/
theorem smallFibres_compose_of_enumerations (inner : UniformEnumerations first)
    (outer : SmallFibres second) : SmallFibres (first.comp second) := by
  intro point value
  obtain ⟨enumeration⟩ := outer point value
  exact ⟨compositionEnumeration first second point value enumeration (inner point)⟩

def coproduct (A : D ⥤ Type v) (X : D ⥤ Type t) : D ⥤ Type (max v t) where
  obj point := A.obj point ⊕ X.obj point
  map step := TypeCat.ofHom (Sum.map (A.map step) (X.map step))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    cases value with
    | inl value => exact congrArg Sum.inl (A.map_id_apply point value)
    | inr value => exact congrArg Sum.inr (X.map_id_apply point value)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    cases value with
    | inl value => exact congrArg Sum.inl (A.map_comp_apply earlier later value)
    | inr value => exact congrArg Sum.inr (X.map_comp_apply earlier later value)

def leftInclusion (A : D ⥤ Type v) (X : D ⥤ Type t) : NaturalHom A (coproduct A X) where
  app _ := Sum.inl
  naturality _ _ := rfl

def rightInclusion (A : D ⥤ Type v) (X : D ⥤ Type t) : NaturalHom X (coproduct A X) where
  app _ := Sum.inr
  naturality _ _ := rfl

variable {X : D ⥤ Type t} {Y : D ⥤ Type s}

def coproductMap (first : NaturalHom A B) (second : NaturalHom X Y) :
    NaturalHom (coproduct A X) (coproduct B Y) where
  app point := Sum.map (first.app point) (second.app point)
  naturality step value := by
    cases value with
    | inl value => exact congrArg Sum.inl (first.naturality step value)
    | inr value => exact congrArg Sum.inr (second.naturality step value)

def leftFibreEquiv (first : NaturalHom A B) (second : NaturalHom X Y) (point : D) (value : B.obj point) :
    Fibre first point value ≃ Fibre (coproductMap first second) point (Sum.inl value) where
  toFun receipt := ⟨Sum.inl receipt.val, congrArg Sum.inl receipt.property⟩
  invFun := by
    rintro ⟨argument, same⟩
    cases argument with
    | inl argument => exact ⟨argument, Sum.inl.inj same⟩
    | inr argument =>
        change Sum.inr (second.app point argument) = Sum.inl value at same
        cases same
  left_inv _ := Subtype.ext rfl
  right_inv := by
    rintro ⟨argument, same⟩
    cases argument with
    | inl argument => exact Subtype.ext rfl
    | inr argument =>
        change Sum.inr (second.app point argument) = Sum.inl value at same
        cases same

def rightFibreEquiv (first : NaturalHom A B) (second : NaturalHom X Y) (point : D) (value : Y.obj point) :
    Fibre second point value ≃ Fibre (coproductMap first second) point (Sum.inr value) where
  toFun receipt := ⟨Sum.inr receipt.val, congrArg Sum.inr receipt.property⟩
  invFun := by
    rintro ⟨argument, same⟩
    cases argument with
    | inl argument =>
        change Sum.inl (first.app point argument) = Sum.inr value at same
        cases same
    | inr argument => exact ⟨argument, Sum.inr.inj same⟩
  left_inv _ := Subtype.ext rfl
  right_inv := by
    rintro ⟨argument, same⟩
    cases argument with
    | inl argument =>
        change Sum.inl (first.app point argument) = Sum.inr value at same
        cases same
    | inr argument => exact Subtype.ext rfl

def coproductEnumerations (first : NaturalHom A B) (second : NaturalHom X Y)
    (left : UniformEnumerations first) (right : UniformEnumerations second) :
    UniformEnumerations (coproductMap first second) :=
  fun point value => match value with
    | .inl value => (left point value).transport (leftFibreEquiv first second point value)
    | .inr value => (right point value).transport (rightFibreEquiv first second point value)

theorem smallFibres_coproduct (first : NaturalHom A B) (second : NaturalHom X Y)
    (left : SmallFibres first) (right : SmallFibres second) : SmallFibres (coproductMap first second) := by
  intro point value
  cases value with
  | inl value =>
      obtain ⟨enumeration⟩ := left point value
      exact ⟨enumeration.transport (leftFibreEquiv first second point value)⟩
  | inr value =>
      obtain ⟨enumeration⟩ := right point value
      exact ⟨enumeration.transport (rightFibreEquiv first second point value)⟩

end Mettapedia.TypeTheory.ContextualSmallMapConstructions
