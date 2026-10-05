import Mettapedia.TypeTheory.ContextualSmallFamilyNativeAdjunction

/-!
# Actual contextual slice maps with separate carrier universes

Slice maps are natural maps with their actual commuting projection
equation. Fibres retain the original source value. Taking total spaces
and reading those fibres have constructed inverse maps; no source value
is recovered by selecting a witness of surjectivity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualNaturalSlices

open CategoryTheory ContextualWitnessCover ContextualImageFactorization

universe u v w h k l

variable {D : Type u} [Category.{u} D]
variable {base : D ⥤ Type v} {X : D ⥤ Type h} {Y : D ⥤ Type k} {Z : D ⥤ Type l}

structure Map (first : NaturalHom X base) (second : NaturalHom Y base) where
  mapping : NaturalHom X Y
  square : ∀ point value, second.app point (mapping.app point value) = first.app point value

namespace Map

variable {first : NaturalHom X base} {second : NaturalHom Y base} {third : NaturalHom Z base}

theorem ext (left right : Map first second)
    (same : ∀ point value, left.mapping.app point value = right.mapping.app point value) : left = right := by
  have maps := NaturalHom.ext left.mapping right.mapping same
  cases left
  cases right
  cases maps
  rfl

def identity (first : NaturalHom X base) : Map first first where
  mapping := { app _ value := value, naturality _ _ := rfl }
  square _ _ := rfl

def comp (earlier : Map first second) (later : Map second third) : Map first third where
  mapping := earlier.mapping.comp later.mapping
  square point value := (later.square point (earlier.mapping.app point value)).trans
    (earlier.square point value)

theorem identity_comp (operation : Map first second) : (identity first).comp operation = operation := by
  apply ext
  intro _ _
  rfl

theorem comp_identity (operation : Map first second) : operation.comp (identity second) = operation := by
  apply ext
  intro _ _
  rfl

theorem assoc {T : D ⥤ Type w} {fourth : NaturalHom T base}
    (earlier : Map first second) (middle : Map second third) (later : Map third fourth) :
    (earlier.comp middle).comp later = earlier.comp (middle.comp later) := by
  apply ext
  intro _ _
  rfl

end Map

def fibreMap (operation : NaturalHom X base) {first second : base.Elements}
    (step : first ⟶ second) (receipt : Fibre operation first.1 first.2) :
    Fibre operation second.1 second.2 :=
  ⟨X.map step.1 receipt.val, (operation.naturality step.1 receipt.val).symm.trans
    ((congrArg (base.map step.1) receipt.property).trans step.2)⟩

def fibres (operation : NaturalHom X base) : base.Elements ⥤ Type h where
  obj point := Fibre operation point.1 point.2
  map step := TypeCat.ofHom (fibreMap operation step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro receipt
    apply Subtype.ext
    exact X.map_id_apply point.1 receipt.val
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro receipt
    apply Subtype.ext
    exact X.map_comp_apply first.1 second.1 receipt.val

theorem fibreReceipt_heq (operation : NaturalHom X base) {first second : base.Elements}
    (same : first = second) (left : Fibre operation first.1 first.2)
    (right : Fibre operation second.1 second.2) (values : HEq left.val right.val) : HEq left right := by
  cases same
  exact heq_of_eq (Subtype.ext (eq_of_heq values))

def familyValueCast (family : base.Elements ⥤ Type w) {first second : base.Elements}
    (same : first = second) (value : family.obj first) : family.obj second := by
  cases same
  exact value

theorem familyValueCast_heq (family : base.Elements ⥤ Type w) {first second : base.Elements}
    (same : first = second) (value : family.obj first) :
    HEq (familyValueCast family same value) value := by
  cases same
  rfl

def totalMap {first : base.Elements ⥤ Type w} {second : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom first second) :
    Map (ContextualSmallFamilyUniverse.projection first) (ContextualSmallFamilyUniverse.projection second) where
  mapping :=
    { app point receipt := ⟨receipt.1, operation.app ⟨point, receipt.1⟩ receipt.2⟩
      naturality {source target} step receipt := by
        change (⟨base.map step receipt.1,
          second.map (CategoryOfElements.homMk (F := base) _ _ step rfl)
            (operation.app ⟨source, receipt.1⟩ receipt.2)⟩ : ContextualSmallFamilyUniverse.TotalAt second target) =
          ⟨base.map step receipt.1,
            operation.app ⟨target, base.map step receipt.1⟩
              (first.map (CategoryOfElements.homMk (F := base) _ _ step rfl) receipt.2)⟩
        refine Sigma.ext rfl ?_
        exact heq_of_eq (operation.naturality
          (CategoryOfElements.homMk (F := base)
            ⟨source, receipt.1⟩ ⟨target, base.map step receipt.1⟩ step rfl) receipt.2) }
  square _ _ := rfl

def toTotal (operation : NaturalHom X base) (family : base.Elements ⥤ Type w)
    (body : WiderPresheafDependentFunctions.Hom (fibres operation) family) :
    Map operation (ContextualSmallFamilyUniverse.projection family) where
  mapping :=
    { app point value := ⟨operation.app point value, body.app ⟨point, operation.app point value⟩ ⟨value, rfl⟩⟩
      naturality {first second} step value := by
        change (⟨base.map step (operation.app first value),
          family.map (CategoryOfElements.homMk (F := base) _ _ step rfl)
            (body.app ⟨first, operation.app first value⟩ ⟨value, rfl⟩)⟩ :
            ContextualSmallFamilyUniverse.TotalAt family second) = _
        refine Sigma.ext (operation.naturality step value) ?_
        have target : (⟨second, base.map step (operation.app first value)⟩ : base.Elements) =
            ⟨second, operation.app second (X.map step value)⟩ :=
          Sigma.ext rfl (heq_of_eq (operation.naturality step value))
        have receipt : HEq
            (fibreMap operation (CategoryOfElements.homMk (F := base)
              ⟨first, operation.app first value⟩ ⟨second, base.map step (operation.app first value)⟩ step rfl)
              (⟨value, rfl⟩ : Fibre operation first (operation.app first value)))
            (⟨X.map step value, rfl⟩ : Fibre operation second (operation.app second (X.map step value))) := by
          exact fibreReceipt_heq operation target _ _ HEq.rfl
        have natural := body.naturality
          (CategoryOfElements.homMk (F := base)
            ⟨first, operation.app first value⟩ ⟨second, base.map step (operation.app first value)⟩ step rfl)
          (⟨value, rfl⟩ : Fibre operation first (operation.app first value))
        exact (heq_of_eq natural).trans
          (ContextualSmallFamilyNativeAdjunction.homApplication_heq body target
            (fibreMap operation (CategoryOfElements.homMk (F := base)
              ⟨first, operation.app first value⟩ ⟨second, base.map step (operation.app first value)⟩ step rfl)
              (⟨value, rfl⟩ : Fibre operation first (operation.app first value)))
            (⟨X.map step value, rfl⟩ : Fibre operation second (operation.app second (X.map step value))) receipt) }
  square _ _ := rfl

def fromTotal (operation : NaturalHom X base) (family : base.Elements ⥤ Type w)
    (body : Map operation (ContextualSmallFamilyUniverse.projection family)) :
    WiderPresheafDependentFunctions.Hom (fibres operation) family where
  app point receipt := by
    have same : (⟨point.1, (body.mapping.app point.1 receipt.val).1⟩ : base.Elements) = point :=
      Sigma.ext rfl (heq_of_eq ((body.square point.1 receipt.val).trans receipt.property))
    exact familyValueCast family same (body.mapping.app point.1 receipt.val).2
  naturality {first second} step receipt := by
    let source := body.mapping.app first.1 receipt.val
    let target := body.mapping.app second.1 (X.map step.1 receipt.val)
    have sourceEq : (⟨first.1, source.1⟩ : base.Elements) = first :=
      Sigma.ext rfl (heq_of_eq ((body.square first.1 receipt.val).trans receipt.property))
    have targetEq : (⟨second.1, base.map step.1 source.1⟩ : base.Elements) = second := by
      refine Sigma.ext rfl ?_
      exact heq_of_eq ((congrArg (base.map step.1)
        ((body.square first.1 receipt.val).trans receipt.property)).trans step.2)
    have valueNatural : HEq
        (family.map (CategoryOfElements.homMk (F := base)
          ⟨first.1, source.1⟩ ⟨second.1, base.map step.1 source.1⟩ step.1 rfl) source.2) target.2 := by
      exact (Sigma.mk.inj_iff.mp (body.mapping.naturality step.1 receipt.val)).2
    have compared := ContextualSmallFamilyUniverse.familyMap_heq family sourceEq targetEq
      (CategoryOfElements.homMk (F := base)
        ⟨first.1, source.1⟩ ⟨second.1, base.map step.1 source.1⟩ step.1 rfl) step
      (ContextualSmallFamilyUniverse.elementsArrow_heq sourceEq targetEq _ _ HEq.rfl)
      source.2 (familyValueCast family sourceEq source.2)
      (familyValueCast_heq family sourceEq source.2).symm
    have actualTarget : (⟨second.1, target.1⟩ : base.Elements) = second :=
      Sigma.ext rfl (heq_of_eq ((body.square second.1 (X.map step.1 receipt.val)).trans
        (fibreMap operation step receipt).property))
    exact eq_of_heq (compared.symm.trans
      (valueNatural.trans (familyValueCast_heq family actualTarget target.2).symm))

theorem from_toTotal (operation : NaturalHom X base) (family : base.Elements ⥤ Type w)
    (body : WiderPresheafDependentFunctions.Hom (fibres operation) family) :
    fromTotal operation family (toTotal operation family body) = body := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point receipt
  apply eq_of_heq
  have same : (⟨point.1, operation.app point.1 receipt.val⟩ : base.Elements) = point :=
    Sigma.ext rfl (heq_of_eq receipt.property)
  have receipts : HEq
      (⟨receipt.val, rfl⟩ : Fibre operation point.1 (operation.app point.1 receipt.val)) receipt
      := fibreReceipt_heq operation same _ _ HEq.rfl
  exact (familyValueCast_heq family same _).trans
    (ContextualSmallFamilyNativeAdjunction.homApplication_heq body same _ _ receipts)

theorem to_fromTotal (operation : NaturalHom X base) (family : base.Elements ⥤ Type w)
    (body : Map operation (ContextualSmallFamilyUniverse.projection family)) :
    toTotal operation family (fromTotal operation family body) = body := by
  apply Map.ext
  intro point value
  change (⟨operation.app point value,
    (fromTotal operation family body).app ⟨point, operation.app point value⟩ ⟨value, rfl⟩⟩ :
      ContextualSmallFamilyUniverse.TotalAt family point) = body.mapping.app point value
  refine Sigma.ext (body.square point value).symm ?_
  have same : (⟨point, (body.mapping.app point value).1⟩ : base.Elements) =
      ⟨point, operation.app point value⟩ := Sigma.ext rfl (heq_of_eq (body.square point value))
  exact familyValueCast_heq family same _

def totalHomEquiv (operation : NaturalHom X base) (family : base.Elements ⥤ Type w) :
    WiderPresheafDependentFunctions.Hom (fibres operation) family ≃
      Map operation (ContextualSmallFamilyUniverse.projection family) where
  toFun := toTotal operation family
  invFun := fromTotal operation family
  left_inv := from_toTotal operation family
  right_inv := to_fromTotal operation family

def mapFibres {first : NaturalHom X base} {second : NaturalHom Y base}
    (mapping : Map first second) : WiderPresheafDependentFunctions.Hom (fibres first) (fibres second) where
  app point receipt := ⟨mapping.mapping.app point.1 receipt.val,
    (mapping.square point.1 receipt.val).trans receipt.property⟩
  naturality step receipt := Subtype.ext (mapping.mapping.naturality step.1 receipt.val)

theorem fromTotal_natural_source (first : NaturalHom X base) (second : NaturalHom Y base)
    (family : base.Elements ⥤ Type w) (earlier : Map first second)
    (body : Map second (ContextualSmallFamilyUniverse.projection family)) :
    fromTotal first family (earlier.comp body) =
      (mapFibres earlier).comp (fromTotal second family body) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point receipt
  apply eq_of_heq
  exact (familyValueCast_heq family _ _).trans (familyValueCast_heq family _ _).symm

def pullbackMap {first : NaturalHom X base} {second : NaturalHom Y base}
    (mapping : Map first second) {T : D ⥤ Type w} (change : NaturalHom T base) :
    Map (pullbackSecond first change) (pullbackSecond second change) where
  mapping :=
    { app point pair := ⟨(mapping.mapping.app point pair.val.1, pair.val.2),
        (mapping.square point pair.val.1).trans pair.property⟩
      naturality step pair := Subtype.ext (Prod.ext
        (mapping.mapping.naturality step pair.val.1) rfl) }
  square _ _ := rfl

theorem pullbackMap_value {first : NaturalHom X base} {second : NaturalHom Y base}
    (mapping : Map first second) {T : D ⥤ Type w} (change : NaturalHom T base)
    (point : D) (pair : (pullback first change).obj point) :
    ((pullbackMap mapping change).mapping.app point pair).val =
      (mapping.mapping.app point pair.val.1, pair.val.2) := rfl

theorem pullbackMap_identity (first : NaturalHom X base) {T : D ⥤ Type w} (change : NaturalHom T base) :
    pullbackMap (Map.identity first) change = Map.identity (pullbackSecond first change) := by
  apply Map.ext
  intro _ _
  rfl

theorem pullbackMap_comp {first : NaturalHom X base} {second : NaturalHom Y base}
    {third : NaturalHom Z base} (earlier : Map first second) (later : Map second third)
    {T : D ⥤ Type w} (change : NaturalHom T base) :
    pullbackMap (earlier.comp later) change =
      (pullbackMap earlier change).comp (pullbackMap later change) := by
  apply Map.ext
  intro _ _
  rfl

def pullbackFibreForward (operation : NaturalHom X base) (change : NaturalHom Y base) :
    WiderPresheafDependentFunctions.Hom (fibres (pullbackSecond operation change))
      (WiderPresheafDependentFunctions.restrict
        (ContextualSmallFamilyUniverse.elementMap change) (fibres operation)) where
  app point := pullbackFibreEquiv operation change point.1 point.2
  naturality _ _ := Subtype.ext rfl

def pullbackFibreBackward (operation : NaturalHom X base) (change : NaturalHom Y base) :
    WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.restrict
        (ContextualSmallFamilyUniverse.elementMap change) (fibres operation))
      (fibres (pullbackSecond operation change)) where
  app point receipt := ⟨⟨(receipt.val, point.2), receipt.property⟩, rfl⟩
  naturality step _ := Subtype.ext (Subtype.ext (Prod.ext rfl step.2))

theorem pullback_fibre_left (operation : NaturalHom X base) (change : NaturalHom Y base) :
    (pullbackFibreForward operation change).comp (pullbackFibreBackward operation change) =
      WiderPresheafDependentFunctions.Hom.identity (fibres (pullbackSecond operation change)) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point receipt
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext rfl receipt.property.symm

theorem pullback_fibre_right (operation : NaturalHom X base) (change : NaturalHom Y base) :
    (pullbackFibreBackward operation change).comp (pullbackFibreForward operation change) =
      WiderPresheafDependentFunctions.Hom.identity
        (WiderPresheafDependentFunctions.restrict
          (ContextualSmallFamilyUniverse.elementMap change) (fibres operation)) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point receipt
  exact Subtype.ext rfl

theorem pullbackFibreForward_value (operation : NaturalHom X base) (change : NaturalHom Y base)
    (point : Y.Elements) (receipt : (fibres (pullbackSecond operation change)).obj point) :
    ((pullbackFibreForward operation change).app point receipt).val = receipt.val.val.1 := rfl

theorem pullbackFibreBackward_value (operation : NaturalHom X base) (change : NaturalHom Y base)
    (point : Y.Elements) (receipt :
      (WiderPresheafDependentFunctions.restrict
        (ContextualSmallFamilyUniverse.elementMap change) (fibres operation)).obj point) :
    ((pullbackFibreBackward operation change).app point receipt).val.val = (receipt.val, point.2) := rfl

end Mettapedia.TypeTheory.ContextualNaturalSlices
