import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers

/-!
# Coherent small maps with retained fibre decoders

A map carries an actual small displayed family and natural inverse fibre
decoders. The identity, composite and parameter pullback data are constructed
from those decoders. Pointwise existence of small receipt enumerations is a
different predicate: no coherent family is selected from that existence.

The cover class used here is pointwise surjectivity. Pullbacks and composition
preserve that class. Coherent decoding descends through an authored natural
splitting; unrestricted descent of coherent presentations is not asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCoherentSmallMaps

open CategoryTheory ContextualWitnessCover ContextualImageFactorization

universe u v w z t
variable {D : Type u} [Category.{u} D]
variable {X : D ⥤ Type v} {A : D ⥤ Type w}

abbrev Cover (operation : NaturalHom X A) : Prop :=
  ∀ point, Function.Surjective (operation.app point)

theorem cover_identity (A : D ⥤ Type w) : Cover (ContextualSmallMapConstructions.identity A) :=
  fun _ value => ⟨value, rfl⟩

theorem cover_comp {B : D ⥤ Type z} (first : NaturalHom X A) (second : NaturalHom A B)
    (inner : Cover first) (outer : Cover second) : Cover (first.comp second) := by
  intro point value
  obtain ⟨middle, middleLaw⟩ := outer point value
  obtain ⟨argument, argumentLaw⟩ := inner point middle
  exact ⟨argument, (congrArg (second.app point) argumentLaw).trans middleLaw⟩

theorem cover_pullback {B : D ⥤ Type z} (operation : NaturalHom X A)
    (change : NaturalHom B A) (covered : Cover operation) :
    Cover (pullbackSecond operation change) := pullback_surjective operation change covered

theorem cover_right_cancel {B : D ⥤ Type z} (operation : NaturalHom X A)
    (covered : Cover operation) (first second : NaturalHom A B)
    (same : operation.comp first = operation.comp second) : first = second := by
  apply NaturalHom.ext
  intro point value
  obtain ⟨argument, represents⟩ := covered point value
  exact (congrArg (first.app point) represents).symm.trans
    ((congrArg (fun map : NaturalHom X B => map.app point argument) same).trans
      (congrArg (second.app point) represents))

def fibreMap (operation : NaturalHom X A) {first second : A.Elements}
    (step : first ⟶ second) (receipt : Fibre operation first.1 first.2) :
    Fibre operation second.1 second.2 :=
  ⟨X.map step.1 receipt.val,
    (operation.naturality step.1 receipt.val).symm.trans
      ((congrArg (A.map step.1) receipt.property).trans step.2)⟩

theorem fibreMap_id (operation : NaturalHom X A) (point : A.Elements)
    (receipt : Fibre operation point.1 point.2) : fibreMap operation (𝟙 point) receipt = receipt := by
  apply Subtype.ext
  change X.map (𝟙 point.1) receipt.val = receipt.val
  exact X.map_id_apply point.1 receipt.val

theorem fibreMap_comp (operation : NaturalHom X A) {first middle last : A.Elements}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (receipt : Fibre operation first.1 first.2) :
    fibreMap operation (earlier ≫ later) receipt =
      fibreMap operation later (fibreMap operation earlier receipt) := by
  apply Subtype.ext
  change X.map (earlier.1 ≫ later.1) receipt.val = X.map later.1 (X.map earlier.1 receipt.val)
  exact X.map_comp_apply earlier.1 later.1 receipt.val

theorem fibreReceipt_heq (operation : NaturalHom X A) {first second : A.Elements}
    (same : first = second) (left : Fibre operation first.1 first.2)
    (right : Fibre operation second.1 second.2) (values : HEq left.val right.val) : HEq left right := by
  cases same
  exact heq_of_eq (Subtype.ext (eq_of_heq values))

theorem inverseDecoder_heq (operation : NaturalHom X A) (carrier : A.Elements → Type u)
    (decoder : ∀ point : A.Elements, carrier point ≃ Fibre operation point.1 point.2)
    {first second : A.Elements} (same : first = second)
    (left : Fibre operation first.1 first.2) (right : Fibre operation second.1 second.2)
    (values : HEq left right) : HEq ((decoder first).symm left) ((decoder second).symm right) := by
  cases same
  cases eq_of_heq values
  rfl

/-- The fields are presentation data for the original map, rather than a
covering-square or Collection existence assumption. -/
structure Data (operation : NaturalHom X A) where
  family : A.Elements ⥤ Type u
  decoder : ∀ point : A.Elements, family.obj point ≃ Fibre operation point.1 point.2
  naturality : ∀ {first second : A.Elements} (step : first ⟶ second) (term : family.obj first),
    fibreMap operation step (decoder first term) = decoder second (family.map step term)

namespace Data

variable {operation : NaturalHom X A} (model : Data operation)

def enumeration (point : D) (value : A.obj point) : Enumeration.{u, v} (Fibre operation point value) where
  Carrier := model.family.obj ⟨point, value⟩
  value := model.decoder ⟨point, value⟩
  covered := (model.decoder ⟨point, value⟩).surjective

include model in
theorem smallFibres : SmallFibres operation := fun point value => ⟨enumeration model point value⟩

def futureEnumerations (point : D) (value : A.obj point) :
    ContextualEnumerationCovers.FutureEnumerations operation point value :=
  fun future => enumeration model future.1 (A.map future.2 value)

def forward : NaturalHom (ContextualSmallFamilyUniverse.total model.family) X where
  app point term := (model.decoder ⟨point, term.1⟩ term.2).val
  naturality step term := congrArg Subtype.val
    (model.naturality (CategoryOfElements.homMk (F := A)
      ⟨_, term.1⟩ ⟨_, A.map step term.1⟩ step rfl) term.2)

def backwardValue (point : D) (argument : X.obj point) :
    (ContextualSmallFamilyUniverse.total model.family).obj point :=
  ⟨operation.app point argument,
    (model.decoder (⟨point, operation.app point argument⟩ : A.Elements)).symm
      (⟨argument, rfl⟩ : Fibre operation point (operation.app point argument))⟩

theorem forward_backward_value (point : D)
    (term : (ContextualSmallFamilyUniverse.total model.family).obj point) :
    model.backwardValue point (model.forward.app point term) = term := by
  rcases term with ⟨parameter, term⟩
  have parameterLaw := (model.decoder ⟨point, parameter⟩ term).property
  apply Sigma.ext parameterLaw
  have target : (⟨point, operation.app point (model.decoder ⟨point, parameter⟩ term).val⟩ : A.Elements) =
      ⟨point, parameter⟩ := congrArg (fun value => (⟨point, value⟩ : A.Elements)) parameterLaw
  have receiptLaw : HEq
      ((model.decoder ⟨point, operation.app point (model.decoder ⟨point, parameter⟩ term).val⟩).symm
        ⟨(model.decoder ⟨point, parameter⟩ term).val, rfl⟩)
      ((model.decoder ⟨point, parameter⟩).symm (model.decoder ⟨point, parameter⟩ term)) :=
    inverseDecoder_heq operation model.family.obj model.decoder target _ _
      (fibreReceipt_heq operation target _ _ HEq.rfl)
  exact receiptLaw.trans (heq_of_eq ((model.decoder _).symm_apply_apply term))

theorem backward_forward_value (point : D) (argument : X.obj point) :
    model.forward.app point (model.backwardValue point argument) = argument :=
  congrArg Subtype.val ((model.decoder (⟨point, operation.app point argument⟩ : A.Elements)).apply_symm_apply
    (⟨argument, rfl⟩ : Fibre operation point (operation.app point argument)))

theorem forward_injective (point : D) : Function.Injective (model.forward.app point) := by
  intro first second same
  exact (model.forward_backward_value point first).symm.trans
    ((congrArg (model.backwardValue point) same).trans (model.forward_backward_value point second))

def backward : NaturalHom X (ContextualSmallFamilyUniverse.total model.family) where
  app := model.backwardValue
  naturality step argument := by
    apply model.forward_injective
    exact ((model.forward.naturality step (model.backwardValue _ argument)).symm.trans
      (congrArg (X.map step) (model.backward_forward_value _ argument))).trans
        (model.backward_forward_value _ (X.map step argument)).symm

theorem forward_backward : model.forward.comp model.backward =
    ContextualSmallMapConstructions.identity (ContextualSmallFamilyUniverse.total model.family) := by
  apply NaturalHom.ext
  exact model.forward_backward_value

theorem backward_forward : model.backward.comp model.forward =
    ContextualSmallMapConstructions.identity X := by
  apply NaturalHom.ext
  exact model.backward_forward_value

theorem forward_parameter : model.forward.comp operation =
    ContextualSmallFamilyUniverse.projection model.family := by
  apply NaturalHom.ext
  rintro point ⟨parameter, term⟩
  exact (model.decoder ⟨point, parameter⟩ term).property

def sectionEquiv : (ContextualSmallFamilyUniverse.total model.family).sections ≃ X.sections where
  toFun := model.forward.mapSection
  invFun := model.backward.mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact model.forward_backward_value point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact model.backward_forward_value point (term.val point)

def classifier : NaturalHom A ContextualSmallFamilyUniverse.universeFamily :=
  ContextualSmallFamilyUniverse.classifier model.family

theorem decoded_classifier : ContextualSmallFamilyUniverse.decodedFamily model.classifier = model.family :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq model.family

end Data

/-- Explicit fibre equivalences determine a coherent displayed action by
decode, transport the actual argument, and encode. There is no selection
from a propositionally surjective map. -/
def ofEquivs (operation : NaturalHom X A) (carrier : A.Elements → Type u)
    (decoder : ∀ point : A.Elements, carrier point ≃ Fibre operation point.1 point.2) : Data operation where
  family :=
    { obj := carrier
      map := fun {first second} step => TypeCat.ofHom fun term =>
        (decoder second).symm (fibreMap operation step (decoder first term))
      map_id := by
        intro point
        apply ConcreteCategory.hom_ext
        intro term
        exact (congrArg (decoder point).symm (fibreMap_id operation point (decoder point term))).trans
          ((decoder point).symm_apply_apply term)
      map_comp := by
        intro first middle last earlier later
        apply ConcreteCategory.hom_ext
        intro term
        apply (decoder last).injective
        exact ((decoder last).apply_symm_apply _).trans
          ((fibreMap_comp operation earlier later (decoder first term)).trans
            ((congrArg (fibreMap operation later) ((decoder middle).apply_symm_apply _).symm).trans
              ((decoder last).apply_symm_apply _).symm)) }
  decoder := decoder
  naturality step term := ((decoder _).apply_symm_apply _).symm

def identityData (A : D ⥤ Type w) : Data (ContextualSmallMapConstructions.identity A) :=
  ofEquivs _ (fun _ => PUnit.{u + 1}) fun point =>
    { toFun := fun _ => ⟨point.2, rfl⟩
      invFun := fun _ => PUnit.unit
      left_inv := fun term => by cases term; rfl
      right_inv := fun receipt => Subtype.ext receipt.property.symm }

def projectionFibreEquiv (family : A.Elements ⥤ Type u) (point : A.Elements) :
    family.obj point ≃ Fibre (ContextualSmallFamilyUniverse.projection family) point.1 point.2 where
  toFun term := ⟨⟨point.2, term⟩, rfl⟩
  invFun receipt := cast (congrArg (fun value => family.obj (⟨point.1, value⟩ : A.Elements))
    receipt.property) receipt.val.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨value, term⟩, same⟩
    change value = point.2 at same
    cases same
    rfl

def projectionData (family : A.Elements ⥤ Type u) :
    Data (ContextualSmallFamilyUniverse.projection family) where
  family := family
  decoder := projectionFibreEquiv family
  naturality := by
    rintro ⟨first, value⟩ ⟨second, nextValue⟩ ⟨step, follows⟩ term
    change first ⟶ second at step
    change A.map step value = nextValue at follows
    subst nextValue
    exact Subtype.ext rfl

section Composition

variable {B : D ⥤ Type z} (first : NaturalHom X A) (second : NaturalHom A B)

def compositeFibreEquiv (point : D) (value : B.obj point) :
    (Σ middle : Fibre second point value, Fibre first point middle.val) ≃
      Fibre (first.comp second) point value where
  toFun term := ⟨term.2.val, (congrArg (second.app point) term.2.property).trans term.1.property⟩
  invFun term := ⟨⟨first.app point term.val, term.property⟩, ⟨term.val, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨middle, middleLaw⟩, ⟨argument, argumentLaw⟩⟩
    change first.app point argument = middle at argumentLaw
    subst middle
    rfl
  right_inv _ := Subtype.ext rfl

variable (inner : Data first) (outer : Data second)

def sigmaFibreEquiv {L : Type v} {R : L → Type w} {S : L → Type z}
    (decoder : ∀ index, R index ≃ S index) : Sigma R ≃ Sigma S where
  toFun term := ⟨term.1, decoder term.1 term.2⟩
  invFun term := ⟨term.1, (decoder term.1).symm term.2⟩
  left_inv term := congrArg (Sigma.mk term.1) ((decoder term.1).symm_apply_apply term.2)
  right_inv term := congrArg (Sigma.mk term.1) ((decoder term.1).apply_symm_apply term.2)

def sigmaBaseEquiv {L : Type v} {R : Type w} (decoder : L ≃ R) (body : R → Type z) :
    (Σ index : L, body (decoder index)) ≃ Sigma body where
  toFun term := ⟨decoder term.1, term.2⟩
  invFun term := ⟨decoder.symm term.1,
    cast (congrArg body (decoder.apply_symm_apply term.1).symm) term.2⟩
  left_inv term := Sigma.ext (decoder.symm_apply_apply term.1) (ContextualSmallFamilyUniverse.cast_heq _ _)
  right_inv term := Sigma.ext (decoder.apply_symm_apply term.1) (ContextualSmallFamilyUniverse.cast_heq _ _)

def sigmaDecoderEquiv {L : Type v} {R : Type w} {innerBody : L → Type z} {outerBody : R → Type t}
    (decoder : L ≃ R) (fibreDecoder : ∀ index, innerBody index ≃ outerBody (decoder index)) :
    Sigma innerBody ≃ Sigma outerBody :=
  (sigmaFibreEquiv fibreDecoder).trans (sigmaBaseEquiv decoder outerBody)

abbrev CompositeAt (point : B.Elements) : Type u :=
  Σ middle : outer.family.obj point,
    inner.family.obj ⟨point.1, (outer.decoder point middle).val⟩

def compositeDecoder (point : B.Elements) :
    CompositeAt first second inner outer point ≃ Fibre (first.comp second) point.1 point.2 :=
  (sigmaDecoderEquiv (outer.decoder point)
    (fun middle => inner.decoder ⟨point.1, (outer.decoder point middle).val⟩)).trans
      (compositeFibreEquiv first second point.1 point.2)

def composeData : Data (first.comp second) :=
  ofEquivs (first.comp second) (CompositeAt first second inner outer)
    (compositeDecoder first second inner outer)

theorem composeData_value (point : B.Elements) (term : CompositeAt first second inner outer point) :
    (((composeData first second inner outer).decoder point) term).val =
      (inner.decoder ⟨point.1, (outer.decoder point term.1).val⟩ term.2).val := rfl

end Composition

section ParameterPullback

variable (operation : NaturalHom X A) (model : Data operation)
variable {B : D ⥤ Type z} (change : NaturalHom B A)

def pullbackData : Data (pullbackSecond operation change) where
  family := ContextualSmallFamilyUniverse.substitutedFamily model.family change
  decoder point := (model.decoder ⟨point.1, change.app point.1 point.2⟩).trans
    (pullbackFibreEquiv operation change point.1 point.2).symm
  naturality {first second} step term := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (model.naturality
        ((ContextualSmallFamilyUniverse.elementMap change).map step) term)
    · exact step.2

theorem pullbackData_family : (pullbackData operation model change).family =
    ContextualSmallFamilyUniverse.substitutedFamily model.family change := rfl

theorem pullbackData_value (point : B.Elements)
    (term : (pullbackData operation model change).family.obj point) :
    (((pullbackData operation model change).decoder point) term).val.val =
      ((model.decoder ⟨point.1, change.app point.1 point.2⟩ term).val, point.2) := rfl

theorem pullbackData_identity_family :
    (pullbackData operation model (ContextualSmallMapConstructions.identity A)).family = model.family :=
  ContextualSmallFamilyUniverse.substitutedFamily_id model.family

theorem pullbackData_composite_family {C : D ⥤ Type t} (earlier : NaturalHom C B) :
    (pullbackData operation model (earlier.comp change)).family =
      ContextualSmallFamilyUniverse.substitutedFamily (pullbackData operation model change).family earlier :=
  (ContextualSmallFamilyUniverse.substitutedFamily_comp model.family change earlier).symm

end ParameterPullback

section SplitDescent

variable {B : D ⥤ Type z} (operation : NaturalHom X A)
variable (cover : NaturalHom B X) (sectionMap : NaturalHom X B)
variable (split : sectionMap.comp cover = ContextualSmallMapConstructions.identity X)
variable (model : Data (cover.comp operation))

abbrev SplitAt (point : A.Elements) : Type u :=
  {receipt : model.family.obj point //
    sectionMap.app point.1 (cover.app point.1 (model.decoder point receipt).val) =
      (model.decoder point receipt).val}

def splitDecoder (point : A.Elements) : SplitAt operation cover sectionMap model point ≃
    Fibre operation point.1 point.2 where
  toFun term := ⟨cover.app point.1 (model.decoder point term.val).val,
    (model.decoder point term.val).property⟩
  invFun term :=
    let receipt : Fibre (cover.comp operation) point.1 point.2 :=
      ⟨sectionMap.app point.1 term.val,
        (congrArg (operation.app point.1)
          (congrArg (fun map : NaturalHom X X => map.app point.1 term.val) split)).trans term.property⟩
    ⟨(model.decoder point).symm receipt, by
      have same := (model.decoder point).apply_symm_apply receipt
      have valueLaw := congrArg Subtype.val same
      rw [valueLaw]
      exact congrArg (sectionMap.app point.1)
        (congrArg (fun map : NaturalHom X X => map.app point.1 term.val) split)⟩
  left_inv term := by
    apply Subtype.ext
    apply (model.decoder point).injective
    exact ((model.decoder point).apply_symm_apply _).trans (Subtype.ext term.property)
  right_inv term := by
    apply Subtype.ext
    have same := (model.decoder point).apply_symm_apply
      (⟨sectionMap.app point.1 term.val,
        (congrArg (operation.app point.1)
          (congrArg (fun map : NaturalHom X X => map.app point.1 term.val) split)).trans term.property⟩ :
        Fibre (cover.comp operation) point.1 point.2)
    exact (congrArg (fun receipt : Fibre (cover.comp operation) point.1 point.2 =>
      cover.app point.1 receipt.val) same).trans
      (congrArg (fun map : NaturalHom X X => map.app point.1 term.val) split)

/-- A retained natural splitting gives an actual smaller subtype of the
supplied source dictionaries and a coherent decoder for the descended map.
Pointwise covering existence alone is not used to choose such a splitting. -/
def splitDescentData : Data operation :=
  ofEquivs operation (SplitAt operation cover sectionMap model)
    (splitDecoder operation cover sectionMap split model)

end SplitDescent

end Mettapedia.TypeTheory.ContextualCoherentSmallMaps
