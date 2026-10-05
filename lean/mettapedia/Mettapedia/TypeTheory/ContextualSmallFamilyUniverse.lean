import Mettapedia.TypeTheory.ContextualEnumerationCovers

/-!
# A constructed universe of coherent small future families

A code at a context is an actual small-valued functor on its complete
future category. Context restriction precomposes that functor with the
actual arrow-prefix functor. Decoding evaluates the code at the identity
future. Codes live one host universe above their decoded fibres.

The construction classifies authored small displayed families, including
their maps along all contextual arrows. Surjective small receipt lists or
pointwise existence of small fibres are distinct inputs; neither is used
to select a coherent decoded family here. No native foundation or
unrestricted realignment law is installed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyUniverse

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafBaseChange

universe u v w z
variable {D : Type u} [Category.{u} D]

def root (point : D) : Future.Objects point := ⟨point, 𝟙 point⟩

def futurePrefix {first second : D} (step : first ⟶ second) :
    Future.Objects second ⥤ Future.Objects first where
  obj future := ⟨future.1, step ≫ future.2⟩
  map arrow := ⟨arrow.1, (Category.assoc _ _ _).trans (congrArg (fun tail => step ≫ tail) arrow.2)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem futureArrow_heq {point : D}
    {first otherFirst second otherSecond : Future.Objects point}
    (source : first = otherFirst) (target : second = otherSecond)
    (left : first ⟶ second) (right : otherFirst ⟶ otherSecond)
    (same : HEq left.val right.val) : HEq left right := by
  cases source
  cases target
  exact heq_of_eq (Subtype.ext (eq_of_heq same))

theorem prefix_id (point : D) : futurePrefix (𝟙 point) = Cat.identity (Future.Objects point) := by
  have objects : ∀ future : Future.Objects point, (futurePrefix (𝟙 point)).obj future = future :=
    fun future => Future.objects_ext rfl (heq_of_eq (Category.id_comp future.2))
  refine Functor.hext objects ?_
  intro first second step
  exact futureArrow_heq (objects first) (objects second) _ _ (heq_of_eq rfl)

theorem prefix_comp {first middle last : D} (earlier : first ⟶ middle) (later : middle ⟶ last) :
    futurePrefix (earlier ≫ later) = Cat.compose (futurePrefix later) (futurePrefix earlier) := by
  have objects : ∀ future : Future.Objects last,
      (futurePrefix (earlier ≫ later)).obj future = (futurePrefix earlier).obj ((futurePrefix later).obj future) :=
    fun future => Future.objects_ext rfl (heq_of_eq (Category.assoc earlier later future.2))
  refine Functor.hext objects ?_
  intro first second step
  exact futureArrow_heq (objects first) (objects second) _ _ (heq_of_eq rfl)

def restrict {E : Type w} {K : Type z} [Category.{u} E] [Category.{u} K]
    (change : E ⥤ K) (family : K ⥤ Type v) : E ⥤ Type v where
  obj point := family.obj (change.obj point)
  map step := family.map (change.map step)
  map_id point := by rw [change.map_id, family.map_id]
  map_comp earlier later := by rw [change.map_comp, family.map_comp]

theorem restrict_id (family : D ⥤ Type v) : restrict (Cat.identity D) family = family := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

abbrev Code (point : D) : Type (u + 1) := Future.Objects point ⥤ Type u

def codeMap {first second : D} (step : first ⟶ second) (code : Code first) : Code second :=
  restrict (futurePrefix step) code

theorem codeMap_id (point : D) (code : Code point) : codeMap (𝟙 point) code = code := by
  unfold codeMap
  rw [prefix_id]
  exact restrict_id code

theorem codeMap_comp {first middle last : D} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (code : Code first) : codeMap (earlier ≫ later) code = codeMap later (codeMap earlier code) := by
  unfold codeMap
  rw [prefix_comp]
  rfl

def universeFamily : D ⥤ Type (u + 1) where
  obj := Code
  map step := TypeCat.ofHom (codeMap step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact codeMap_id point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact codeMap_comp earlier later

def decode {point : D} (code : Code point) : Type u := code.obj (root point)

def rootArrow {first second : D} (step : first ⟶ second) :
    root first ⟶ (futurePrefix step).obj (root second) :=
  ⟨step, (Category.id_comp step).trans (Category.comp_id step).symm⟩

def decodeMap {first second : D} (step : first ⟶ second) (code : Code first) :
    decode code → decode (codeMap step code) := code.map (rootArrow step)

theorem familyMap_heq {E : Type w} [Category.{u} E] (family : E ⥤ Type v)
    {first otherFirst second otherSecond : E}
    (source : first = otherFirst) (target : second = otherSecond)
    (left : first ⟶ second) (right : otherFirst ⟶ otherSecond) (same : HEq left right)
    (value : family.obj first) (other : family.obj otherFirst) (values : HEq value other) :
    HEq (family.map left value) (family.map right other) := by
  cases source
  cases target
  cases eq_of_heq same
  cases eq_of_heq values
  rfl

theorem decodeMap_id_heq (point : D) (code : Code point) (value : decode code) :
    HEq (decodeMap (𝟙 point) code value) value := by
  have target : (futurePrefix (𝟙 point)).obj (root point) = root point :=
    congrArg (fun change : Future.Objects point ⥤ Future.Objects point => change.obj (root point))
      (prefix_id point)
  exact (familyMap_heq code rfl target (rootArrow (𝟙 point)) (𝟙 (root point))
    (futureArrow_heq rfl target _ _ (heq_of_eq rfl)) value value (heq_of_eq rfl)).trans
      (heq_of_eq (code.map_id_apply (root point) value))

theorem decodeMap_comp_heq {first middle last : D} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (code : Code first) (value : decode code) :
    HEq (decodeMap (earlier ≫ later) code value)
      (decodeMap later (codeMap earlier code) (decodeMap earlier code value)) := by
  have target : (futurePrefix (earlier ≫ later)).obj (root last) =
      (futurePrefix earlier).obj ((futurePrefix later).obj (root last)) :=
    congrArg (fun change : Future.Objects last ⥤ Future.Objects first => change.obj (root last))
      (prefix_comp earlier later)
  exact (familyMap_heq code rfl target (rootArrow (earlier ≫ later))
    (rootArrow earlier ≫ (futurePrefix earlier).map (rootArrow later))
    (futureArrow_heq rfl target _ _ (heq_of_eq rfl)) value value (heq_of_eq rfl)).trans
      (heq_of_eq (code.map_comp_apply _ _ value))

theorem cast_heq {first second : Type v} (same : first = second) (value : first) :
    HEq (cast same value) value := by
  cases same
  rfl

def typeEqualityEquiv {first second : Type v} (same : first = second) : first ≃ second where
  toFun := cast same
  invFun := cast same.symm
  left_inv := by intro value; cases same; rfl
  right_inv := by intro value; cases same; rfl

theorem decodeMap_heq {first second : D} (step : first ⟶ second) {code other : Code first}
    (same : code = other) (value : decode code) (otherValue : decode other)
    (values : HEq value otherValue) : HEq (decodeMap step code value) (decodeMap step other otherValue) := by
  cases same
  cases eq_of_heq values
  rfl

/-- Identity-future evaluation carries an actual displayed action, including
the retained code equality of an arrow in the universe's element category. -/
def decoder : (universeFamily (D := D)).Elements ⥤ Type u where
  obj point := decode point.2
  map {first second} step := TypeCat.ofHom fun value =>
    cast (congrArg (fun code : Code second.1 => decode code) step.2) (decodeMap step.1 first.2 value)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    apply eq_of_heq
    exact (cast_heq _ _).trans (decodeMap_id_heq point.1 point.2 value)
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    apply eq_of_heq
    have earlierValue : HEq
        (cast (congrArg (fun code : Code middle.1 => decode code) earlier.2)
          (decodeMap earlier.1 first.2 value)) (decodeMap earlier.1 first.2 value) := cast_heq _ _
    exact (cast_heq _ _).trans ((decodeMap_comp_heq earlier.1 later.1 first.2 value).trans
      ((decodeMap_heq later.1 earlier.2.symm _ _ earlierValue).symm.trans (cast_heq _ _).symm))

theorem decoder_map_heq {first second : (universeFamily (D := D)).Elements} (step : first ⟶ second)
    (value : decode first.2) : HEq (decoder.map step value) (decodeMap step.1 first.2 value) := cast_heq _ _

theorem elementsArrow_heq {base : D ⥤ Type v}
    {first otherFirst second otherSecond : base.Elements}
    (source : first = otherFirst) (target : second = otherSecond)
    (left : first ⟶ second) (right : otherFirst ⟶ otherSecond)
    (same : HEq left.val right.val) : HEq left right := by
  cases source
  cases target
  exact heq_of_eq (Subtype.ext (eq_of_heq same))

abbrev TotalAt {base : D ⥤ Type v} (family : base.Elements ⥤ Type w) (point : D) :=
  Σ value : base.obj point, family.obj ⟨point, value⟩

def totalMap {base : D ⥤ Type v} (family : base.Elements ⥤ Type w)
    {first second : D} (step : first ⟶ second) (receipt : TotalAt family first) : TotalAt family second :=
  ⟨base.map step receipt.1,
    family.map (CategoryOfElements.homMk (F := base)
      ⟨first, receipt.1⟩ ⟨second, base.map step receipt.1⟩ step rfl) receipt.2⟩

theorem totalMap_id {base : D ⥤ Type v} (family : base.Elements ⥤ Type w)
    (point : D) (receipt : TotalAt family point) : totalMap family (𝟙 point) receipt = receipt := by
  rcases receipt with ⟨value, evidence⟩
  apply Sigma.ext (base.map_id_apply point value)
  have target : (⟨point, base.map (𝟙 point) value⟩ : base.Elements) = ⟨point, value⟩ :=
    congrArg (fun value => (⟨point, value⟩ : base.Elements)) (base.map_id_apply point value)
  exact (familyMap_heq (E := base.Elements) family rfl target _
    (CategoryOfElements.homMk (F := base) ⟨point, value⟩ ⟨point, value⟩
      (𝟙 point) (base.map_id_apply point value))
    (elementsArrow_heq rfl target _ _ (heq_of_eq rfl)) evidence evidence (heq_of_eq rfl)).trans
      (heq_of_eq (family.map_id_apply _ evidence))

theorem totalMap_comp {base : D ⥤ Type v} (family : base.Elements ⥤ Type w)
    {first middle last : D} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (receipt : TotalAt family first) :
    totalMap family (earlier ≫ later) receipt = totalMap family later (totalMap family earlier receipt) := by
  rcases receipt with ⟨value, evidence⟩
  apply Sigma.ext (base.map_comp_apply earlier later value)
  have target : (⟨last, base.map (earlier ≫ later) value⟩ : base.Elements) =
      ⟨last, base.map later (base.map earlier value)⟩ :=
    congrArg (fun value => (⟨last, value⟩ : base.Elements)) (base.map_comp_apply earlier later value)
  exact (familyMap_heq (E := base.Elements) family rfl target _
    (CategoryOfElements.homMk (F := base)
      ⟨first, value⟩ ⟨middle, base.map earlier value⟩ earlier rfl ≫
        CategoryOfElements.homMk (F := base)
          ⟨middle, base.map earlier value⟩ ⟨last, base.map later (base.map earlier value)⟩ later rfl)
    (elementsArrow_heq rfl target _ _ (heq_of_eq rfl)) evidence evidence (heq_of_eq rfl)).trans
      (heq_of_eq (family.map_comp_apply _ _ evidence))

def total {base : D ⥤ Type v} (family : base.Elements ⥤ Type w) : D ⥤ Type (max v w) where
  obj := TotalAt family
  map step := TypeCat.ofHom (totalMap family step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact totalMap_id family point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact totalMap_comp family earlier later

def projection {base : D ⥤ Type v} (family : base.Elements ⥤ Type w) : NaturalHom (total family) base where
  app _ := Sigma.fst
  naturality _ _ := rfl

abbrev universalTotal : D ⥤ Type (u + 1) := total (decoder (D := D))

def universalProjection : NaturalHom (universalTotal (D := D)) universeFamily := projection decoder

def universalFibreEquiv (point : D) (code : Code point) :
    decode code ≃ Fibre universalProjection point code where
  toFun value := ⟨⟨code, value⟩, rfl⟩
  invFun receipt := cast (congrArg (fun code : Code point => decode code) receipt.property) receipt.val.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨other, value⟩, same⟩
    change other = code at same
    cases same
    rfl

def universalEnumeration (point : D) (code : Code point) :
    Enumeration.{u, u + 1} (Fibre universalProjection point code) where
  Carrier := decode code
  value := universalFibreEquiv point code
  covered := (universalFibreEquiv point code).surjective

theorem universalProjection_smallFibres : SmallFibres (universalProjection (D := D)) :=
  fun point code => ⟨universalEnumeration point code⟩

section Classification

variable {base : D ⥤ Type v} (family : base.Elements ⥤ Type u)

def futureElement (point : D) (value : base.obj point) : Future.Objects point ⥤ base.Elements where
  obj future := ⟨future.1, base.map future.2 value⟩
  map {first second} arrow := CategoryOfElements.homMk (F := base)
    ⟨first.1, base.map first.2 value⟩ ⟨second.1, base.map second.2 value⟩ arrow.1
      ((base.map_comp_apply first.2 arrow.1 value).symm.trans
        (congrArg (fun step => base.map step value) arrow.2))
  map_id _ := rfl
  map_comp _ _ := rfl

def familyCode (point : D) (value : base.obj point) : Code point :=
  restrict (futureElement point value) family

theorem familyArrow_heq {E : Type w} [Category.{u} E] (family : E ⥤ Type z)
    {first otherFirst second otherSecond : E}
    (source : first = otherFirst) (target : second = otherSecond)
    (left : first ⟶ second) (right : otherFirst ⟶ otherSecond) (same : HEq left right) :
    HEq (family.map left) (family.map right) := by
  cases source
  cases target
  cases eq_of_heq same
  rfl

theorem familyCode_naturality {first second : D} (step : first ⟶ second) (value : base.obj first) :
    codeMap step (familyCode family first value) = familyCode family second (base.map step value) := by
  have objects : ∀ future : Future.Objects second,
      (futureElement first value).obj ((futurePrefix step).obj future) =
        (futureElement second (base.map step value)).obj future :=
    fun future => congrArg (fun member : base.obj future.1 => (⟨future.1, member⟩ : base.Elements))
      (base.map_comp_apply step future.2 value)
  refine Functor.hext (fun future => congrArg family.obj (objects future)) ?_
  intro firstFuture secondFuture arrow
  exact familyArrow_heq (E := base.Elements) family (objects firstFuture) (objects secondFuture) _ _
    (elementsArrow_heq (base := base) (objects firstFuture) (objects secondFuture) _ _ (heq_of_eq rfl))

/-- The classifier constructs every complete future code from the authored
displayed functor; its naturality follows from the actual contextual action. -/
def classifier : NaturalHom base universeFamily where
  app := familyCode family
  naturality := familyCode_naturality family

def elementMap {other : D ⥤ Type w} (operation : NaturalHom base other) : base.Elements ⥤ other.Elements where
  obj point := ⟨point.1, operation.app point.1 point.2⟩
  map {first second} step := CategoryOfElements.homMk (F := other) _ _ step.1
    ((operation.naturality step.1 first.2).trans (congrArg (operation.app second.1) step.2))
  map_id _ := rfl
  map_comp _ _ := rfl

def decodedFamily (operation : NaturalHom base universeFamily) : base.Elements ⥤ Type u :=
  restrict (elementMap operation) decoder

theorem evaluationPoint_eq (point : D) (value : base.obj point) :
    (futureElement point value).obj (root point) = (⟨point, value⟩ : base.Elements) :=
  congrArg (fun member : base.obj point => (⟨point, member⟩ : base.Elements))
    (base.map_id_apply point value)

def evaluationEquiv (point : D) (value : base.obj point) :
    decode (familyCode family point value) ≃ family.obj ⟨point, value⟩ :=
  typeEqualityEquiv (congrArg family.obj (evaluationPoint_eq point value))

theorem castFunction_heq {input first second : Type u} (same : first = second) (operation : input → first) :
    HEq (TypeCat.ofHom (fun value => cast same (operation value))) (TypeCat.ofHom operation) := by
  cases same
  rfl

theorem decoder_arrow_heq {first second : (universeFamily (D := D)).Elements} (step : first ⟶ second) :
    HEq (decoder.map step) (TypeCat.ofHom (decodeMap step.1 first.2)) := castFunction_heq _ _

/-- The independently constructed identity decoder recovers the whole
displayed family, including its maps; present-fibre equivalence alone is
insufficient for this equation. -/
theorem decoded_classifier_eq : decodedFamily (classifier family) = family := by
  refine Functor.hext (fun point => congrArg family.obj (evaluationPoint_eq point.1 point.2)) ?_
  intro first second step
  have source := evaluationPoint_eq first.1 first.2
  have target : (futureElement first.1 first.2).obj
      ((futurePrefix step.1).obj (root second.1)) = second :=
    Sigma.ext rfl (heq_of_eq ((congrArg (fun arrow => base.map arrow first.2)
      (Category.comp_id step.1)).trans step.2))
  exact (decoder_arrow_heq ((elementMap (classifier family)).map step)).trans
    (familyArrow_heq (E := base.Elements) family source target _ step
      (elementsArrow_heq (base := base) source target _ step (heq_of_eq rfl)))

end Classification

end Mettapedia.TypeTheory.ContextualSmallFamilyUniverse
