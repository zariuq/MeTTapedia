import Mettapedia.TypeTheory.PresheafElementSubstitutionLifting
import Mettapedia.TypeTheory.CategoryOfElementsBaseChange

/-!
# Future-arrow indices for presheaf dependent products

At a contextual point, a pointwise right-Kan dependent product must answer
for later syntax arrows and dependent arguments. A natural context
substitution sends the future element reached by such an arrow to the same
observed element reached after substitution. This file compares both the
future-argument object types and their evidence-bearing index categories.
It does not yet construct the right-Kan limit or Beck-Chevalley comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafPiIndexComparison

open CategoryTheory
open Mettapedia.TypeTheory.CategoryOfElementsBaseChange

universe u v w wEvidence

variable {Context : Type u} [Category.{v} Context]
variable {source target : Context ⥤ Type w}

/-- An object of the pointwise right-Kan comma category, unpacked as
an observed endpoint, an arrow to it, and a dependent argument. -/
def elementCommaObjectIndex (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) : Type (max u v w wEvidence) :=
  Σ observed : base.Elements, (point ⟶ observed) × domain.obj observed

/-- The same index normalized by the underlying syntax arrow; its
endpoint value is determined by functorial transport. -/
def elementFutureIndex (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) : Type (max u v wEvidence) :=
  Σ later : Context, Σ route : point.1 ⟶ later,
    domain.obj ⟨later, base.map route point.2⟩

/-- Normalizing a category-of-elements arrow loses neither its syntax
arrow nor its dependent argument. -/
def elementCommaObjectIndexEquiv (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) :
    elementCommaObjectIndex base domain point ≃
      elementFutureIndex base domain point where
  toFun
    | ⟨⟨later, observedValue⟩, ⟨⟨route, follows⟩, evidence⟩⟩ =>
        ⟨later, route, follows.symm ▸ evidence⟩
  invFun
    | ⟨later, route, evidence⟩ =>
        ⟨⟨later, base.map route point.2⟩,
          ⟨⟨route, rfl⟩, evidence⟩⟩
  left_inv := by
    rintro ⟨⟨later, observedValue⟩, ⟨⟨route, follows⟩, evidence⟩⟩
    change point.1 ⟶ later at route
    change base.map route point.2 = observedValue at follows
    cases follows
    rfl
  right_inv := by
    rintro ⟨later, route, evidence⟩
    rfl

/-- The exact structured-arrow object type in Mathlib's pointwise
right-Kan formula for a category-of-elements projection. -/
abbrev structuredElementIndex (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) :=
  StructuredArrow point (CategoryOfElements.π domain)

/-- Structured-arrow objects and their explicit endpoint/arrow/evidence
triples are equivalent, not merely equinumerous. -/
def structuredElementIndexEquiv (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) :
    structuredElementIndex base domain point ≃
      elementCommaObjectIndex base domain point where
  toFun item := ⟨item.right.1, item.hom, item.right.2⟩
  invFun
    | ⟨observed, ⟨arrow, evidence⟩⟩ =>
        ⟨⟨⟨⟩⟩, ⟨observed, evidence⟩, arrow⟩
  left_inv := by
    intro item
    cases item with
    | mk left right hom =>
        cases left
        rfl
  right_inv := by
    rintro ⟨observed, ⟨arrow, evidence⟩⟩
    rfl

/-- The pointwise right-Kan structured-arrow category maps to the
category of elements of the dependent argument family over outgoing
arrows. Both the route triangle and its dependent evidence are kept. -/
def structuredElementToUnderElements (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) :
    structuredElementIndex base domain point ⥤
      (Under.forget point ⋙ domain).Elements where
  obj item := ⟨Under.mk item.hom, item.right.2⟩
  map {first second} between :=
    ⟨Under.homMk between.right.val (StructuredArrow.w between),
      between.right.property⟩
  map_id item := by
    apply CategoryOfElements.ext (Under.forget point ⋙ domain)
    apply StructuredArrow.hom_ext
    rfl
  map_comp firstStep secondStep := by
    apply CategoryOfElements.ext (Under.forget point ⋙ domain)
    apply StructuredArrow.hom_ext
    rfl

/-- Reconstruct a dependent structured-arrow index from an outgoing
route equipped with its endpoint evidence. -/
def underElementsToStructuredElement (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) :
    (Under.forget point ⋙ domain).Elements ⥤
      structuredElementIndex base domain point where
  obj receipt :=
    ⟨⟨⟨⟩⟩, ⟨receipt.1.right, receipt.2⟩, receipt.1.hom⟩
  map {first second} between :=
    StructuredArrow.homMk
      (CategoryOfElements.homMk
        (⟨first.1.right, first.2⟩ : domain.Elements)
        (⟨second.1.right, second.2⟩ : domain.Elements)
        between.val.right between.property)
      (Under.w between.val)
  map_id receipt := by
    apply StructuredArrow.hom_ext
    apply CategoryOfElements.ext domain
    rfl
  map_comp firstStep secondStep := by
    apply StructuredArrow.hom_ext
    apply CategoryOfElements.ext domain
    rfl

/-- Reconstructing after unpacking preserves every pointwise
structured-arrow object, including its dependent evidence. -/
theorem structuredElement_roundtrip_obj (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements)
    (item : structuredElementIndex base domain point) :
    (structuredElementToUnderElements base domain point ⋙
      underElementsToStructuredElement base domain point).obj item = item := by
  cases item with
  | mk left right hom =>
      cases left
      rfl

/-- Unpacking after reconstruction preserves every outgoing route and
its dependent evidence. -/
theorem underElements_roundtrip_obj (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements)
    (receipt : (Under.forget point ⋙ domain).Elements) :
    (underElementsToStructuredElement base domain point ⋙
      structuredElementToUnderElements base domain point).obj receipt = receipt := by
  cases receipt with
  | mk route evidence =>
      cases route with
      | mk left right hom =>
          cases left
          rfl

/-- Reconstruction and unpacking are naturally inverse on the actual
pointwise structured-arrow category. -/
def structuredElement_roundtrip_iso (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) :
    structuredElementToUnderElements base domain point ⋙
        underElementsToStructuredElement base domain point ≅
      𝟭 (structuredElementIndex base domain point) :=
  NatIso.ofComponents
    (fun item => StructuredArrow.isoMk (Iso.refl item.right) (by
      change item.hom ≫ (CategoryOfElements.π domain).map (𝟙 item.right) =
        item.hom
      rw [(CategoryOfElements.π domain).map_id]
      exact Category.comp_id _))
    (by
      intro first second between
      apply StructuredArrow.hom_ext
      apply CategoryOfElements.ext domain
      simp only [StructuredArrow.comp_right, Functor.comp_map,
        Functor.id_map]
      change between.right.val ≫ 𝟙 second.right.1 =
        𝟙 first.right.1 ≫ between.right.val
      calc
        between.right.val ≫ 𝟙 second.right.1 = between.right.val :=
          Category.comp_id _
        _ = 𝟙 first.right.1 ≫ between.right.val :=
          (Category.id_comp _).symm)

/-- The inverse direction also retains the dependent endpoint evidence,
not merely the underlying outgoing route. -/
def underElements_roundtrip_iso (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) :
    underElementsToStructuredElement base domain point ⋙
        structuredElementToUnderElements base domain point ≅
      𝟭 ((Under.forget point ⋙ domain).Elements) :=
  NatIso.ofComponents
    (fun receipt =>
      CategoryOfElements.isoMk
        ((underElementsToStructuredElement base domain point ⋙
          structuredElementToUnderElements base domain point).obj receipt)
        receipt
        (Under.isoMk (Iso.refl receipt.1.right) (by
          change receipt.1.hom ≫ 𝟙 receipt.1.right = receipt.1.hom
          exact Category.comp_id _))
        (by
          change domain.map (𝟙 receipt.1.right) receipt.2 = receipt.2
          exact domain.map_id_apply receipt.1.right receipt.2))
    (by
      intro first second between
      apply CategoryOfElements.ext (Under.forget point ⋙ domain)
      apply StructuredArrow.hom_ext
      change between.val.right ≫ 𝟙 second.1.right =
        𝟙 first.1.right ≫ between.val.right
      calc
        between.val.right ≫ 𝟙 second.1.right = between.val.right :=
          Category.comp_id _
        _ = 𝟙 first.1.right ≫ between.val.right :=
          (Category.id_comp _).symm)

/-- The actual pointwise right-Kan structured-arrow category is
equivalent to the proof-relevant category of elements of endpoint
evidence over outgoing arrows. This comparison keeps morphisms, not
only the index-object set. -/
def structuredElementUnderElementsEquivalence
    (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) :
    structuredElementIndex base domain point ≌
      (Under.forget point ⋙ domain).Elements where
  functor := structuredElementToUnderElements base domain point
  inverse := underElementsToStructuredElement base domain point
  unitIso := (structuredElement_roundtrip_iso base domain point).symm
  counitIso := underElements_roundtrip_iso base domain point
  functor_unitIso_comp item := by
    apply CategoryOfElements.ext (Under.forget point ⋙ domain)
    apply StructuredArrow.hom_ext
    change (𝟙 item.right.1) ≫ 𝟙 item.right.1 = 𝟙 item.right.1
    exact Category.id_comp _

/-- Read the exact endpoint evidence from a route-indexed element. -/
def underElementsEndpoint (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) :
    (Under.forget point ⋙ domain).Elements ⥤ domain.Elements where
  obj receipt := ⟨receipt.1.right, receipt.2⟩
  map {first second} between :=
    CategoryOfElements.homMk
      ⟨first.1.right, first.2⟩
      ⟨second.1.right, second.2⟩
      between.val.right between.property
  map_id receipt := by
    apply CategoryOfElements.ext domain
    rfl
  map_comp firstStep secondStep := by
    apply CategoryOfElements.ext domain
    rfl

/-- The structured-arrow / route-with-evidence comparison preserves
the exact endpoint object and evidence that the pointwise limit diagram
will read. -/
def structuredElementToUnderElements_endpointIso
    (base : Context ⥤ Type w)
    (domain : base.Elements ⥤ Type wEvidence)
    (point : base.Elements) :
    structuredElementToUnderElements base domain point ⋙
        underElementsEndpoint base domain point ≅
      StructuredArrow.proj point (CategoryOfElements.π domain) :=
  NatIso.ofComponents
    (fun item => CategoryOfElements.isoMk
      ((structuredElementToUnderElements base domain point ⋙
        underElementsEndpoint base domain point).obj item)
      item.right
      (Iso.refl item.right.1)
      (by
        change domain.map (𝟙 item.right.1) item.right.2 = item.right.2
        exact domain.map_id_apply item.right.1 item.right.2))
    (by
      intro first second between
      apply CategoryOfElements.ext domain
      change between.right.val ≫ 𝟙 second.right.1 =
        𝟙 first.right.1 ≫ between.right.val
      calc
        between.right.val ≫ 𝟙 second.right.1 = between.right.val :=
          Category.comp_id _
        _ = 𝟙 first.right.1 ≫ between.right.val :=
          (Category.id_comp _).symm)


/-- The object indices of the structured-arrow comma category used in
the pointwise right-Kan formula, retaining the domain argument. -/
def observedCommaObjectIndex (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) : Type (max u v w wEvidence) :=
  elementCommaObjectIndex target domain (substitution.mapElements.obj point)

/-- The actual structured-arrow object type in Mathlib's pointwise
right-Kan formula for the domain projection. -/
abbrev structuredFutureIndex (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :=
  structuredElementIndex target domain (substitution.mapElements.obj point)

/-- A pointwise structured-arrow object is exactly an observed endpoint,
an outgoing arrow to it, and its retained dependent argument. -/
def structuredFutureIndexEquiv (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :
    structuredFutureIndex substitution domain point ≃
      observedCommaObjectIndex substitution domain point :=
  structuredElementIndexEquiv target domain
    (substitution.mapElements.obj point)

/-- Future dependent arguments, viewed after substituting the current
context point. -/
def observedFutureIndex (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) : Type (max u v wEvidence) :=
  elementFutureIndex target domain (substitution.mapElements.obj point)

/-- The same future arguments, first transported in the source context
and then observed by the natural substitution. -/
def reindexedFutureIndex (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) : Type (max u v wEvidence) :=
  Σ later : Context, Σ route : point.1 ⟶ later,
    domain.obj (substitution.mapElements.obj
      ⟨later, source.map route point.2⟩)

/-- Naturality identifies the observed future element at each syntax
arrow, including its carried context value. -/
theorem observedFutureElement_eq (substitution : source ⟶ target)
    (point : source.Elements) (later : Context)
    (route : point.1 ⟶ later) :
    (⟨later,
      target.map route (substitution.app point.1 point.2)⟩ : target.Elements) =
      substitution.mapElements.obj
        ⟨later, source.map route point.2⟩ := by
  change (⟨later,
      target.map route (substitution.app point.1 point.2)⟩ : target.Elements) =
    ⟨later, substitution.app later (source.map route point.2)⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  exact (substitution.naturality_apply route point.2).symm

/-- An observed outgoing element-arrow has a uniquely determined
endpoint value, so its comma-object index can be normalized to its
underlying syntax arrow and retained dependent argument. -/
def observedCommaObjectIndexEquiv (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :
    observedCommaObjectIndex substitution domain point ≃
      observedFutureIndex substitution domain point :=
  elementCommaObjectIndexEquiv target domain
    (substitution.mapElements.obj point)

/-- The future-argument indices before and after natural substitution
are equivalent. The equivalence is just transport along the proved
element equality; it does not identify distinct syntax arrows. -/
def futureIndexEquiv (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :
    observedFutureIndex substitution domain point ≃
      reindexedFutureIndex substitution domain point :=
  Equiv.sigmaCongrRight fun later =>
    Equiv.sigmaCongrRight fun route =>
      Equiv.cast (congrArg domain.obj
        (observedFutureElement_eq substitution point later route))

/-- The comparison retains the future syntax context and arrow exactly;
only the dependent argument is transported across naturality. -/
theorem futureIndexEquiv_retains_route (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements)
    (answer : observedFutureIndex substitution domain point) :
    (futureIndexEquiv substitution domain point answer).1 = answer.1 ∧
      (futureIndexEquiv substitution domain point answer).2.1 = answer.2.1 :=
  ⟨rfl, rfl⟩

/-- The structured-arrow indices for the domain reindexed to the source
presheaf context. -/
abbrev reindexedStructuredFutureIndex (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :=
  structuredElementIndex source (substitution.mapElements ⋙ domain) point

/-- The reindexed pointwise comma objects normalize to the same future
syntax arrows, with domain arguments read after substitution. -/
def reindexedStructuredFutureIndexEquiv (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :
    reindexedStructuredFutureIndex substitution domain point ≃
      reindexedFutureIndex substitution domain point :=
  (structuredElementIndexEquiv source
    (substitution.mapElements ⋙ domain) point).trans
      (elementCommaObjectIndexEquiv source
        (substitution.mapElements ⋙ domain) point)

/-- At each source context element, the *objects* indexing the two
pointwise right-Kan products correspond exactly under natural
substitution. The categorical comparison is proved separately below. -/
def pointwisePiIndexBaseChangeEquiv (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :
    structuredFutureIndex substitution domain point ≃
      reindexedStructuredFutureIndex substitution domain point :=
  (((structuredFutureIndexEquiv substitution domain point).trans
    (observedCommaObjectIndexEquiv substitution domain point)).trans
    (futureIndexEquiv substitution domain point)).trans
    (reindexedStructuredFutureIndexEquiv substitution domain point).symm

/-- A natural context substitution sends a reindexed dependent future
argument to its observed future argument. The retained evidence is not
recomputed or replaced. This is the forward functor of the pending
dependent comma-category base-change comparison. -/
def dependentIndexBaseChangeForward (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :
    reindexedStructuredFutureIndex substitution domain point ⥤
      structuredFutureIndex substitution domain point where
  obj item :=
    ⟨⟨⟨⟩⟩,
      ⟨substitution.mapElements.obj item.right.1, item.right.2⟩,
      substitution.mapElements.map item.hom⟩
  map {first second} between :=
    StructuredArrow.homMk
      (CategoryOfElements.homMk
        (⟨substitution.mapElements.obj first.right.1, first.right.2⟩ :
          domain.Elements)
        (⟨substitution.mapElements.obj second.right.1, second.right.2⟩ :
          domain.Elements)
        (substitution.mapElements.map between.right.val)
        between.right.property)
      (by
        change substitution.mapElements.map first.hom ≫
            substitution.mapElements.map
              ((CategoryOfElements.π
                (substitution.mapElements ⋙ domain)).map between.right) =
          substitution.mapElements.map second.hom
        exact (substitution.mapElements.map_comp _ _).symm.trans
          (congrArg substitution.mapElements.map
            (StructuredArrow.w between)))
  map_id item := by
    apply StructuredArrow.hom_ext
    apply CategoryOfElements.ext domain
    exact substitution.mapElements.map_id _
  map_comp firstStep secondStep := by
    apply StructuredArrow.hom_ext
    apply CategoryOfElements.ext domain
    exact substitution.mapElements.map_comp _ _

/-- The question at a present dependent argument is carried to the
same argument at the observed point. No argument value is recomputed. -/
theorem dependentIndexBaseChangeForward_identity
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (receipt : (substitution.mapElements ⋙ domain).Elements) :
    (dependentIndexBaseChangeForward substitution domain receipt.1).obj
        (StructuredArrow.mk (T := CategoryOfElements.π
          (substitution.mapElements ⋙ domain))
          (Y := receipt) (𝟙 receipt.1)) =
      StructuredArrow.mk (T := CategoryOfElements.π domain)
        (Y := (mapPrecompElements substitution.mapElements domain).obj receipt)
        (𝟙 (substitution.mapElements.obj receipt.1)) := by
  rfl

/-- Natural substitution induces an equivalence of complete dependent
future-index categories. The outgoing route equivalence lifts through
the category of elements of the dependent argument family. -/
noncomputable def dependentIndexBaseChangeEquivalence
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :
    reindexedStructuredFutureIndex substitution domain point ≌
      structuredFutureIndex substitution domain point :=
  (structuredElementUnderElementsEquivalence source
      (substitution.mapElements ⋙ domain) point).trans
    ((precompElementsEquivalence
      (PresheafElementSubstitutionLifting.underMapElementsEquivalence
        substitution point)
      (Under.forget (substitution.mapElements.obj point) ⋙ domain)).trans
      (structuredElementUnderElementsEquivalence target domain
        (substitution.mapElements.obj point)).symm)

/-- The categorical equivalence is carried by the already specified
forward substitution action, rather than a second observational map. -/
theorem dependentIndexBaseChangeEquivalence_forward_obj
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements)
    (item : reindexedStructuredFutureIndex substitution domain point) :
    (dependentIndexBaseChangeEquivalence substitution domain point).functor.obj item =
      (dependentIndexBaseChangeForward substitution domain point).obj item := by
  rfl

/-- The same agreement holds on route/evidence-preserving morphisms. -/
theorem dependentIndexBaseChangeEquivalence_forward_map
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements)
    {first second : reindexedStructuredFutureIndex substitution domain point}
    (between : first ⟶ second) :
    (dependentIndexBaseChangeEquivalence substitution domain point).functor.map between =
      (dependentIndexBaseChangeForward substitution domain point).map between := by
  rfl

/-- The assembled equivalence has precisely the original forward
functor, not merely objectwise the same answer set. -/
theorem dependentIndexBaseChangeEquivalence_functor_eq
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :
    (dependentIndexBaseChangeEquivalence substitution domain point).functor =
      dependentIndexBaseChangeForward substitution domain point := by
  rfl

/-- The pointwise right-Kan endpoint diagram commutes with dependent
base change on the nose. It retains the same endpoint evidence rather
than comparing only its truth value. -/
theorem dependentIndexBaseChange_endpointDiagram
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements) :
    dependentIndexBaseChangeForward substitution domain point ⋙
        StructuredArrow.proj (substitution.mapElements.obj point)
          (CategoryOfElements.π domain) =
      StructuredArrow.proj point
          (CategoryOfElements.π (substitution.mapElements ⋙ domain)) ⋙
        mapPrecompElements substitution.mapElements domain := by
  rfl

/-- Changing the current context point commutes with observing a
dependent future index up to a canonical natural isomorphism. The
square is contravariant in the point: an arrow from `earlier` to
`later` precomposes future routes. -/
def dependentIndexBaseChangeForward_naturalIso
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    {earlier later : source.Elements}
    (route : earlier ⟶ later) :
    StructuredArrow.map route ⋙
        dependentIndexBaseChangeForward substitution domain earlier ≅
      dependentIndexBaseChangeForward substitution domain later ⋙
        StructuredArrow.map (substitution.mapElements.map route) :=
  NatIso.ofComponents
    (fun item => StructuredArrow.isoMk (Iso.refl _) (by
      change substitution.mapElements.map (route ≫ item.hom) ≫ 𝟙 _ =
        substitution.mapElements.map route ≫
          substitution.mapElements.map item.hom
      rw [Category.comp_id]
      exact substitution.mapElements.map_comp route item.hom))
    (by
      intro first second between
      apply StructuredArrow.hom_ext
      apply CategoryOfElements.ext domain
      change substitution.mapElements.map between.right.val ≫ 𝟙 _ =
        𝟙 _ ≫ substitution.mapElements.map between.right.val
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The point-change coherence isomorphism changes only the
description of the outgoing route: its endpoint-evidence morphism is
the identity. This is the exact witness needed by pointwise limits. -/
theorem dependentIndexBaseChangeForward_naturalIso_endpoint
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    {earlier later : source.Elements}
    (route : earlier ⟶ later)
    (item : reindexedStructuredFutureIndex substitution domain later) :
    (StructuredArrow.proj (substitution.mapElements.obj earlier)
        (CategoryOfElements.π domain)).map
          ((dependentIndexBaseChangeForward_naturalIso
            substitution domain route).hom.app item) =
      𝟙 _ := by
  apply CategoryOfElements.ext domain
  rfl

/-- The forward comparison observes the original syntax arrow and
keeps the very same dependent evidence value. -/
theorem dependentIndexBaseChangeForward_retains
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements)
    (item : reindexedStructuredFutureIndex substitution domain point) :
    ((dependentIndexBaseChangeForward substitution domain point).obj item).hom.val =
        item.hom.val ∧
      ((dependentIndexBaseChangeForward substitution domain point).obj item).right.2 =
        item.right.2 :=
  ⟨rfl, rfl⟩

/-- The pointwise index comparison does not replace the authored syntax
arrow; it transports only the dependent argument at its endpoint. -/
theorem pointwisePiIndexBaseChangeEquiv_retains_route
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (point : source.Elements)
    (item : structuredFutureIndex substitution domain point) :
    ((pointwisePiIndexBaseChangeEquiv substitution domain point item).hom).val =
      item.hom.val := by
  rfl

#print axioms observedFutureElement_eq
#print axioms structuredElementToUnderElements
#print axioms underElementsToStructuredElement
#print axioms structuredElementUnderElementsEquivalence
#print axioms structuredElementToUnderElements_endpointIso
#print axioms dependentIndexBaseChangeForward
#print axioms dependentIndexBaseChangeEquivalence
#print axioms dependentIndexBaseChangeEquivalence_forward_obj
#print axioms dependentIndexBaseChangeEquivalence_forward_map
#print axioms dependentIndexBaseChangeEquivalence_functor_eq
#print axioms dependentIndexBaseChange_endpointDiagram
#print axioms dependentIndexBaseChangeForward_naturalIso
#print axioms dependentIndexBaseChangeForward_naturalIso_endpoint
#print axioms dependentIndexBaseChangeForward_retains
#print axioms structuredFutureIndexEquiv
#print axioms observedCommaObjectIndexEquiv
#print axioms futureIndexEquiv
#print axioms futureIndexEquiv_retains_route
#print axioms reindexedStructuredFutureIndexEquiv
#print axioms pointwisePiIndexBaseChangeEquiv
#print axioms pointwisePiIndexBaseChangeEquiv_retains_route

end Mettapedia.TypeTheory.PresheafPiIndexComparison
