import Mettapedia.OSLF.Syntax.CategoricalAuthoredOperationalModels

/-!
# Chosen reduction observations of authored operational models

Individual firings, a chosen reduction subobject, and the exact image of
event endpoints are three different structures. A chosen mono and a factor
through it need no image construction. Exactness becomes available when the
target has images; maps of observations need not reflect reductions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredReductionObservations

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation
open Mettapedia.OSLF.Binding.CategoricalAuthoredOperationalModels
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable {equations : EquationPresentation S schema}
variable {rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)}

/-- A chosen reduction predicate contains all authored event endpoints. It
may contain additional pairs, so this field alone does not assert exactness. -/
structure Observation (X : PresentedModel (D := D) equations rules) where
  reduction : D
  embedding : reduction ⟶ EndpointPairs X.base.binding X.base.carrier
  mono : Mono embedding
  factor : X.event ⟶ reduction
  factor_comm : factor ≫ embedding = X.endpoints

instance (X : PresentedModel (D := D) equations rules)
    (O : Observation X) : Mono O.embedding := O.mono

/-- An observation map is a square over the program-pair map of the
underlying operational interpretation. -/
structure ObservationMap {X Y : PresentedModel (D := D) equations rules}
    (f : PresentedModel.Hom X Y) (O : Observation X) (P : Observation Y) where
  reduction : O.reduction ⟶ P.reduction
  embedding_comm : reduction ≫ P.embedding =
    O.embedding ≫ f.base.endpointMap

/-- Once the chosen target observation is a subobject, its action on an
individual firing is forced by endpoint preservation. -/
theorem ObservationMap.factor_comm
    {X Y : PresentedModel (D := D) equations rules}
    {f : PresentedModel.Hom X Y}
    {O : Observation X} {P : Observation Y}
    (h : ObservationMap f O P) :
    f.event ≫ P.factor = O.factor ≫ h.reduction := by
  apply (cancel_mono P.embedding).mp
  calc
    (f.event ≫ P.factor) ≫ P.embedding =
      f.event ≫ (P.factor ≫ P.embedding) := Category.assoc _ _ _
    _ = f.event ≫ Y.endpoints := by rw [P.factor_comm]
    _ = X.endpoints ≫ f.base.endpointMap := f.endpoints_comm
    _ = (O.factor ≫ O.embedding) ≫ f.base.endpointMap := by
      rw [O.factor_comm]
    _ = O.factor ≫ (O.embedding ≫ f.base.endpointMap) :=
      Category.assoc _ _ _
    _ = O.factor ≫ (h.reduction ≫ P.embedding) := by
      rw [h.embedding_comm]
    _ = (O.factor ≫ h.reduction) ≫ P.embedding :=
      (Category.assoc _ _ _).symm

/-- Identity preserves a chosen reduction subobject. -/
noncomputable def ObservationMap.id
    {X : PresentedModel (D := D) equations rules}
    (O : Observation X) :
    ObservationMap (PresentedModel.Hom.id X) O O where
  reduction := 𝟙 O.reduction
  embedding_comm := by
    change (𝟙 O.reduction) ≫ O.embedding =
      O.embedding ≫ (CategoricalAuthoredProgramCarrierMaps.ModelWithPrograms.Hom.id
        X.base).endpointMap
    rw [CategoricalAuthoredProgramCarrierMaps.ModelWithPrograms.Hom.endpointMap_id]
    simp

/-- Observation squares compose along the same operational model maps. -/
noncomputable def ObservationMap.comp
    {X Y Z : PresentedModel (D := D) equations rules}
    {O : Observation X} {P : Observation Y} {Q : Observation Z}
    {f : PresentedModel.Hom X Y} {g : PresentedModel.Hom Y Z}
    (first : ObservationMap f O P)
    (second : ObservationMap g P Q) :
    ObservationMap (PresentedModel.Hom.comp f g) O Q where
  reduction := first.reduction ≫ second.reduction
  embedding_comm := by
    change (first.reduction ≫ second.reduction) ≫ Q.embedding =
      O.embedding ≫ (f.base.comp g.base).endpointMap
    rw [CategoricalAuthoredProgramCarrierMaps.ModelWithPrograms.Hom.endpointMap_comp]
    calc
      (first.reduction ≫ second.reduction) ≫ Q.embedding =
        first.reduction ≫ (second.reduction ≫ Q.embedding) :=
          Category.assoc _ _ _
      _ = first.reduction ≫ (P.embedding ≫ g.base.endpointMap) := by
        rw [second.embedding_comm]
      _ = (first.reduction ≫ P.embedding) ≫ g.base.endpointMap :=
        (Category.assoc _ _ _).symm
      _ = (O.embedding ≫ f.base.endpointMap) ≫ g.base.endpointMap := by
        rw [first.embedding_comm]
      _ = O.embedding ≫ (f.base.endpointMap ≫ g.base.endpointMap) :=
        Category.assoc _ _ _

/-- Operational models equipped with a chosen reduction subobject. -/
structure ObservedModel
    (equations : EquationPresentation S schema)
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)) where
  model : PresentedModel (D := D) equations rules
  observation : Observation model

namespace ObservedModel

variable {X Y Z : ObservedModel (D := D) equations rules}

structure Hom (X Y : ObservedModel (D := D) equations rules) where
  model : PresentedModel.Hom X.model Y.model
  observation : ObservationMap model X.observation Y.observation

noncomputable def Hom.id (X : ObservedModel (D := D) equations rules) :
    Hom X X where
  model := PresentedModel.Hom.id X.model
  observation := ObservationMap.id X.observation

noncomputable def Hom.comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  model := PresentedModel.Hom.comp f.model g.model
  observation := ObservationMap.comp f.observation g.observation

@[ext] theorem Hom.ext_of_components {f g : Hom X Y}
    (model : f.model = g.model)
    (reduction : f.observation.reduction =
      g.observation.reduction) : f = g := by
  cases f with
  | mk firstModel firstObservation =>
    cases g with
    | mk secondModel secondObservation =>
      dsimp at model reduction
      cases model
      cases firstObservation with
      | mk firstReduction firstLaw =>
        cases secondObservation with
        | mk secondReduction secondLaw =>
          dsimp at reduction
          cases reduction
          rfl

noncomputable instance : Category (ObservedModel (D := D) equations rules) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro X Y f
    apply Hom.ext_of_components
    · exact PresentedModel.Hom.id_comp f.model
    · exact Category.id_comp f.observation.reduction
  comp_id := by
    intro X Y f
    apply Hom.ext_of_components
    · exact PresentedModel.Hom.comp_id f.model
    · exact Category.comp_id f.observation.reduction
  assoc := by
    intro W X Y Z f g h
    apply Hom.ext_of_components
    · exact PresentedModel.Hom.comp_assoc f.model g.model h.model
    · exact Category.assoc f.observation.reduction
        g.observation.reduction h.observation.reduction

end ObservedModel

/-- Images supply the smallest chosen observation when the target supports
them. The event object and its individual witnesses are still retained. -/
noncomputable def imageObservation [HasImages D]
    (X : PresentedModel (D := D) equations rules) : Observation X where
  reduction := PresentedModel.reductionImage X
  embedding := PresentedModel.reductionMono X
  mono := by
    change Mono (image.ι X.endpoints)
    infer_instance
  factor := factorThruImage X.endpoints
  factor_comm := PresentedModel.event_factors_reduction X

/-- The whole endpoint-pair object is always a lawful chosen reduction
subobject. This shows why factoring events alone cannot prove exactness. -/
def topObservation
    (X : PresentedModel (D := D) equations rules) : Observation X where
  reduction := EndpointPairs X.base.binding X.base.carrier
  embedding := 𝟙 _
  mono := inferInstance
  factor := X.endpoints
  factor_comm := by simp

/-- A model with no firing events makes the distinction concrete: its top
observation can contain a pair, while no event realizes any pair. -/
noncomputable def noEventModel
    (base : CategoricalAuthoredProgramCarrierMaps.ModelWithPrograms S (Type u))
    (satisfies : base.binding.Satisfies equations) :
    PresentedModel (D := Type u) equations [] where
  base := base
  satisfies := satisfies
  event := PEmpty
  endpoints := _root_.TypeCat.ofHom PEmpty.elim
  action index := Fin.elim0 index

theorem noEventModel_top_unrealized
    (base : CategoricalAuthoredProgramCarrierMaps.ModelWithPrograms S (Type u))
    (satisfies : base.binding.Satisfies equations)
    (pair : EndpointPairs base.binding base.carrier) :
    ¬ ∃ firing : (noEventModel base satisfies).event,
      (noEventModel base satisfies).endpoints firing = pair := by
  rintro ⟨firing, _⟩
  exact firing.elim

theorem noEventModel_top_accepts_pair
    (base : CategoricalAuthoredProgramCarrierMaps.ModelWithPrograms S (Type u))
    (satisfies : base.binding.Satisfies equations)
    (pair : EndpointPairs base.binding base.carrier) :
    ∃ observed : (topObservation (noEventModel base satisfies)).reduction,
      (topObservation (noEventModel base satisfies)).embedding observed = pair := by
  refine ⟨pair, ?_⟩
  change (𝟙 (EndpointPairs base.binding base.carrier)) pair = pair
  exact _root_.CategoryTheory.types_id_apply _ pair

/-- The canonical image observations move forward along model maps in a
target that supports image maps. This does not assert pointwise reflection. -/
noncomputable def imageObservationMap [HasImages D] [HasImageMaps D]
    {X Y : PresentedModel (D := D) equations rules}
    (f : PresentedModel.Hom X Y) :
    ObservationMap f (imageObservation X) (imageObservation Y) where
  reduction := image.map f.endpointSquare
  embedding_comm := PresentedModel.reductionImage_forward f

/-- Taking the exact image is functorial when the target supplies image
maps. It adds an observation to a model without erasing its firing events. -/
noncomputable def imageObservationFunctor [HasImages D] [HasImageMaps D] :
    PresentedModel (D := D) equations rules ⥤
      ObservedModel (D := D) equations rules where
  obj X := ⟨X, imageObservation X⟩
  map f := ⟨f, imageObservationMap f⟩
  map_id X := by
    apply ObservedModel.Hom.ext_of_components
    · rfl
    · change image.map (PresentedModel.Hom.id X).endpointSquare =
        𝟙 (image X.endpoints)
      rw [PresentedModel.Hom.endpointSquare_id, image.map_id]
      rfl
  map_comp f g := by
    apply ObservedModel.Hom.ext_of_components
    · rfl
    · change image.map (PresentedModel.Hom.comp f g).endpointSquare =
        image.map f.endpointSquare ≫ image.map g.endpointSquare
      rw [PresentedModel.Hom.endpointSquare_comp, image.map_comp]

end Mettapedia.OSLF.Binding.CategoricalAuthoredReductionObservations
