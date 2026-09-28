import Mettapedia.OSLF.Syntax.CategoricalScopedEventBaseChange

/-!
# Canonical transport of scoped events along contravariant binder maps

Changing a binder object covariantly does not determine a map on arbitrary
event-valued functions. When a map from the new binder object back to the old
one is supplied, precomposition does determine such a map. It combines with
the event and endpoint maps to transport the actual pullback witness.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalScopedEventContravariantTransport

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalScopedEventPremise
open Mettapedia.OSLF.Binding.CategoricalScopedEventBaseChange

universe u v
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable {B X E Q B' X' E' Q' : D}

omit [HasPullbacks D] in
/-- Covariant codomain maps and contravariant binder maps commute in an
internal hom, including two successive changes of each kind. -/
theorem ihomMap_pre_comp {B'' Y Y' Y'' : D}
    (first : Y ⟶ Y') (second : Y' ⟶ Y'')
    (binderBack : B' ⟶ B) (nextBinderBack : B'' ⟶ B') :
    (ihom B).map (first ≫ second) ≫
        (MonoidalClosed.pre (nextBinderBack ≫ binderBack)).app Y'' =
      ((ihom B).map first ≫ (MonoidalClosed.pre binderBack).app Y') ≫
        ((ihom B').map second ≫
          (MonoidalClosed.pre nextBinderBack).app Y'') := by
  simp only [Functor.map_comp, MonoidalClosed.pre_map,
    NatTrans.comp_app, Category.assoc]
  have exchange := MonoidalClosed.pre_comm_ihom_map binderBack second
  have replacement := congrArg
    (fun arrow => (ihom B).map first ≫ arrow ≫
      (MonoidalClosed.pre nextBinderBack).app Y'') exchange
  simpa only [Category.assoc] using replacement.symm

/-- Source and target maps with an explicitly contravariant binder map.
The requested endpoint functions must commute with that precomposition. -/
structure StructuralMap (source : Request B X E Q)
    (target : Request B' X' E' Q') where
  binderBack : B' ⟶ B
  parameter : X ⟶ X'
  event : E ⟶ E'
  endpoint : Q ⟶ Q'
  endpoints_comm : event ≫ target.endpoints = source.endpoints ≫ endpoint
  request_comm : parameter ≫ target.required =
    source.required ≫ (ihom B).map endpoint ≫
      (MonoidalClosed.pre binderBack).app Q'

namespace StructuralMap

variable {source : Request B X E Q} {target : Request B' X' E' Q'}

/-- The unchanged request supplies the identity structural transport. -/
def id (source : Request B X E Q) : StructuralMap source source where
  binderBack := 𝟙 B
  parameter := 𝟙 X
  event := 𝟙 E
  endpoint := 𝟙 Q
  endpoints_comm := by simp
  request_comm := by simp

/-- Postcompose events, then precompose the binder. -/
def eventFunction (f : StructuralMap source target) :
    (ihom B).obj E ⟶ (ihom B').obj E' :=
  (ihom B).map f.event ≫ (MonoidalClosed.pre f.binderBack).app E'

/-- Apply the same contravariant binder map to endpoint functions. -/
def endpointFunction (f : StructuralMap source target) :
    (ihom B).obj Q ⟶ (ihom B').obj Q' :=
  (ihom B).map f.endpoint ≫ (MonoidalClosed.pre f.binderBack).app Q'

/-- A structural map supplies the contextual maps needed by the generic
pullback witness transport. -/
def toMap (f : StructuralMap source target) : Map source target where
  parameter := f.parameter
  eventFunction := f.eventFunction
  endpointFunction := f.endpointFunction
  endpoint_comm := by
    dsimp [eventFunction, endpointFunction]
    calc
      ((ihom B).map f.event ≫ (MonoidalClosed.pre f.binderBack).app E') ≫
          (ihom B').map target.endpoints =
        (ihom B).map f.event ≫
          ((ihom B).map target.endpoints ≫
            (MonoidalClosed.pre f.binderBack).app Q') := by
              rw [Category.assoc,
                MonoidalClosed.pre_comm_ihom_map]
      _ = (ihom B).map source.endpoints ≫
          ((ihom B).map f.endpoint ≫
            (MonoidalClosed.pre f.binderBack).app Q') := by
              rw [← Category.assoc, ← Functor.map_comp,
                f.endpoints_comm, Functor.map_comp, Category.assoc]
  request_comm := f.request_comm

omit [HasPullbacks D] in
/-- Canonical contextual transport fixes identity maps. -/
theorem toMap_id (source : Request B X E Q) :
    (id source).toMap = CategoricalScopedEventBaseChange.Map.id source := by
  apply CategoricalScopedEventBaseChange.Map.ext
  · rfl
  · change (ihom B).map (𝟙 E) ≫
      (MonoidalClosed.pre (𝟙 B)).app E = 𝟙 _
    simp
  · change (ihom B).map (𝟙 Q) ≫
      (MonoidalClosed.pre (𝟙 B)).app Q = 𝟙 _
    simp

variable {B'' X'' E'' Q'' : D}
variable {last : Request B'' X'' E'' Q''}

/-- Structural maps compose contravariantly on binder objects. -/
def comp (f : StructuralMap source target)
    (g : StructuralMap target last) : StructuralMap source last where
  binderBack := g.binderBack ≫ f.binderBack
  parameter := f.parameter ≫ g.parameter
  event := f.event ≫ g.event
  endpoint := f.endpoint ≫ g.endpoint
  endpoints_comm := by
    calc
      (f.event ≫ g.event) ≫ last.endpoints =
          f.event ≫ (g.event ≫ last.endpoints) := Category.assoc _ _ _
      _ = f.event ≫ (target.endpoints ≫ g.endpoint) := by
        rw [g.endpoints_comm]
      _ = (f.event ≫ target.endpoints) ≫ g.endpoint :=
        (Category.assoc _ _ _).symm
      _ = (source.endpoints ≫ f.endpoint) ≫ g.endpoint := by
        rw [f.endpoints_comm]
      _ = source.endpoints ≫ (f.endpoint ≫ g.endpoint) :=
        Category.assoc _ _ _
  request_comm := by
    calc
      (f.parameter ≫ g.parameter) ≫ last.required =
          f.parameter ≫ (g.parameter ≫ last.required) := Category.assoc _ _ _
      _ = f.parameter ≫
          (target.required ≫ (ihom B').map g.endpoint ≫
            (MonoidalClosed.pre g.binderBack).app Q'') := by
              rw [g.request_comm]
      _ = (source.required ≫ (ihom B).map f.endpoint ≫
            (MonoidalClosed.pre f.binderBack).app Q') ≫
          (ihom B').map g.endpoint ≫
            (MonoidalClosed.pre g.binderBack).app Q'' := by
              have congruent := congrArg
                (fun arrow => arrow ≫ (ihom B').map g.endpoint ≫
                  (MonoidalClosed.pre g.binderBack).app Q'')
                f.request_comm
              simpa only [Category.assoc] using congruent
      _ = source.required ≫
          (ihom B).map (f.endpoint ≫ g.endpoint) ≫
            (MonoidalClosed.pre (g.binderBack ≫ f.binderBack)).app Q'' := by
              simpa only [Category.assoc] using
                (congrArg (fun arrow => source.required ≫ arrow)
                  (ihomMap_pre_comp f.endpoint g.endpoint
                    f.binderBack g.binderBack)).symm

omit [HasPullbacks D] in
/-- The generic scoped witness transport composes exactly as the
contravariant binder, event, endpoint and parameter maps do. -/
theorem toMap_comp (f : StructuralMap source target)
    (g : StructuralMap target last) :
    (comp f g).toMap = CategoricalScopedEventBaseChange.Map.comp
      f.toMap g.toMap := by
  apply CategoricalScopedEventBaseChange.Map.ext
  · rfl
  · exact ihomMap_pre_comp f.event g.event f.binderBack g.binderBack
  · exact ihomMap_pre_comp f.endpoint g.endpoint f.binderBack g.binderBack

end StructuralMap

namespace StructuralMap

variable {source : Request B X E Q}
variable {target : Request B X' E' Q'}

/-- Existing fixed-binder premise maps are the identity-binder case of the
contravariant contextual transport. -/
def ofFixedBinder
    (f : CategoricalScopedEventPremise.Map source target) :
    StructuralMap source target where
  binderBack := 𝟙 B
  parameter := f.parameter
  event := f.event
  endpoint := f.endpoint
  endpoints_comm := f.endpoint_comm
  request_comm := by
    simpa [MonoidalClosed.pre_id] using f.required_comm

/-- The new changing-binder witness map agrees exactly with the existing
fixed-binder witness map when no binder change occurs. -/
theorem mapWitness_ofFixedBinder
    (f : CategoricalScopedEventPremise.Map source target) :
    CategoricalScopedEventBaseChange.mapWitness (ofFixedBinder f).toMap =
      CategoricalScopedEventPremise.mapWitness source f := by
  apply pullback.hom_ext
  · change
      CategoricalScopedEventBaseChange.mapWitness (ofFixedBinder f).toMap ≫
        CategoricalScopedEventPremise.event target =
      CategoricalScopedEventPremise.mapWitness source f ≫
        CategoricalScopedEventPremise.event target
    rw [CategoricalScopedEventBaseChange.mapWitness_event,
      CategoricalScopedEventPremise.mapWitness_event]
    simp [StructuralMap.toMap, StructuralMap.eventFunction,
      ofFixedBinder, MonoidalClosed.pre_id]
  · change
      CategoricalScopedEventBaseChange.mapWitness (ofFixedBinder f).toMap ≫
        CategoricalScopedEventPremise.parameters target =
      CategoricalScopedEventPremise.mapWitness source f ≫
        CategoricalScopedEventPremise.parameters target
    rw [CategoricalScopedEventBaseChange.mapWitness_parameters,
      CategoricalScopedEventPremise.mapWitness_parameters]
    rfl

end StructuralMap

end Mettapedia.OSLF.Binding.CategoricalScopedEventContravariantTransport
