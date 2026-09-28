import Mettapedia.OSLF.Syntax.CategoricalScopedEventPremise

/-!
# Scoped event witnesses under a change of binder context

An interpretation can change the object of local binders. A map of event
objects alone does not determine how a function of the old binder object
extends to a function of the new one. The contextual function maps below are
therefore explicit parts of the interpretation, with endpoint and request
compatibility laws. Pullback witnesses then transport functorially.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalScopedEventBaseChange

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalScopedEventPremise

universe u v
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable {B X E Q B' X' E' Q' : D}

/-- A binder inclusion used to test whether an old contextual event
function uniquely determines its interpretation at new binder values. -/
def includeBinder (_ : PUnit) : Bool := false

/-- One extension keeps the old event value at every new binder value. -/
def constantExtension (event : PUnit → Bool) (_ : Bool) : Bool :=
  event PUnit.unit

/-- Another extension agrees on the old binder but changes a new value. -/
def varyingExtension (event : PUnit → Bool) (binder : Bool) : Bool :=
  if binder then !(event PUnit.unit) else event PUnit.unit

theorem extensions_agree_on_old_binder (event : PUnit → Bool)
    (binder : PUnit) :
    constantExtension event (includeBinder binder) =
      varyingExtension event (includeBinder binder) := by
  rfl

/-- Agreement after the binder inclusion does not select a unique map on
contextual event functions. The additional transport is genuine data. -/
theorem extensions_differ :
    constantExtension (fun _ => false) ≠
      varyingExtension (fun _ => false) := by
  intro same
  have atNew := congrFun same true
  simp [constantExtension, varyingExtension] at atNew

/-- A map of scoped-premise requests may change the binder object. Its
contextual event and endpoint maps are explicit because a noninvertible
binder map does not determine an extension of every source function. -/
structure Map (source : Request B X E Q)
    (target : Request B' X' E' Q') where
  parameter : X ⟶ X'
  eventFunction : (ihom B).obj E ⟶ (ihom B').obj E'
  endpointFunction : (ihom B).obj Q ⟶ (ihom B').obj Q'
  endpoint_comm :
    eventFunction ≫ (ihom B').map target.endpoints =
      (ihom B).map source.endpoints ≫ endpointFunction
  request_comm : parameter ≫ target.required =
    source.required ≫ endpointFunction

variable {source : Request B X E Q}
  {target : Request B' X' E' Q'}

/-- Transport a firing function under a changed binder context while
retaining the individual event-function witness. -/
noncomputable def mapWitness (f : Map source target) :
    Witness source ⟶ Witness target := by
  apply assemble target
    (event source ≫ f.eventFunction)
    (parameters source ≫ f.parameter)
  calc
    (event source ≫ f.eventFunction) ≫
        (ihom B').map target.endpoints =
      event source ≫
        (f.eventFunction ≫ (ihom B').map target.endpoints) :=
          Category.assoc _ _ _
    _ = event source ≫
          ((ihom B).map source.endpoints ≫ f.endpointFunction) := by
            rw [f.endpoint_comm]
    _ = (event source ≫ (ihom B).map source.endpoints) ≫
          f.endpointFunction := (Category.assoc _ _ _).symm
    _ = (parameters source ≫ source.required) ≫
          f.endpointFunction := by rw [endpoint_condition source]
    _ = parameters source ≫
          (source.required ≫ f.endpointFunction) :=
            Category.assoc _ _ _
    _ = parameters source ≫
          (f.parameter ≫ target.required) := by
            rw [← f.request_comm]
    _ = (parameters source ≫ f.parameter) ≫
          target.required := (Category.assoc _ _ _).symm

theorem mapWitness_event (f : Map source target) :
    mapWitness f ≫ event target = event source ≫ f.eventFunction :=
  assemble_event target _ _ _

theorem mapWitness_parameters (f : Map source target) :
    mapWitness f ≫ parameters target =
      parameters source ≫ f.parameter :=
  assemble_parameters target _ _ _

namespace Map

variable {B'' X'' E'' Q'' : D}
  {first : Request B X E Q}
  {middle : Request B' X' E' Q'}
  {last : Request B'' X'' E'' Q''}

omit [HasPullbacks D] in
@[ext] theorem ext {f g : Map first middle}
    (parameter : f.parameter = g.parameter)
    (eventFunction : f.eventFunction = g.eventFunction)
    (endpointFunction : f.endpointFunction = g.endpointFunction) :
    f = g := by
  cases f
  cases g
  cases parameter
  cases eventFunction
  cases endpointFunction
  rfl

omit [HasPullbacks D] in
/-- Identity changes neither the binder context nor any event function. -/
def id (first : Request B X E Q) : Map first first where
  parameter := 𝟙 X
  eventFunction := 𝟙 _
  endpointFunction := 𝟙 _
  endpoint_comm := by simp
  request_comm := by simp

omit [HasPullbacks D] in
/-- Composition retains the explicit contextual function transport. -/
def comp (f : Map first middle) (g : Map middle last) :
    Map first last where
  parameter := f.parameter ≫ g.parameter
  eventFunction := f.eventFunction ≫ g.eventFunction
  endpointFunction := f.endpointFunction ≫ g.endpointFunction
  endpoint_comm := by
    calc
      (f.eventFunction ≫ g.eventFunction) ≫
          (ihom B'').map last.endpoints =
        f.eventFunction ≫
          (g.eventFunction ≫ (ihom B'').map last.endpoints) :=
            Category.assoc _ _ _
      _ = f.eventFunction ≫
            ((ihom B').map middle.endpoints ≫ g.endpointFunction) := by
              rw [g.endpoint_comm]
      _ = (f.eventFunction ≫ (ihom B').map middle.endpoints) ≫
            g.endpointFunction := (Category.assoc _ _ _).symm
      _ = ((ihom B).map first.endpoints ≫ f.endpointFunction) ≫
            g.endpointFunction := by rw [f.endpoint_comm]
      _ = (ihom B).map first.endpoints ≫
            (f.endpointFunction ≫ g.endpointFunction) :=
              Category.assoc _ _ _
  request_comm := by
    calc
      (f.parameter ≫ g.parameter) ≫ last.required =
        f.parameter ≫ (g.parameter ≫ last.required) :=
          Category.assoc _ _ _
      _ = f.parameter ≫
            (middle.required ≫ g.endpointFunction) := by
              rw [g.request_comm]
      _ = (f.parameter ≫ middle.required) ≫ g.endpointFunction :=
            (Category.assoc _ _ _).symm
      _ = (first.required ≫ f.endpointFunction) ≫
            g.endpointFunction := by rw [f.request_comm]
      _ = first.required ≫
            (f.endpointFunction ≫ g.endpointFunction) :=
              Category.assoc _ _ _

omit [HasPullbacks D] in
theorem id_comp (f : Map first middle) :
    comp (id first) f = f := by
  apply ext <;> simp [comp, id]

omit [HasPullbacks D] in
theorem comp_id (f : Map first middle) :
    comp f (id middle) = f := by
  apply ext <;> simp [comp, id]

omit [HasPullbacks D] in
theorem comp_assoc {B''' X''' E''' Q''' : D}
    {fourth : Request B''' X''' E''' Q'''}
    (f : Map first middle) (g : Map middle last)
    (h : Map last fourth) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext <;> simp [comp, Category.assoc]

end Map

/-- Identity transport fixes the complete scoped firing witness. -/
theorem mapWitness_id (source : Request B X E Q) :
    mapWitness (Map.id source) = 𝟙 (Witness source) := by
  apply pullback.hom_ext
  · change mapWitness (Map.id source) ≫ event source =
        𝟙 (Witness source) ≫ event source
    rw [mapWitness_event]
    simp [Map.id]
  · change mapWitness (Map.id source) ≫ parameters source =
        𝟙 (Witness source) ≫ parameters source
    rw [mapWitness_parameters]
    simp [Map.id]

/-- Contextual witness transport respects composition, even when each
stage has a different binder object. -/
theorem mapWitness_comp {B'' X'' E'' Q'' : D}
    {middle : Request B' X' E' Q'}
    {last : Request B'' X'' E'' Q''}
    (f : Map source middle) (g : Map middle last) :
    mapWitness (Map.comp f g) = mapWitness f ≫ mapWitness g := by
  apply pullback.hom_ext
  · change mapWitness (Map.comp f g) ≫ event last =
        (mapWitness f ≫ mapWitness g) ≫ event last
    rw [mapWitness_event, Category.assoc, mapWitness_event]
    rw [← Category.assoc, mapWitness_event]
    simp [Map.comp, Category.assoc]
  · change mapWitness (Map.comp f g) ≫ parameters last =
        (mapWitness f ≫ mapWitness g) ≫ parameters last
    rw [mapWitness_parameters, Category.assoc,
      mapWitness_parameters]
    rw [← Category.assoc, mapWitness_parameters]
    simp [Map.comp, Category.assoc]

/-- The earlier fixed-binder request map is a special case of contextual
base change, using functorial postcomposition on internal homs. -/
def ofFixed {X' E' Q' : D}
    {source : Request B X E Q}
    {target : Request B X' E' Q'}
    (f : CategoricalScopedEventPremise.Map source target) :
    Map source target where
  parameter := f.parameter
  eventFunction := (ihom B).map f.event
  endpointFunction := (ihom B).map f.endpoint
  endpoint_comm := by
    simp only [← Functor.map_comp]
    rw [f.endpoint_comm]
  request_comm := f.required_comm

omit [HasPullbacks D] in
/-- Fixed-binder identity embeds as contextual identity. -/
theorem ofFixed_id (source : Request B X E Q) :
    ofFixed (CategoricalScopedEventPremise.Map.id source) =
      Map.id source := by
  apply Map.ext <;> simp [ofFixed,
    CategoricalScopedEventPremise.Map.id, Map.id]

omit [HasPullbacks D] in
/-- Fixed-binder composition embeds as contextual composition. -/
theorem ofFixed_comp {X₂ E₂ Q₂ X₃ E₃ Q₃ : D}
    {middle : Request B X₂ E₂ Q₂}
    {last : Request B X₃ E₃ Q₃}
    (f : CategoricalScopedEventPremise.Map source middle)
    (g : CategoricalScopedEventPremise.Map middle last) :
    ofFixed (CategoricalScopedEventPremise.Map.comp f g) =
      Map.comp (ofFixed f) (ofFixed g) := by
  apply Map.ext <;> simp [ofFixed,
    CategoricalScopedEventPremise.Map.comp, Map.comp,
    Functor.map_comp]

/-- The generalized transport agrees exactly with the established
fixed-binder witness map, rather than defining a second interpretation. -/
theorem mapWitness_ofFixed {X' E' Q' : D}
    {source : Request B X E Q}
    {target : Request B X' E' Q'}
    (f : CategoricalScopedEventPremise.Map source target) :
    mapWitness (ofFixed f) =
      CategoricalScopedEventPremise.mapWitness source f := by
  apply pullback.hom_ext
  · change mapWitness (ofFixed f) ≫ event target =
        CategoricalScopedEventPremise.mapWitness source f ≫ event target
    rw [mapWitness_event,
      CategoricalScopedEventPremise.mapWitness_event]
    rfl
  · change mapWitness (ofFixed f) ≫ parameters target =
        CategoricalScopedEventPremise.mapWitness source f ≫ parameters target
    rw [mapWitness_parameters,
      CategoricalScopedEventPremise.mapWitness_parameters]
    rfl

/-- A contextual request map is pointwise over maps of binder, event and
endpoint objects when its function maps agree with evaluation on source
binder values. This extra law prevents unrelated extensions on the image
of the old binder from masquerading as operational interpretations. -/
structure PointwiseMap (source : Request B X E Q)
    (target : Request B' X' E' Q') where
  contextual : Map source target
  binder : B ⟶ B'
  event : E ⟶ E'
  endpoint : Q ⟶ Q'
  event_eval :
    (binder ⊗ₘ contextual.eventFunction) ≫
        (ihom.ev B').app E' =
      (ihom.ev B).app E ≫ event
  endpoint_eval :
    (binder ⊗ₘ contextual.endpointFunction) ≫
        (ihom.ev B').app Q' =
      (ihom.ev B).app Q ≫ endpoint
  endpoint_comm : event ≫ target.endpoints =
    source.endpoints ≫ endpoint

namespace PointwiseMap

variable {B'' X'' E'' Q'' : D}
  {first : Request B X E Q}
  {middle : Request B' X' E' Q'}
  {last : Request B'' X'' E'' Q''}

omit [HasPullbacks D] in
@[ext] theorem ext {f g : PointwiseMap first middle}
    (contextual : f.contextual = g.contextual)
    (binder : f.binder = g.binder)
    (event : f.event = g.event)
    (endpoint : f.endpoint = g.endpoint) : f = g := by
  cases f
  cases g
  cases contextual
  cases binder
  cases event
  cases endpoint
  rfl

/-- Identity interpretation is pointwise on binder, event and endpoints. -/
def id (first : Request B X E Q) : PointwiseMap first first where
  contextual := Map.id first
  binder := 𝟙 B
  event := 𝟙 E
  endpoint := 𝟙 Q
  event_eval := by simp [Map.id]
  endpoint_eval := by simp [Map.id]
  endpoint_comm := by simp

/-- Pointwise scoped maps compose over the actual binder and event maps. -/
def comp (f : PointwiseMap first middle)
    (g : PointwiseMap middle last) : PointwiseMap first last where
  contextual := Map.comp f.contextual g.contextual
  binder := f.binder ≫ g.binder
  event := f.event ≫ g.event
  endpoint := f.endpoint ≫ g.endpoint
  event_eval := by
    calc
      ((f.binder ≫ g.binder) ⊗ₘ
          (f.contextual.eventFunction ≫ g.contextual.eventFunction)) ≫
          (ihom.ev B'').app E'' =
        ((f.binder ⊗ₘ f.contextual.eventFunction) ≫
          (g.binder ⊗ₘ g.contextual.eventFunction)) ≫
          (ihom.ev B'').app E'' := by
            rw [tensorHom_comp_tensorHom]
      _ = (f.binder ⊗ₘ f.contextual.eventFunction) ≫
            ((g.binder ⊗ₘ g.contextual.eventFunction) ≫
              (ihom.ev B'').app E'') := Category.assoc _ _ _
      _ = (f.binder ⊗ₘ f.contextual.eventFunction) ≫
            ((ihom.ev B').app E' ≫ g.event) := by
              rw [g.event_eval]
      _ = ((f.binder ⊗ₘ f.contextual.eventFunction) ≫
            (ihom.ev B').app E') ≫ g.event :=
          (Category.assoc _ _ _).symm
      _ = ((ihom.ev B).app E ≫ f.event) ≫ g.event := by
            rw [f.event_eval]
      _ = (ihom.ev B).app E ≫ (f.event ≫ g.event) :=
          Category.assoc _ _ _
  endpoint_eval := by
    calc
      ((f.binder ≫ g.binder) ⊗ₘ
          (f.contextual.endpointFunction ≫ g.contextual.endpointFunction)) ≫
          (ihom.ev B'').app Q'' =
        ((f.binder ⊗ₘ f.contextual.endpointFunction) ≫
          (g.binder ⊗ₘ g.contextual.endpointFunction)) ≫
          (ihom.ev B'').app Q'' := by
            rw [tensorHom_comp_tensorHom]
      _ = (f.binder ⊗ₘ f.contextual.endpointFunction) ≫
            ((g.binder ⊗ₘ g.contextual.endpointFunction) ≫
              (ihom.ev B'').app Q'') := Category.assoc _ _ _
      _ = (f.binder ⊗ₘ f.contextual.endpointFunction) ≫
            ((ihom.ev B').app Q' ≫ g.endpoint) := by
              rw [g.endpoint_eval]
      _ = ((f.binder ⊗ₘ f.contextual.endpointFunction) ≫
            (ihom.ev B').app Q') ≫ g.endpoint :=
          (Category.assoc _ _ _).symm
      _ = ((ihom.ev B).app Q ≫ f.endpoint) ≫ g.endpoint := by
            rw [f.endpoint_eval]
      _ = (ihom.ev B).app Q ≫ (f.endpoint ≫ g.endpoint) :=
          Category.assoc _ _ _
  endpoint_comm := by
    calc
      (f.event ≫ g.event) ≫ last.endpoints =
        f.event ≫ (g.event ≫ last.endpoints) := Category.assoc _ _ _
      _ = f.event ≫ (middle.endpoints ≫ g.endpoint) := by
            rw [g.endpoint_comm]
      _ = (f.event ≫ middle.endpoints) ≫ g.endpoint :=
          (Category.assoc _ _ _).symm
      _ = (first.endpoints ≫ f.endpoint) ≫ g.endpoint := by
            rw [f.endpoint_comm]
      _ = first.endpoints ≫ (f.endpoint ≫ g.endpoint) :=
          Category.assoc _ _ _

omit [HasPullbacks D] in
theorem id_comp (f : PointwiseMap first middle) :
    comp (id first) f = f := by
  apply ext
  · exact Map.id_comp f.contextual
  · simp [comp, id]
  · simp [comp, id]
  · simp [comp, id]

omit [HasPullbacks D] in
theorem comp_id (f : PointwiseMap first middle) :
    comp f (id middle) = f := by
  apply ext
  · exact Map.comp_id f.contextual
  · simp [comp, id]
  · simp [comp, id]
  · simp [comp, id]

omit [HasPullbacks D] in
theorem comp_assoc {B''' X''' E''' Q''' : D}
    {fourth : Request B''' X''' E''' Q'''}
    (f : PointwiseMap first middle)
    (g : PointwiseMap middle last)
    (h : PointwiseMap last fourth) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  · exact Map.comp_assoc f.contextual g.contextual h.contextual
  · exact Category.assoc f.binder g.binder h.binder
  · exact Category.assoc f.event g.event h.event
  · exact Category.assoc f.endpoint g.endpoint h.endpoint

end PointwiseMap

/-- The established fixed-binder map is pointwise over the identity binder
map and its original event and endpoint arrows. -/
def pointwiseOfFixed {X' E' Q' : D}
    {source : Request B X E Q}
    {target : Request B X' E' Q'}
    (f : CategoricalScopedEventPremise.Map source target) :
    PointwiseMap source target where
  contextual := ofFixed f
  binder := 𝟙 B
  event := f.event
  endpoint := f.endpoint
  event_eval := by
    change (𝟙 B ⊗ₘ (ihom B).map f.event) ≫
        (ihom.ev B).app E' = (ihom.ev B).app E ≫ f.event
    rw [id_tensorHom]
    exact ihom.ev_naturality B f.event
  endpoint_eval := by
    change (𝟙 B ⊗ₘ (ihom B).map f.endpoint) ≫
        (ihom.ev B).app Q' = (ihom.ev B).app Q ≫ f.endpoint
    rw [id_tensorHom]
    exact ihom.ev_naturality B f.endpoint
  endpoint_comm := f.endpoint_comm

end Mettapedia.OSLF.Binding.CategoricalScopedEventBaseChange

#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventBaseChange.mapWitness_comp
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventBaseChange.mapWitness_ofFixed
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventBaseChange.ofFixed_comp
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventBaseChange.extensions_differ
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventBaseChange.PointwiseMap.comp
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventBaseChange.pointwiseOfFixed
