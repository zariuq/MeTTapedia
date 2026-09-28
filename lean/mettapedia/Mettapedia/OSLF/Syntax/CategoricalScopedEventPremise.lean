import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# A binder-local operational premise in a closed target

A scoped premise asks for an individual event under a binder object `B`,
whose source and target agree with a requested pair of program functions.
The pullback below enforces that endpoint condition while retaining the
event function itself. It works in any closed target with pullbacks; image
factorizations and a truth classifier are not required.

This describes the target-side object for one premise. Interpreting an
authored rule requires a morphism from its full ordered premise domain to
the target event object, compatible with the declared conclusion and
substitution. Such rule actions belong to the operational model contract.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalScopedEventPremise

open CategoryTheory CategoryTheory.Limits

universe u v

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]

/-- A requested binder-local endpoint function and the endpoint map of
individual events. The endpoint codomain may be a program-pair object. -/
structure Request (B X E Q : D) where
  endpoints : E ⟶ Q
  required : X ⟶ (ihom B).obj Q

variable {B X E Q : D} (request : Request B X E Q)

/-- Witnesses are scoped event functions over a parameter assignment whose
observed endpoints agree with the premise's requested functions. -/
noncomputable abbrev Witness : D :=
  pullback ((ihom B).map request.endpoints) request.required

/-- The retained event function of a scoped premise witness. -/
noncomputable def event : Witness request ⟶ (ihom B).obj E :=
  pullback.fst _ _

/-- The ambient parameter assignment of a scoped premise witness. -/
noncomputable def parameters : Witness request ⟶ X :=
  pullback.snd _ _

/-- The event function has exactly the requested endpoint function. -/
theorem endpoint_condition :
    event request ≫ (ihom B).map request.endpoints =
      parameters request ≫ request.required :=
  pullback.condition

/-- An event function and parameter assignment satisfying the endpoint
condition determine one witness. -/
noncomputable def assemble {Z : D} (candidate : Z ⟶ (ihom B).obj E)
    (assignment : Z ⟶ X)
    (agrees : candidate ≫ (ihom B).map request.endpoints =
      assignment ≫ request.required) : Z ⟶ Witness request :=
  pullback.lift candidate assignment agrees

theorem assemble_event {Z : D} (candidate : Z ⟶ (ihom B).obj E)
    (assignment : Z ⟶ X)
    (agrees : candidate ≫ (ihom B).map request.endpoints =
      assignment ≫ request.required) :
    assemble request candidate assignment agrees ≫ event request = candidate :=
  pullback.lift_fst _ _ _

theorem assemble_parameters {Z : D} (candidate : Z ⟶ (ihom B).obj E)
    (assignment : Z ⟶ X)
    (agrees : candidate ≫ (ihom B).map request.endpoints =
      assignment ≫ request.required) :
    assemble request candidate assignment agrees ≫ parameters request = assignment :=
  pullback.lift_snd _ _ _

/-- This universal property states the exact independent target data of
one binder-local event premise, including maps from any test object. -/
noncomputable def witnessEquiv (Z : D) :
    (Z ⟶ Witness request) ≃
      {pair : (Z ⟶ (ihom B).obj E) × (Z ⟶ X) //
        pair.1 ≫ (ihom B).map request.endpoints =
          pair.2 ≫ request.required} where
  toFun witness :=
    ⟨⟨witness ≫ event request, witness ≫ parameters request⟩, by
      rw [Category.assoc, Category.assoc, endpoint_condition request]⟩
  invFun pair := assemble request pair.1.1 pair.1.2 pair.2
  left_inv witness := by
    apply pullback.hom_ext
    · simp only [assemble, event, pullback.lift_fst]
    · simp only [assemble, parameters, pullback.lift_snd]
  right_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · exact assemble_event request pair.1.1 pair.1.2 pair.2
    · exact assemble_parameters request pair.1.1 pair.1.2 pair.2

/-- The construction retains distinct individual scoped events even when
their endpoint functions coincide. Applying the event projection recovers
the distinction. -/
theorem assemble_injective_event {Z : D}
    {first second : Z ⟶ (ihom B).obj E}
    {assignment : Z ⟶ X}
    (firstAgrees : first ≫ (ihom B).map request.endpoints =
      assignment ≫ request.required)
    (secondAgrees : second ≫ (ihom B).map request.endpoints =
      assignment ≫ request.required)
    (different : first ≠ second) :
    assemble request first assignment firstAgrees ≠
      assemble request second assignment secondAgrees := by
  intro same
  apply different
  have projected := congrArg (fun arrow => arrow ≫ event request) same
  simpa [assemble_event] using projected

/-- A map of scoped premise requests preserves the parameter assignment,
the individual event and its endpoint observation. Neither injectivity nor
coverage of target events is part of an ordinary interpretation map. -/
structure Map {X' E' Q' : D} (target : Request B X' E' Q') where
  parameter : X ⟶ X'
  event : E ⟶ E'
  endpoint : Q ⟶ Q'
  endpoint_comm : event ≫ target.endpoints =
    request.endpoints ≫ endpoint
  required_comm : parameter ≫ target.required =
    request.required ≫ (ihom B).map endpoint

/-- Transport a scoped firing through a model map without discarding its
event function. The endpoint condition follows from the two commuting
squares in the map contract. -/
noncomputable def mapWitness {X' E' Q' : D}
    {target : Request B X' E' Q'} (f : Map request target) :
    Witness request ⟶ Witness target := by
  apply assemble target
    (event request ≫ (ihom B).map f.event)
    (parameters request ≫ f.parameter)
  calc
    (event request ≫ (ihom B).map f.event) ≫
        (ihom B).map target.endpoints =
      event request ≫ (ihom B).map
        (f.event ≫ target.endpoints) := by
          simp only [Category.assoc, ← Functor.map_comp]
    _ = event request ≫ (ihom B).map
        (request.endpoints ≫ f.endpoint) := by rw [f.endpoint_comm]
    _ = (event request ≫ (ihom B).map request.endpoints) ≫
        (ihom B).map f.endpoint := by
          simp only [Category.assoc, Functor.map_comp]
    _ = (parameters request ≫ request.required) ≫
        (ihom B).map f.endpoint := by rw [endpoint_condition request]
    _ = (parameters request ≫ f.parameter) ≫
        target.required := by
          calc
            (parameters request ≫ request.required) ≫
                (ihom B).map f.endpoint =
              parameters request ≫
                (request.required ≫ (ihom B).map f.endpoint) :=
                  Category.assoc _ _ _
            _ = parameters request ≫
                (f.parameter ≫ target.required) := by
                  rw [← f.required_comm]
            _ = (parameters request ≫ f.parameter) ≫ target.required :=
                  (Category.assoc _ _ _).symm

theorem mapWitness_event {X' E' Q' : D}
    {target : Request B X' E' Q'} (f : Map request target) :
    mapWitness request f ≫ event target =
      event request ≫ (ihom B).map f.event :=
  assemble_event target _ _ _

theorem mapWitness_parameters {X' E' Q' : D}
    {target : Request B X' E' Q'} (f : Map request target) :
    mapWitness request f ≫ parameters target =
      parameters request ≫ f.parameter :=
  assemble_parameters target _ _ _

namespace Map

variable {X₁ E₁ Q₁ X₂ E₂ Q₂ X₃ E₃ Q₃ : D}
  {first : Request B X₁ E₁ Q₁}
  {middle : Request B X₂ E₂ Q₂}
  {last : Request B X₃ E₃ Q₃}

omit [HasPullbacks D] in
@[ext] theorem ext {f g : Map first middle}
    (parameter : f.parameter = g.parameter)
    (event : f.event = g.event)
    (endpoint : f.endpoint = g.endpoint) : f = g := by
  cases f
  cases g
  cases parameter
  cases event
  cases endpoint
  rfl

/-- Identity interpretation of a scoped premise request. -/
def id (first : Request B X₁ E₁ Q₁) : Map first first where
  parameter := 𝟙 X₁
  event := 𝟙 E₁
  endpoint := 𝟙 Q₁
  endpoint_comm := by simp
  required_comm := by simp

/-- Compose ordinary premise interpretations, retaining both event maps. -/
def comp (f : Map first middle) (g : Map middle last) :
    Map first last where
  parameter := f.parameter ≫ g.parameter
  event := f.event ≫ g.event
  endpoint := f.endpoint ≫ g.endpoint
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
  required_comm := by
    calc
      (f.parameter ≫ g.parameter) ≫ last.required =
        f.parameter ≫ (g.parameter ≫ last.required) :=
          Category.assoc _ _ _
      _ = f.parameter ≫
          (middle.required ≫ (ihom B).map g.endpoint) := by
            rw [g.required_comm]
      _ = (f.parameter ≫ middle.required) ≫
          (ihom B).map g.endpoint := (Category.assoc _ _ _).symm
      _ = (first.required ≫ (ihom B).map f.endpoint) ≫
          (ihom B).map g.endpoint := by rw [f.required_comm]
      _ = first.required ≫ (ihom B).map (f.endpoint ≫ g.endpoint) := by
            simp only [Category.assoc, Functor.map_comp]

end Map

/-- The scope-witness action of an identity model map is identity. -/
theorem mapWitness_id :
    mapWitness request (Map.id request) = 𝟙 (Witness request) := by
  apply pullback.hom_ext
  · change mapWitness request (Map.id request) ≫ event request =
        𝟙 (Witness request) ≫ event request
    rw [mapWitness_event]
    simp [Map.id]
  · change mapWitness request (Map.id request) ≫ parameters request =
        𝟙 (Witness request) ≫ parameters request
    rw [mapWitness_parameters]
    simp [Map.id]

/-- Scope-witness transport composes on the individual event function and
the parameter assignment. -/
theorem mapWitness_comp {X₂ E₂ Q₂ X₃ E₃ Q₃ : D}
    {middle : Request B X₂ E₂ Q₂}
    {last : Request B X₃ E₃ Q₃}
    (f : Map request middle) (g : Map middle last) :
    mapWitness request (Map.comp f g) =
      mapWitness request f ≫ mapWitness middle g := by
  apply pullback.hom_ext
  · change mapWitness request (Map.comp f g) ≫ event last =
        (mapWitness request f ≫ mapWitness middle g) ≫ event last
    calc
      mapWitness request (Map.comp f g) ≫ event last =
          event request ≫ (ihom B).map (f.event ≫ g.event) :=
            mapWitness_event request (Map.comp f g)
      _ = (event request ≫ (ihom B).map f.event) ≫
          (ihom B).map g.event := by
            rw [Functor.map_comp]
            exact (Category.assoc _ _ _).symm
      _ = (mapWitness request f ≫ event middle) ≫
          (ihom B).map g.event := by rw [mapWitness_event]
      _ = mapWitness request f ≫
          (event middle ≫ (ihom B).map g.event) :=
            Category.assoc _ _ _
      _ = mapWitness request f ≫
          (mapWitness middle g ≫ event last) := by
            rw [mapWitness_event middle g]
      _ = (mapWitness request f ≫ mapWitness middle g) ≫
          event last := (Category.assoc _ _ _).symm
  · change mapWitness request (Map.comp f g) ≫ parameters last =
        (mapWitness request f ≫ mapWitness middle g) ≫ parameters last
    calc
      mapWitness request (Map.comp f g) ≫ parameters last =
          parameters request ≫ (f.parameter ≫ g.parameter) :=
            mapWitness_parameters request (Map.comp f g)
      _ = (parameters request ≫ f.parameter) ≫ g.parameter :=
            (Category.assoc _ _ _).symm
      _ = (mapWitness request f ≫ parameters middle) ≫ g.parameter := by
            rw [mapWitness_parameters]
      _ = mapWitness request f ≫
          (parameters middle ≫ g.parameter) :=
            Category.assoc _ _ _
      _ = mapWitness request f ≫
          (mapWitness middle g ≫ parameters last) := by
            rw [mapWitness_parameters middle g]
      _ = (mapWitness request f ≫ mapWitness middle g) ≫
          parameters last := (Category.assoc _ _ _).symm

/-- Independent target-side data for one scoped operational premise. The
three objects represent parameters, individual events and endpoint values;
the request specifies their actual endpoint condition. -/
structure Package (B : D) where
  X : D
  E : D
  Q : D
  request : Request B X E Q

instance packageCategory (B : D) : Category (Package B) where
  Hom P Q := Map P.request Q.request
  id P := Map.id P.request
  comp f g := Map.comp f g
  id_comp := by
    intro P Q f
    apply Map.ext <;> simp [Map.comp, Map.id]
  comp_id := by
    intro P Q f
    apply Map.ext <;> simp [Map.comp, Map.id]
  assoc := by
    intro P Q R T f g h
    apply Map.ext <;> simp [Map.comp, Category.assoc]

/-- Taking the object of lawful scoped event witnesses is functorial in the
independently specified model data and its ordinary preservation maps. -/
noncomputable def witnessFunctor (B : D) : Package B ⥤ D where
  obj P := Witness P.request
  map f := mapWitness _ f
  map_id P := mapWitness_id P.request
  map_comp f g := mapWitness_comp _ f g

/-- If the parameter object is the entire space of requested endpoint
functions, the premise witness object recovers the full space of scoped
event functions. No evidence is invented or quotiented by this pullback. -/
def allEndpointsRequest (endpointMap : E ⟶ Q) :
    Request B ((ihom B).obj Q) E Q where
  endpoints := endpointMap
  required := 𝟙 _

noncomputable def allEndpointsWitnessIso (endpointMap : E ⟶ Q) :
    Witness (allEndpointsRequest (B := B) endpointMap) ≅
      (ihom B).obj E where
  hom := event _
  inv := assemble _ (𝟙 _) ((ihom B).map endpointMap)
    (by simp [allEndpointsRequest])
  hom_inv_id := by
    apply pullback.hom_ext
    · change (event _ ≫ assemble _ (𝟙 _) ((ihom B).map endpointMap) _) ≫
        event _ = 𝟙 _ ≫ event _
      rw [Category.assoc, assemble_event]
      simp
    · change (event _ ≫ assemble _ (𝟙 _) ((ihom B).map endpointMap) _) ≫
        parameters _ = 𝟙 _ ≫ parameters _
      rw [Category.assoc, assemble_parameters]
      simpa [allEndpointsRequest] using endpoint_condition
        (allEndpointsRequest (B := B) endpointMap)
  inv_hom_id := by
    exact assemble_event _ _ _ _

end Mettapedia.OSLF.Binding.CategoricalScopedEventPremise

#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventPremise.witnessEquiv
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventPremise.assemble_injective_event
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventPremise.mapWitness_comp
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventPremise.witnessFunctor
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedEventPremise.allEndpointsWitnessIso
