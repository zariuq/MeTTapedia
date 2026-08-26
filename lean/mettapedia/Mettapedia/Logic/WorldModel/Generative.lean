import Mettapedia.Logic.WorldModel.Basic

/-!
# Relational generative world models

This file adds a non-probabilistic, representation-neutral semantics for models
with residual or boundary data.  Generation is relational: one model/boundary
pair may realize many worlds, and no global joint object is assumed.

The central distinction is between:

* universal consequence, which holds in every realized world;
* residual stability, which says a property does not vary across realizations;
* productivity, which prevents consequence from being accepted merely because
  the model has no realizations.

PLN evidence, probabilities, algorithmic descriptions, and Gibbs specifications
are downstream instances of this interface, not prerequisites for it.
-/

namespace Mettapedia.Logic.WorldModel.Generative

universe uModel uResidual uWorld uObservation

/-- A relational generator with an explicit admissibility boundary. -/
structure Semantics
    (Model : Type uModel) (Residual : Type uResidual) (World : Type uWorld) where
  admissible : Model → Residual → Prop
  realizes : Model → Residual → World → Prop
  realizes_admissible : ∀ {model residual world},
    realizes model residual world → admissible model residual

/-- The model realizes at least one world through the stated residual. -/
def HasRealization
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    (semantics : Semantics Model Residual World)
    (model : Model) (residual : Residual) : Prop :=
  ∃ world, semantics.realizes model residual world

/-- Every admissible residual realizes at least one world. -/
def Productive
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    (semantics : Semantics Model Residual World) (model : Model) : Prop :=
  ∀ residual, semantics.admissible model residual →
    HasRealization semantics model residual

/-- The model has at least one realized world. -/
def HasAnyRealization
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    (semantics : Semantics Model Residual World) (model : Model) : Prop :=
  ∃ residual world, semantics.realizes model residual world

/-- Universal, non-probabilistic consequence from a generative model. -/
def Entails
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    (semantics : Semantics Model Residual World)
    (model : Model) (property : World → Prop) : Prop :=
  ∀ residual world, semantics.realizes model residual world → property world

/-- A property is insensitive to the choice of residual and realized world. -/
def PropertyStable
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    (semantics : Semantics Model Residual World)
    (model : Model) (property : World → Prop) : Prop :=
  ∀ {leftResidual rightResidual leftWorld rightWorld},
    semantics.realizes model leftResidual leftWorld →
    semantics.realizes model rightResidual rightWorld →
    (property leftWorld ↔ property rightWorld)

/-- A witnessed residual leak: two realizations of one model disagree on the
property. -/
def PropertyLeaks
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    (semantics : Semantics Model Residual World)
    (model : Model) (property : World → Prop) : Prop :=
  ∃ leftResidual rightResidual leftWorld rightWorld,
    semantics.realizes model leftResidual leftWorld ∧
    semantics.realizes model rightResidual rightWorld ∧
    property leftWorld ∧ ¬ property rightWorld

/-- An observation is insensitive to the residual and realized world chosen
for one model.  Unlike `PropertyStable`, this retains the observed value rather
than immediately quotienting it to a proposition. -/
def ObservationStable
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {Obs : Type uObservation}
    (semantics : Semantics Model Residual World)
    (model : Model) (observe : World → Obs) : Prop :=
  ∀ {leftResidual rightResidual leftWorld rightWorld},
    semantics.realizes model leftResidual leftWorld →
    semantics.realizes model rightResidual rightWorld →
    observe leftWorld = observe rightWorld

/-- Two realizations of one model whose observations differ. -/
def ObservationLeaks
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {Obs : Type uObservation}
    (semantics : Semantics Model Residual World)
    (model : Model) (observe : World → Obs) : Prop :=
  ∃ leftResidual rightResidual leftWorld rightWorld,
    semantics.realizes model leftResidual leftWorld ∧
    semantics.realizes model rightResidual rightWorld ∧
    observe leftWorld ≠ observe rightWorld

theorem observationLeaks_not_stable
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {Obs : Type uObservation}
    {semantics : Semantics Model Residual World}
    {model : Model} {observe : World → Obs}
    (leaks : ObservationLeaks semantics model observe) :
    ¬ ObservationStable semantics model observe := by
  intro stable
  obtain ⟨leftResidual, rightResidual, leftWorld, rightWorld,
    realizesLeft, realizesRight, differs⟩ := leaks
  exact differs (stable realizesLeft realizesRight)

/-- A stable observation makes equality to any fixed value a stable
property. -/
theorem ObservationStable.propertyStable_eq
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {Obs : Type uObservation}
    {semantics : Semantics Model Residual World}
    {model : Model} {observe : World → Obs}
    (stable : ObservationStable semantics model observe)
    (value : Obs) :
    PropertyStable semantics model (fun world => observe world = value) := by
  intro leftResidual rightResidual leftWorld rightWorld realizesLeft realizesRight
  change observe leftWorld = value ↔ observe rightWorld = value
  rw [stable realizesLeft realizesRight]

/-- A stable observation and one realized witness determine an ordinary
world-model consequence: every realization has the witness's observed value. -/
theorem ObservationStable.entails_eq_of_witness
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {Obs : Type uObservation}
    {semantics : Semantics Model Residual World}
    {model : Model} {observe : World → Obs}
    (stable : ObservationStable semantics model observe)
    {baseResidual : Residual} {baseWorld : World}
    (realizesBase : semantics.realizes model baseResidual baseWorld) :
    Entails semantics model (fun world => observe world = observe baseWorld) := by
  intro residual world realizesWorld
  exact stable realizesWorld realizesBase

/-- If one value is entailed for an observation, then the observation is
stable across all realizations.  This direction does not require a realization
witness and hence remains valid for empty semantics. -/
theorem observationStable_of_exists_entails_eq
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {Obs : Type uObservation}
    {semantics : Semantics Model Residual World}
    {model : Model} {observe : World → Obs}
    (contained : ∃ value, Entails semantics model (fun world => observe world = value)) :
    ObservationStable semantics model observe := by
  obtain ⟨value, entailsValue⟩ := contained
  intro leftResidual rightResidual leftWorld rightWorld realizesLeft realizesRight
  exact (entailsValue leftResidual leftWorld realizesLeft).trans
    (entailsValue rightResidual rightWorld realizesRight).symm

/-- For an inhabited generative model, residual stability of an observation is
equivalent to the specification entailing one exact observed value.  The
inhabitedness premise prevents the existential value from being manufactured
by vacuous entailment. -/
theorem observationStable_iff_exists_entails_eq
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {Obs : Type uObservation}
    {semantics : Semantics Model Residual World}
    {model : Model} {observe : World → Obs}
    (inhabited : HasAnyRealization semantics model) :
    ObservationStable semantics model observe ↔
      ∃ value, Entails semantics model (fun world => observe world = value) := by
  constructor
  · intro stable
    obtain ⟨residual, world, realizesWorld⟩ := inhabited
    exact ⟨observe world, stable.entails_eq_of_witness realizesWorld⟩
  · exact observationStable_of_exists_entails_eq

theorem entails_propertyStable
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {semantics : Semantics Model Residual World}
    {model : Model} {property : World → Prop}
    (h : Entails semantics model property) :
    PropertyStable semantics model property := by
  intro leftResidual rightResidual leftWorld rightWorld hleft hright
  exact ⟨fun _ => h rightResidual rightWorld hright,
    fun _ => h leftResidual leftWorld hleft⟩

/-- Stability plus one positive realized witness yields universal consequence. -/
theorem entails_of_propertyStable_of_witness
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {semantics : Semantics Model Residual World}
    {model : Model} {property : World → Prop}
    (stable : PropertyStable semantics model property)
    {baseResidual : Residual} {baseWorld : World}
    (realizesBase : semantics.realizes model baseResidual baseWorld)
    (positive : property baseWorld) :
    Entails semantics model property := by
  intro residual world realizesWorld
  exact (stable realizesBase realizesWorld).mp positive

theorem entails_iff_stable_positive_witness
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {semantics : Semantics Model Residual World}
    {model : Model} {property : World → Prop}
    (inhabited : HasAnyRealization semantics model) :
    Entails semantics model property ↔
      PropertyStable semantics model property ∧
        ∃ residual world, semantics.realizes model residual world ∧ property world := by
  constructor
  · intro entails
    refine ⟨entails_propertyStable entails, ?_⟩
    obtain ⟨residual, world, realizesWorld⟩ := inhabited
    exact ⟨residual, world, realizesWorld, entails residual world realizesWorld⟩
  · rintro ⟨stable, residual, world, realizesWorld, positive⟩
    exact entails_of_propertyStable_of_witness stable realizesWorld positive

theorem propertyLeaks_not_entails
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {semantics : Semantics Model Residual World}
    {model : Model} {property : World → Prop}
    (leaks : PropertyLeaks semantics model property) :
    ¬ Entails semantics model property := by
  intro entails
  obtain ⟨_leftResidual, rightResidual, _leftWorld, rightWorld,
    _realizesLeft, realizesRight, _positive, negative⟩ := leaks
  exact negative (entails rightResidual rightWorld realizesRight)

theorem propertyLeaks_not_stable
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    {semantics : Semantics Model Residual World}
    {model : Model} {property : World → Prop}
    (leaks : PropertyLeaks semantics model property) :
    ¬ PropertyStable semantics model property := by
  intro stable
  obtain ⟨leftResidual, rightResidual, leftWorld, rightWorld,
    realizesLeft, realizesRight, positive, negative⟩ := leaks
  exact negative ((stable realizesLeft realizesRight).mp positive)

/-! ## Connection to the minimal world-model class -/

/-- Package relational entailment as the extraction operation of the minimal
world-model interface.  Revision remains an explicit policy parameter. -/
@[reducible] def asWorldModel
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    (semantics : Semantics Model Residual World)
    (reviseModel : Model → Model → Model) (emptyModel : Model) :
    _root_.WorldModel Model (World → Prop) Prop where
  revise := reviseModel
  empty := emptyModel
  extract := fun model property => Entails semantics model property

@[simp] theorem asWorldModel_extract
    {Model : Type uModel} {Residual : Type uResidual} {World : Type uWorld}
    (semantics : Semantics Model Residual World)
    (reviseModel : Model → Model → Model) (emptyModel : Model)
    (model : Model) (property : World → Prop) :
    (asWorldModel semantics reviseModel emptyModel).extract model property =
      Entails semantics model property := rfl

/-! ## Positive, leakage, and vacuity controls -/

/-- A deterministic Boolean generator: the residual is the realized world. -/
def booleanSemantics : Semantics Unit Bool Bool where
  admissible := fun _ _ => True
  realizes := fun _ residual world => world = residual
  realizes_admissible := by simp

theorem booleanSemantics_productive : Productive booleanSemantics () := by
  intro residual _admissible
  exact ⟨residual, rfl⟩

theorem booleanSemantics_entails_true :
    Entails booleanSemantics () (fun _ => True) := by
  simp [Entails]

theorem booleanSemantics_truth_leaks :
    PropertyLeaks booleanSemantics () (fun world => world = true) := by
  exact ⟨true, false, true, false, rfl, rfl, rfl, by decide⟩

/-- The identity observation on the Boolean generator genuinely depends on
the residual choice. -/
theorem booleanSemantics_identityObservation_leaks :
    ObservationLeaks booleanSemantics () id := by
  exact ⟨true, false, true, false, rfl, rfl, by decide⟩

theorem booleanSemantics_identityObservation_not_stable :
    ¬ ObservationStable booleanSemantics () id :=
  observationLeaks_not_stable booleanSemantics_identityObservation_leaks

/-- A constant observation is the positive control: its value is entailed by
every realization. -/
theorem booleanSemantics_entails_constantObservation :
    Entails booleanSemantics () (fun world => (fun _ : Bool => false) world = false) := by
  simp [Entails]

theorem booleanSemantics_not_entails_truth :
    ¬ Entails booleanSemantics () (fun world => world = true) :=
  propertyLeaks_not_entails booleanSemantics_truth_leaks

/-- A model with no realizations.  It exposes the vacuity boundary. -/
def emptySemantics : Semantics Unit Unit Bool where
  admissible := fun _ _ => True
  realizes := fun _ _ _ => False
  realizes_admissible := by simp

theorem emptySemantics_entails_every_property (property : Bool → Prop) :
    Entails emptySemantics () property := by
  simp [Entails, emptySemantics]

theorem emptySemantics_not_productive :
    ¬ Productive emptySemantics () := by
  intro productive
  obtain ⟨world, realizesWorld⟩ := productive () trivial
  exact realizesWorld

/-- Universal consequence without productivity may be vacuous. -/
theorem entailment_alone_does_not_imply_productivity :
    Entails emptySemantics () (fun world => world = true) ∧
      ¬ Productive emptySemantics () :=
  ⟨emptySemantics_entails_every_property _, emptySemantics_not_productive⟩

#print axioms entails_iff_stable_positive_witness
#print axioms observationStable_iff_exists_entails_eq
#print axioms observationLeaks_not_stable
#print axioms booleanSemantics_identityObservation_not_stable
#print axioms booleanSemantics_entails_constantObservation
#print axioms booleanSemantics_not_entails_truth
#print axioms entailment_alone_does_not_imply_productivity

end Mettapedia.Logic.WorldModel.Generative
