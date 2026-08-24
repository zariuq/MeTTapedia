import Mettapedia.GSLT.Core.LooseRelationCompanions
import Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture
import Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition

/-!
# NIK admission over proof-relevant indexed executions

Ordinary GSLT paths are one proof-relevant execution family, not the only
one.  Intrinsic interaction paths, proof derivations, and protocol traces may
retain evidence that a proposition-valued step relation erases.

This module places NIK admission at the equipment level already established
by `LooseRelationEquipment`:

* states are objects;
* an indexed execution family is a proof-relevant loose endo-arrow;
* a realization maps states and execution witnesses, hence supplies a cell;
* semantic meaning and declared observation agreement decorate that cell;
* revision currentness indexes the retained admitted cell;
* active execution applies only the retained state map.

The existing path-based NIK refinement is recovered as a specialization with
`ExecutionPath` as the loose arrow.  Thus this is a common foundation, not a
parallel authority hierarchy.  A capability-indexed observation architecture
also embeds directly while retaining its event, container, and value layers.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission

open Mettapedia.GSLT
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

universe u uValue

/-! ## The equipment-level semantic object and cell -/

/-- A state space, its proof-relevant executions, and the semantic fibre that
an admitted realization must preserve. -/
structure IndexedOperationalObject where
  State : Type u
  Execution : State → State → Type u
  Meaning : State → Prop

namespace IndexedOperationalObject

/-- Forget execution structure only after selecting the common NIK admission
object. -/
def toAdmissionObject (object : IndexedOperationalObject.{u}) :
    AdmissionObject where
  Carrier := object.State
  Meaning := object.Meaning

end IndexedOperationalObject

/-- A semantic refinement cell maps endpoints and proof-relevant executions
and preserves the selected state fibre. -/
structure IndexedRefinement
    (source target : IndexedOperationalObject.{u}) where
  mapState : source.State → target.State
  mapExecution : ∀ {first last}, source.Execution first last →
    target.Execution (mapState first) (mapState last)
  preservesMeaning : ∀ state, source.Meaning state →
    target.Meaning (mapState state)

namespace IndexedRefinement

/-- Identity retains every execution witness. -/
def id (object : IndexedOperationalObject.{u}) :
    IndexedRefinement object object where
  mapState := _root_.id
  mapExecution := _root_.id
  preservesMeaning := fun _ meaningful => meaningful

/-- Refinement cells compose in execution order. -/
def comp {first middle last : IndexedOperationalObject.{u}}
    (earlier : IndexedRefinement first middle)
    (later : IndexedRefinement middle last) :
    IndexedRefinement first last where
  mapState := later.mapState ∘ earlier.mapState
  mapExecution := fun execution =>
    later.mapExecution (earlier.mapExecution execution)
  preservesMeaning := fun state meaningful =>
    later.preservesMeaning _ (earlier.preservesMeaning state meaningful)

/-- The execution component is exactly a cell in the loose-relation
equipment. -/
def toCell {source target : IndexedOperationalObject.{u}}
    (refinement : IndexedRefinement source target) :
    Cell refinement.mapState refinement.mapState source.Execution
      target.Execution where
  map := refinement.mapExecution

/-- The state component is the common NIK admission arrow. -/
def toAdmissionHom {source target : IndexedOperationalObject.{u}}
    (refinement : IndexedRefinement source target) :
    source.toAdmissionObject ⟶ target.toAdmissionObject where
  run := refinement.mapState
  preserves := refinement.preservesMeaning

@[simp] theorem toAdmissionHom_run
    {source target : IndexedOperationalObject.{u}}
    (refinement : IndexedRefinement source target)
    (state : source.State) :
    refinement.toAdmissionHom.run state = refinement.mapState state :=
  rfl

@[simp] theorem toAdmissionHom_comp
    {first middle last : IndexedOperationalObject.{u}}
    (earlier : IndexedRefinement first middle)
    (later : IndexedRefinement middle last) :
    (comp earlier later).toAdmissionHom =
      AdmissionHom.comp earlier.toAdmissionHom later.toAdmissionHom := by
  apply AdmissionHom.ext
  rfl

/-- Vertical composition in the equipment is exactly composition of indexed
execution refinements. -/
theorem toCell_comp
    {first middle last : IndexedOperationalObject.{u}}
    (earlier : IndexedRefinement first middle)
    (later : IndexedRefinement middle last) :
    (comp earlier later).toCell =
      Cell.vcomp earlier.toCell later.toCell := by
  apply Cell.ext
  intro source target execution
  simp only [toCell, comp, Cell.vcomp]

end IndexedRefinement

/-! ## Observation-decorated cells -/

/-- An indexed operational object with one possibly partial declared
observation.  `none` declines observation; it does not remove the execution
from the indexed family. -/
structure IndexedObservedOperationalObject (Value : Type uValue) where
  operational : IndexedOperationalObject.{u}
  observe : ∀ {first last}, operational.Execution first last → Option Value

namespace IndexedObservedOperationalObject

/-- A capability-indexed architecture supplies an exact observed object while
retaining its richer event/container/value factorization separately. -/
def ofArchitecture
    {State : Type u} {Execution : State → State → Type u}
    (architecture : CapabilityIndexedObservationArchitecture State Execution)
    (Meaning : State → Prop) :
    IndexedObservedOperationalObject architecture.Value where
  operational :=
    { State := State
      Execution := Execution
      Meaning := Meaning }
  observe := fun execution => some (architecture.observation.value execution)

end IndexedObservedOperationalObject

/-- A compiler-correctness square on arbitrary proof-relevant indexed
executions. -/
structure IndexedObservedRefinement {Value : Type uValue}
    (source target : IndexedObservedOperationalObject.{u, uValue} Value) where
  refinement : IndexedRefinement source.operational target.operational
  commutes : ∀ {first last} (execution : source.operational.Execution first last),
    target.observe (refinement.mapExecution execution) = source.observe execution

namespace IndexedObservedRefinement

/-- A fixed semantic execution cell is compatible with two declared
observations exactly when the observation square commutes.  This property is
independent of whether the cell is subsequently retained at a revision. -/
def Compatible {Value : Type uValue}
    {source target : IndexedObservedOperationalObject.{u, uValue} Value}
    (refinement : IndexedRefinement source.operational target.operational) :
    Prop :=
  ∀ {first last} (execution : source.operational.Execution first last),
    target.observe (refinement.mapExecution execution) = source.observe execution

/-- Decorating one fixed semantic cell by an observation square is possible
precisely when that cell is compatible with the declared observations. -/
theorem compatible_iff_exists_square_over {Value : Type uValue}
    {source target : IndexedObservedOperationalObject.{u, uValue} Value}
    (refinement : IndexedRefinement source.operational target.operational) :
    Compatible refinement ↔
      Nonempty { square : IndexedObservedRefinement source target //
        square.refinement = refinement } := by
  constructor
  · intro compatible
    exact ⟨⟨⟨refinement, compatible⟩, rfl⟩⟩
  · rintro ⟨⟨square, sameRefinement⟩⟩
    cases sameRefinement
    exact square.commutes

def id {Value : Type uValue}
    (object : IndexedObservedOperationalObject.{u, uValue} Value) :
    IndexedObservedRefinement object object where
  refinement := IndexedRefinement.id object.operational
  commutes := fun _ => rfl

def comp {Value : Type uValue}
    {first middle last : IndexedObservedOperationalObject.{u, uValue} Value}
    (earlier : IndexedObservedRefinement first middle)
    (later : IndexedObservedRefinement middle last) :
    IndexedObservedRefinement first last where
  refinement := IndexedRefinement.comp earlier.refinement later.refinement
  commutes := by
    intro source target execution
    change last.observe
        (later.refinement.mapExecution
          (earlier.refinement.mapExecution execution)) =
      first.observe execution
    exact (later.commutes (earlier.refinement.mapExecution execution)).trans
      (earlier.commutes execution)

end IndexedObservedRefinement

/-! ## Revision-indexed retention -/

/-- An observation-decorated execution cell retained at one dependency
revision. -/
structure IndexedObservedAdmittedAt {Value : Type uValue}
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (source target : IndexedObservedOperationalObject.{u, uValue} Value) where
  refinement : IndexedObservedRefinement source target

namespace IndexedObservedAdmittedAt

/-- Forget to the common revision-independent NIK admission arrow only after
retaining the full indexed execution square. -/
def toAdmissionHom {Value : Type uValue} {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{u, uValue} Value}
    (admission : IndexedObservedAdmittedAt dependencies revision source target) :
    source.operational.toAdmissionObject ⟶
      target.operational.toAdmissionObject :=
  admission.refinement.refinement.toAdmissionHom

def id {Value : Type uValue} (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (object : IndexedObservedOperationalObject.{u, uValue} Value) :
    IndexedObservedAdmittedAt dependencies revision object object where
  refinement := IndexedObservedRefinement.id object

def comp {Value : Type uValue} {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {first middle last : IndexedObservedOperationalObject.{u, uValue} Value}
    (earlier : IndexedObservedAdmittedAt dependencies revision first middle)
    (later : IndexedObservedAdmittedAt dependencies revision middle last) :
    IndexedObservedAdmittedAt dependencies revision first last where
  refinement := IndexedObservedRefinement.comp earlier.refinement later.refinement

/-- Current activation retains only equality of the selected dependency
view. -/
structure Active {Value : Type uValue} {dependencies : DependencySystem}
    {admittedRevision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{u, uValue} Value}
    (_admission : IndexedObservedAdmittedAt dependencies admittedRevision
      source target)
    (currentRevision : dependencies.Revision) : Prop where
  current : dependencies.SameDependencies admittedRevision currentRevision

def activate {Value : Type uValue} {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{u, uValue} Value}
    (admission : IndexedObservedAdmittedAt dependencies admittedRevision
      source target)
    (current : dependencies.SameDependencies admittedRevision currentRevision) :
    admission.Active currentRevision :=
  ⟨current⟩

/-- Active hot execution is only the retained state map. -/
def Active.run {Value : Type uValue} {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{u, uValue} Value}
    {admission : IndexedObservedAdmittedAt dependencies admittedRevision
      source target}
    (_active : admission.Active currentRevision) :
    source.operational.State → target.operational.State :=
  admission.refinement.refinement.mapState

/-- The proof-relevant execution map remains available as retained semantic
evidence, without becoming an argument of `run`. -/
def Active.mapExecution {Value : Type uValue}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{u, uValue} Value}
    {admission : IndexedObservedAdmittedAt dependencies admittedRevision
      source target}
    (_active : admission.Active currentRevision)
    {first last : source.operational.State}
    (execution : source.operational.Execution first last) :
    target.operational.Execution
      (admission.refinement.refinement.mapState first)
      (admission.refinement.refinement.mapState last) :=
  admission.refinement.refinement.mapExecution execution

theorem Active.observationAgreement {Value : Type uValue}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{u, uValue} Value}
    {admission : IndexedObservedAdmittedAt dependencies admittedRevision
      source target}
    (active : admission.Active currentRevision)
    {first last : source.operational.State}
    (execution : source.operational.Execution first last) :
    target.observe (active.mapExecution execution) = source.observe execution :=
  admission.refinement.commutes execution

/-- Admissions stored at different raw revisions compose after both are
aligned with one common current dependency world. -/
def compAtCommonCurrent {Value : Type uValue}
    {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : IndexedObservedOperationalObject.{u, uValue} Value}
    (earlier : IndexedObservedAdmittedAt dependencies earlierRevision
      first middle)
    (later : IndexedObservedAdmittedAt dependencies laterRevision middle last)
    (_alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    IndexedObservedAdmittedAt dependencies currentRevision first last where
  refinement := IndexedObservedRefinement.comp earlier.refinement later.refinement

def activateComposite {Value : Type uValue}
    {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : IndexedObservedOperationalObject.{u, uValue} Value}
    (earlier : IndexedObservedAdmittedAt dependencies earlierRevision
      first middle)
    (later : IndexedObservedAdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    (compAtCommonCurrent earlier later alignment).Active currentRevision :=
  (compAtCommonCurrent earlier later alignment).activate
    (dependencies.sameDependencies_refl currentRevision)

end IndexedObservedAdmittedAt

/-! ## Existing GSLT-path admission is the canonical specialization -/

namespace PathSpecialization

/-- Regard the ordinary path-based NIK object as an indexed execution object. -/
def operationalObject
    (object : NIKRouteAdmission.OperationalObject) :
    IndexedOperationalObject where
  State := object.theory.Term
  Execution := ExecutionPath object.theory
  Meaning := object.Meaning

/-- Every existing operational refinement is an equipment-level indexed
execution cell. -/
def refinement
    {source target : NIKRouteAdmission.OperationalObject}
    (existing : NIKRouteAdmission.Refinement source target) :
    IndexedRefinement (operationalObject source) (operationalObject target) where
  mapState := existing.realization.mapTerm
  mapExecution := existing.realization.mapRoute
  preservesMeaning := existing.preservesMeaning

def observedObject {Value : Type uValue}
    (object : ObservedOperationalObject Value) :
    IndexedObservedOperationalObject Value where
  operational := operationalObject object.operational
  observe := object.observe

def observedRefinement {Value : Type uValue}
    {source target : ObservedOperationalObject Value}
    (existing : ObservedRefinement source target) :
    IndexedObservedRefinement (observedObject source) (observedObject target) where
  refinement := refinement existing.refinement
  commutes := existing.commutes

/-- Existing revision-indexed observed admission retains exactly the same
path square inside the generic indexed-execution doctrine. -/
def observedAdmittedAt {Value : Type uValue}
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    (existing : ObservedAdmittedAt dependencies revision source target) :
    IndexedObservedAdmittedAt dependencies revision
      (observedObject source) (observedObject target) where
  refinement := observedRefinement existing.refinement

/-- Existing path admission and its indexed specialization activate under
the identical dependency-currentness premise. -/
def active {Value : Type uValue}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    (existing : ObservedAdmittedAt dependencies admittedRevision source target)
    (current : dependencies.SameDependencies admittedRevision currentRevision) :
    (observedAdmittedAt existing).Active currentRevision :=
  (observedAdmittedAt existing).activate current

@[simp] theorem refinement_mapState
    {source target : NIKRouteAdmission.OperationalObject}
    (existing : NIKRouteAdmission.Refinement source target) :
    (refinement existing).mapState = existing.realization.mapTerm :=
  rfl

@[simp] theorem observedRefinement_mapExecution {Value : Type uValue}
    {source target : ObservedOperationalObject Value}
    (existing : ObservedRefinement source target)
    {first last : source.operational.theory.Term}
    (execution : ExecutionPath source.operational.theory first last) :
    (observedRefinement existing).refinement.mapExecution execution =
      existing.refinement.realization.mapRoute execution :=
  rfl

/-- The generic specialization does not insert an operational wrapper: its
active state map is definitionally the existing path admission's direct map. -/
@[simp] theorem active_run_agrees {Value : Type uValue}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    (existing : ObservedAdmittedAt dependencies admittedRevision source target)
    (current : dependencies.SameDependencies admittedRevision currentRevision)
    (state : source.operational.theory.Term) :
    (active existing current).run state =
      (existing.activate current).run state :=
  rfl

end PathSpecialization

#print axioms IndexedRefinement.toAdmissionHom_comp
#print axioms IndexedRefinement.toCell_comp
#print axioms IndexedObservedRefinement.comp
#print axioms IndexedObservedRefinement.compatible_iff_exists_square_over
#print axioms IndexedObservedAdmittedAt.Active.observationAgreement
#print axioms PathSpecialization.observedRefinement_mapExecution
#print axioms PathSpecialization.active_run_agrees

end Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
