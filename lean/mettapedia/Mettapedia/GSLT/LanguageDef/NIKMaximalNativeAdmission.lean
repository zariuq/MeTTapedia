import Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
import Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

/-!
# Revision-indexed admission of request-local maximal native calculi

`RecognizedFamily` selects admitted operations in one exact semantic fibre.
`NIKRouteAdmission` stores operational refinements at dependency revisions.
This file gives their canonical common boundary.

A small admission object embeds as a discrete operational object, and every
arrow between such runtime-sized objects becomes a path-valued refinement whose
source has no primitive steps.  A strongest request-local native operation may
therefore be stored at one revision and activated at a dependency-equivalent
revision.  Activation runs the selected operation directly; neither selection
nor currentness adds a checker or certificate to the execution function.  The
current operational API is deliberately `Type 0`; higher-universe operational
objects require a separate universe-polymorphic generalization.

The construction does not assert that every request has a strongest member.
That remains exactly the directedness condition proved by the maximal-native
calculus, and incomparable request fibres remain incomparable.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus

universe uIndex uCapability uRevision uDependency uValue

/-! ## The canonical discrete operational embedding -/

/-- A small admission fibre regarded as a discrete operational theory. -/
@[reducible] def discreteOperationalObject
    (object : AdmissionObject) : OperationalObject where
  theory := GSLT.discrete object.Carrier
  Meaning := object.Meaning

/-- Every runtime-sized admission arrow is an operational refinement between
the corresponding discrete theories.  Its term action and semantic
preservation law are unchanged. -/
def refinementOfAdmission
    {source target : AdmissionObject}
    (operation : source ⟶ target) :
    Refinement (discreteOperationalObject source)
      (discreteOperationalObject target) where
  realization :=
    { mapTerm := operation.run
      mapEquiv := fun equivalent => congrArg operation.run equivalent
      mapStep := fun impossible => impossible.elim }
  preservesMeaning := operation.preserves

@[simp] theorem refinementOfAdmission_mapTerm
    {source target : AdmissionObject}
    (operation : source ⟶ target) :
    (refinementOfAdmission operation).realization.mapTerm = operation.run :=
  rfl

/-- Forgetting the operational path structure recovers exactly the original
admission arrow. -/
@[simp] theorem refinementOfAdmission_toAdmissionHom
    {source target : AdmissionObject}
    (operation : source ⟶ target) :
    (refinementOfAdmission operation).toAdmissionHom = operation := by
  apply AdmissionHom.ext
  rfl

/-- The embedding respects admission composition at the executable map. -/
@[simp] theorem refinementOfAdmission_comp_mapTerm
    {first middle last : AdmissionObject}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    (refinementOfAdmission (AdmissionHom.comp earlier later)).realization.mapTerm =
      (Refinement.comp (refinementOfAdmission earlier)
        (refinementOfAdmission later)).realization.mapTerm :=
by
  funext value
  rfl

/-! ## Revision-indexed strongest selection -/

/-- Store one already-proved request-local strongest native operation at an
exact dependency revision.  Selection supplies the operation; admission
retains its semantic refinement. -/
def admitStrongestAt
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {source target : AdmissionObject}
    (family : RecognizedFamily.{uIndex, uCapability, 0}
      Index source target)
    (request : family.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple)
    (dependencies : DependencySystem.{uRevision, uDependency, uValue})
    (revision : dependencies.Revision) :
    AdmittedAt dependencies revision
      (discreteOperationalObject source)
      (discreteOperationalObject target) where
  refinement := refinementOfAdmission
    (request.strongestOperation selection)

/-- Activating a current strongest selection executes precisely the retained
request-local operation. -/
@[simp] theorem activateStrongest_run
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {source target : AdmissionObject}
    (family : RecognizedFamily.{uIndex, uCapability, 0}
      Index source target)
    (request : family.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple)
    (dependencies : DependencySystem.{uRevision, uDependency, uValue})
    (admittedRevision currentRevision : dependencies.Revision)
    (current : dependencies.SameDependencies admittedRevision currentRevision)
    (input : source.Carrier) :
    ((admitStrongestAt family request selection dependencies admittedRevision)
      |>.activate current).run input =
        (request.strongestOperation selection).run input :=
  rfl

/-- Semantic preservation is inherited from the selected admitted operation;
activation generates no new proof obligation. -/
theorem activateStrongest_preserves
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {source target : AdmissionObject}
    (family : RecognizedFamily.{uIndex, uCapability, 0}
      Index source target)
    (request : family.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple)
    (dependencies : DependencySystem.{uRevision, uDependency, uValue})
    (admittedRevision currentRevision : dependencies.Revision)
    (current : dependencies.SameDependencies admittedRevision currentRevision)
    (input : source.Carrier) (meaningful : source.Meaning input) :
    target.Meaning
      (((admitStrongestAt family request selection dependencies
        admittedRevision).activate current).run input) :=
  (request.strongestOperation selection).preserves input meaningful

/-! ## Positive and stale controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus.Canary

def strongestLinearSelection :
    secondCapabilityRequest.StrongestNativeCalculusPrinciple where
  val := (1 : Fin 2)
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        secondCapabilityRequest]
    · intro candidate candidateMember
      have candidateEqual : candidate = (1 : Fin 2) := by
        simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
          secondCapabilityRequest] using candidateMember
      subst candidate
      exact le_rfl

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

def admittedLinear :=
  admitStrongestAt linearFamily secondCapabilityRequest
    strongestLinearSelection dependencies false

def activeLinear : admittedLinear.Active false :=
  admittedLinear.activate (dependencies.sameDependencies_refl false)

def activeLinearRun : Nat → Nat := activeLinear.run

/-- The active strongest realization is the original nonidentity operation,
not a replay wrapper. -/
theorem active_strongest_runs_original_operation :
    activeLinearRun 1 = 3 :=
  rfl

/-- A changed selected dependency cannot activate the stored strongest
realization. -/
theorem changed_dependency_has_no_active_selection :
    ¬ Nonempty (admittedLinear.Active true) := by
  rintro ⟨active⟩
  have changed := active.current ()
  simp [dependencies] at changed

end Canary

#print axioms refinementOfAdmission_toAdmissionHom
#print axioms refinementOfAdmission_comp_mapTerm
#print axioms activateStrongest_run
#print axioms activateStrongest_preserves
#print axioms Canary.active_strongest_runs_original_operation
#print axioms Canary.changed_dependency_has_no_active_selection

end Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
