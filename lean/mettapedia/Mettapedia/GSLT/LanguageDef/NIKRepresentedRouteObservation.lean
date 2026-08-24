import Mettapedia.GSLT.LanguageDef.GSLTILObservationTransport
import Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition

/-!
# Observed NIK admission induced by represented operational routes

An operational translation can transport both execution and a target
observation discipline.  This module connects that transport square to NIK's
revision-indexed admission doctrine.

The construction first works for any strict operational translation.  A
represented GSLT-IL route then supplies such a translation together with the
stronger proof-relevant reflection law relating its direct map to its loose
route witnesses.  These are deliberately different claims:

* observation transport preserves the declared readout along mapped paths;
* route representation reflects the exact loose relation, including its
  proof-relevant witness fibre;
* revision-indexed admission retains both facts but executes only the direct
  map after currentness has been established.

A loose route that is not representable remains meaningful.  It simply does
not induce this particular direct observed admission.
-/

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ExecutionPathObservation
open Mettapedia.GSLT.Dynamics.ObservationTransport
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement

universe uContainer uObservation

namespace Mettapedia.GSLT.LanguageDef.NIKRouteAdmission.OperationalObject

/-- Equip one existing GSLT with a selected semantic fibre. -/
@[reducible] def ofMeaning (theory : GSLT) (meaning : theory.Term -> Prop) :
    OperationalObject where
  theory := theory
  Meaning := meaning

end Mettapedia.GSLT.LanguageDef.NIKRouteAdmission.OperationalObject

/-! ## Operational translations as observed direct-image refinements -/

namespace Mettapedia.GSLT.IndexedOperational.OperationalTranslation

/-- The direct image of a selected source semantic fibre.  The source witness
is retained, so this does not identify the target predicate with an
unexplained postcondition. -/
def ImageMeaning {source target : GSLT}
    (translation : OperationalTranslation source target)
    (sourceMeaning : source.Term -> Prop) (targetTerm : target.Term) : Prop :=
  exists sourceTerm,
    sourceMeaning sourceTerm /\ translation.mapTerm sourceTerm = targetTerm

/-- The source operational object of a direct-image refinement. -/
@[reducible] def sourceObject {source target : GSLT}
    (_translation : OperationalTranslation source target)
    (sourceMeaning : source.Term -> Prop) : OperationalObject :=
  OperationalObject.ofMeaning source sourceMeaning

/-- The target operational object carries exactly the direct-image meaning. -/
@[reducible] def targetImageObject {source target : GSLT}
    (translation : OperationalTranslation source target)
    (sourceMeaning : source.Term -> Prop) : OperationalObject where
  theory := target
  Meaning := translation.ImageMeaning sourceMeaning

/-- Every strict operational translation preserves the direct image of an
arbitrary selected source meaning. -/
def imageRefinement {source target : GSLT}
    (translation : OperationalTranslation source target)
    (sourceMeaning : source.Term -> Prop) :
    Refinement (translation.sourceObject sourceMeaning)
      (translation.targetImageObject sourceMeaning) where
  realization := OperationalRealization.ofTranslation translation
  preservesMeaning := by
    intro sourceTerm meaningful
    exact ⟨sourceTerm, meaningful, rfl⟩

/-- Observe source paths with the canonical pullback of a target discipline. -/
@[reducible] def sourceObserved {source target : GSLT}
    (translation : OperationalTranslation source target)
    (sourceMeaning : source.Term -> Prop)
    (targetDiscipline : GSLTObservation.{0, uContainer, uObservation}
      target) : ObservedOperationalObject targetDiscipline.Value where
  operational := translation.sourceObject sourceMeaning
  observe := ofDiscipline
    (ObservationDiscipline.pullback (mapEvent translation) targetDiscipline)

/-- Observe target paths with the original target discipline. -/
@[reducible] def targetImageObserved {source target : GSLT}
    (translation : OperationalTranslation source target)
    (sourceMeaning : source.Term -> Prop)
    (targetDiscipline : GSLTObservation.{0, uContainer, uObservation}
      target) : ObservedOperationalObject targetDiscipline.Value where
  operational := translation.targetImageObject sourceMeaning
  observe := ofDiscipline targetDiscipline

/-- Observation transport supplies the compiler-correctness square required
by NIK.  The observation discipline is declared independently of the
translation; it is not inferred from the direct map. -/
def observedImageRefinement {source target : GSLT}
    (translation : OperationalTranslation source target)
    (sourceMeaning : source.Term -> Prop)
    (targetDiscipline : GSLTObservation.{0, uContainer, uObservation}
      target) :
    ObservedRefinement
      (translation.sourceObserved sourceMeaning targetDiscipline)
      (translation.targetImageObserved sourceMeaning targetDiscipline) where
  refinement := translation.imageRefinement sourceMeaning
  commutes := by
    intro first last path
    change ofDiscipline targetDiscipline
        ((OperationalRealization.ofTranslation translation).mapRoute path) =
      ofDiscipline
        (ObservationDiscipline.pullback (mapEvent translation)
          targetDiscipline) path
    rw [OperationalRealization.mapRoute_ofTranslation]
    exact (observe_mapRoute translation targetDiscipline path).symm

/-- Store the complete translation/observation square at one dependency
revision. -/
def admitObservedImage {source target : GSLT}
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (translation : OperationalTranslation source target)
    (sourceMeaning : source.Term -> Prop)
    (targetDiscipline : GSLTObservation.{0, uContainer, uObservation}
      target) :
    ObservedAdmittedAt dependencies revision
      (translation.sourceObserved sourceMeaning targetDiscipline)
      (translation.targetImageObserved sourceMeaning targetDiscipline) :=
  ⟨translation.observedImageRefinement sourceMeaning targetDiscipline⟩

@[simp] theorem observedImageRefinement_mapTerm
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (sourceMeaning : source.Term -> Prop)
    (targetDiscipline : GSLTObservation.{0, uContainer, uObservation}
      target) :
    (translation.observedImageRefinement sourceMeaning targetDiscipline
      ).refinement.realization.mapTerm = translation.mapTerm :=
  rfl

end Mettapedia.GSLT.IndexedOperational.OperationalTranslation

/-! ## The stronger represented-route boundary -/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment.RepresentedOperationalRoute

/-- A represented route inherits the observed direct-image refinement of its
compiled operational translation. -/
def observedImageRefinement {source target : GSLT}
    (route : RepresentedOperationalRoute source target)
    (sourceMeaning : source.Term -> Prop)
    (targetDiscipline : GSLTObservation.{0, uContainer, uObservation}
      target) :=
  route.toOperationalTranslation.observedImageRefinement sourceMeaning
    targetDiscipline

/-- Store the represented route's complete observation square at one
dependency revision. -/
def admitObservedImage {source target : GSLT}
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (route : RepresentedOperationalRoute source target)
    (sourceMeaning : source.Term -> Prop)
    (targetDiscipline : GSLTObservation.{0, uContainer, uObservation}
      target) :=
  route.toOperationalTranslation.admitObservedImage dependencies revision
    sourceMeaning targetDiscipline

/-- Exact proof-relevant reflection on the represented fragment.  This is
strictly stronger than equality of a lossy observation: the complete loose
route witness fibre is equivalent to equality with the compiled result. -/
def relatedEquivCompiledEquality {source target : GSLT}
    (route : RepresentedOperationalRoute source target)
    (sourceTerm : source.Term) (targetTerm : target.Term) :
    route.related sourceTerm targetTerm ≃
      EqWitness (route.representation.map sourceTerm) targetTerm :=
  route.representation.exact sourceTerm targetTerm

/-- Extensional shadow of exact proof-relevant reflection. -/
theorem related_nonempty_iff_compiled_eq
    {source target : GSLT}
    (route : RepresentedOperationalRoute source target)
    (sourceTerm : source.Term) (targetTerm : target.Term) :
    Nonempty (route.related sourceTerm targetTerm) ↔
      route.representation.map sourceTerm = targetTerm := by
  constructor
  · rintro ⟨witness⟩
    exact (route.relatedEquivCompiledEquality sourceTerm targetTerm witness).down.down
  · intro equal
    exact ⟨(route.relatedEquivCompiledEquality sourceTerm targetTerm).symm
      ⟨⟨equal⟩⟩⟩

/-- The target meaning used by generic NIK admission is not merely a predicate
about the compiled map: on a represented route it is exactly reachability by
one retained loose witness from a meaningful source. -/
theorem imageMeaning_iff_exists_related
    {source target : GSLT}
    (route : RepresentedOperationalRoute source target)
    (sourceMeaning : source.Term -> Prop) (targetTerm : target.Term) :
    route.toOperationalTranslation.ImageMeaning sourceMeaning targetTerm ↔
      exists sourceTerm,
        sourceMeaning sourceTerm /\ Nonempty (route.related sourceTerm targetTerm) := by
  constructor
  · rintro ⟨sourceTerm, meaningful, mapped⟩
    exact ⟨sourceTerm, meaningful,
      (route.related_nonempty_iff_compiled_eq sourceTerm targetTerm).2 mapped⟩
  · rintro ⟨sourceTerm, meaningful, related⟩
    exact ⟨sourceTerm, meaningful,
      (route.related_nonempty_iff_compiled_eq sourceTerm targetTerm).1 related⟩

@[simp] theorem observedImageRefinement_mapTerm
    {source target : GSLT}
    (route : RepresentedOperationalRoute source target)
    (sourceMeaning : source.Term -> Prop)
    (targetDiscipline : GSLTObservation.{0, uContainer, uObservation}
      target) :
    (route.observedImageRefinement sourceMeaning targetDiscipline
      ).refinement.realization.mapTerm = route.representation.map :=
  rfl

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment.RepresentedOperationalRoute

/-! ## Positive and negative controls -/

namespace Mettapedia.GSLT.LanguageDef.NIKRepresentedRouteObservation.Canary

@[reducible] def successorTheory : GSLT where
  Term := Nat
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => target = Nat.succ source
  rewrites_resp_left := by
    rintro source source' target sourceEq targetEq
    subst source'
    exact ⟨target, targetEq, rfl⟩
  rewrites_resp_right := by
    rintro source target target' targetEq targetEq'
    subst target'
    exact targetEq

def successorRoute : RepresentedOperationalRoute successorTheory successorTheory where
  related := companion Nat.succ
  representation := Representation.companionSelf Nat.succ
  mapEquiv := fun equal => congrArg Nat.succ equal
  mapStep := fun step => congrArg Nat.succ step

def traceLength : GSLTObservation successorTheory where
  collection :=
    { Container := List successorTheory.LabeledStep
      collect := some }
  Value := Nat
  readout := List.length

def zero : ExecutionObject successorTheory := (0 : Nat)

def one : ExecutionObject successorTheory := (1 : Nat)

def four : ExecutionObject successorTheory := (4 : Nat)

def five : ExecutionObject successorTheory := (5 : Nat)

def sourceStep : successorTheory.Step zero one := rfl

def sourcePath : ExecutionPath successorTheory zero one :=
  .cons ⟨sourceStep⟩ (.refl one)

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

def admittedSuccessor :=
  successorRoute.admitObservedImage dependencies false (fun _ => True)
    traceLength

def activeSuccessor : admittedSuccessor.Active false :=
  admittedSuccessor.activate (dependencies.sameDependencies_refl false)

/-- A represented route is stored and activated once, then executes exactly
its direct compiled map. -/
theorem active_route_runs_directly : activeSuccessor.run four = five :=
  rfl

/-- The declared path observation survives active execution. -/
theorem active_route_preserves_trace_observation :
    (OperationalTranslation.targetImageObserved
      successorRoute.toOperationalTranslation (fun _ => True) traceLength).observe
        (admittedSuccessor.refinement.refinement.realization.mapRoute sourcePath) =
      (OperationalTranslation.sourceObserved
        successorRoute.toOperationalTranslation (fun _ => True) traceLength).observe
          sourcePath :=
  activeSuccessor.observationAgreement sourcePath

/-- A relevant revision change cannot activate the stored route. -/
theorem relevant_change_prevents_activation :
    Not (admittedSuccessor.Active true) := by
  rintro ⟨current⟩
  have changed := current ()
  simp [dependencies] at changed

/-- The raw nondeterministic choice route still has both results, while no
represented operational route can claim that exact loose relation. -/
theorem raw_choice_remains_meaningful_without_representation :
    (Nonempty (LooseRelationEquipment.Canary.choice () false) /\
      Nonempty (LooseRelationEquipment.Canary.choice () true)) /\
      Not (Exists (fun route : RepresentedOperationalRoute
          (GSLT.discrete Unit) (GSLT.discrete Bool) =>
        route.related = LooseRelationEquipment.Canary.choice)) := by
  constructor
  · exact LooseRelationEquipment.Canary.choice_executes_both
  · rintro ⟨route, sameRelation⟩
    apply LooseRelationEquipment.Canary.choice_not_representable
    rw [← sameRelation]
    exact ⟨route.representation⟩

/-- Even on the positive represented route, a lossy readout does not reflect
distinct zero-step endpoints. -/
theorem observed_equality_does_not_reflect_states :
    (0 : Nat) ≠ 1 /\
      ofDiscipline traceLength
          (.refl zero : ExecutionPath successorTheory zero zero) =
        ofDiscipline traceLength
          (.refl one : ExecutionPath successorTheory one one) := by
  constructor
  · decide
  · rfl

end Mettapedia.GSLT.LanguageDef.NIKRepresentedRouteObservation.Canary

open Mettapedia.GSLT.LanguageDef.NIKRepresentedRouteObservation

#print axioms OperationalTranslation.observedImageRefinement
#print axioms RepresentedOperationalRoute.related_nonempty_iff_compiled_eq
#print axioms RepresentedOperationalRoute.imageMeaning_iff_exists_related
#print axioms Canary.active_route_runs_directly
#print axioms Canary.active_route_preserves_trace_observation
#print axioms Canary.relevant_change_prevents_activation
#print axioms Canary.raw_choice_remains_meaningful_without_representation
#print axioms Canary.observed_equality_does_not_reflect_states
