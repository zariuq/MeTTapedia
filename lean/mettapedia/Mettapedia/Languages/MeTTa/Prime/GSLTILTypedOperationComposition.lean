import Mettapedia.Languages.MeTTa.Prime.GSLTILTypedOperationAdmission

/-!
# Composition of typed Prime operations at a common NIK world

A selected Prime operation has an authored typed occurrence, a represented
proof-relevant route, and an observation-preserving admission.  This module
proves that those three layers compose without imposing a functional meaning
on raw GSLT-IL commands.

The final observation discipline is pulled back through the later route.  The
resulting intermediate observed object is therefore shared definitionally by
the two stages: execution moves covariantly, while observations move
contravariantly.  Admissions stored at different raw revisions compose when
their selected dependency views have one common current world.

The current two-language signature has only one proper route.  The generic
composition law is nevertheless stated for arbitrary endpoint-indexed route
programs, while a negative theorem records why this particular signature
cannot supply two consecutive proper-route examples.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILTypedOperationComposition

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.ElaborationSelection
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition
open Mettapedia.Languages.MeTTa.Prime.GSLTILLayeredCrown
open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedOperationAdmission
open Mettapedia.Languages.MeTTa.Prime.LanguageOperationFactorization
open Mettapedia.Languages.MeTTa.Prime.LanguageOperationNIKAdmission
open Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax
open Mettapedia.Languages.MeTTa.Prime.IndexedLanguageChange
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics

/-! ## One endpoint-indexed program at all three layers -/

/-- Package an intrinsically endpoint-indexed route program for the existing
syntax-directed operation recognizer. -/
def decodedOfProgram {source target : Language}
    (program : Program source target) :
    currentOperationSignature.DecodedProgram :=
  { source := source, target := target, program := program }

/-- The canonical authored spelling of an endpoint-indexed route program. -/
def recognizedProgram {source target : Language}
    (program : Program source target) : RecognizedOperation :=
  LanguageOperationFactorization.Signature.canonical
    currentOperationSignature (decodedOfProgram program)

@[simp] theorem recognizedProgram_term {source target : Language}
    (program : Program source target) :
    (recognizedProgram program).term = encodeProgram program :=
  rfl

@[simp] theorem recognizedProgram_decoded {source target : Language}
    (program : Program source target) :
    (recognizedProgram program).decoded = decodedOfProgram program :=
  rfl

/-- Canonicalization is only a spelling choice: its term independently has
the endpoint-indexed route type. -/
theorem recognizedProgram_wellTyped {source target : Language}
    (program : Program source target) :
    HasTypeDecl operationDeclEnv .nil (recognizedProgram program).term
      (routeType (languageTerm source) (languageTerm target)) := by
  simpa [recognizedProgram, decodedOfProgram] using encodeProgram_typed program

/-- The semantic operational translation regarded as a represented loose
route.  Its loose relation is the companion graph of the already established
translation; no second evaluator is introduced. -/
def representedProgramRoute (model : PrimeModel)
    {source target : Language} (program : Program source target) :
    RepresentedOperationalRoute (SemanticTheoryAt model source)
      (SemanticTheoryAt model target) where
  related := companion (programTranslation model program).mapTerm
  representation :=
    Representation.companionSelf (programTranslation model program).mapTerm
  mapEquiv := (programTranslation model program).mapEquiv
  mapStep := (programTranslation model program).mapStep

/-- Forgetting the loose witness returns exactly the decoded operational
translation. -/
@[simp] theorem representedProgramRoute_toOperationalTranslation
    (model : PrimeModel) {source target : Language}
    (program : Program source target) :
    (representedProgramRoute model program).toOperationalTranslation =
      programTranslation model program := by
  apply OperationalTranslation.ext
  rfl

/-- One typed program selected, represented, observed, and admitted at a
revision.  The target discipline is declared independently of the route. -/
structure SelectedObservedProgram
    (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (model : PrimeModel)
    {source target : Language} (program : Program source target)
    (sourceMeaning : StateAt model source -> Prop)
    (targetDiscipline : GSLTObservation (SemanticTheoryAt model target)) where
  elaboration : ExactSelection (typedProfile (recognizedProgram program))
  evidenceElaboration :
    Representation (typedEvidenceProfile (recognizedProgram program)).related
  realization : SelectedRouteRealization model (decodedOfProgram program)
  admission : ObservedAdmittedAt dependencies revision
    ((representedProgramRoute model program).toOperationalTranslation.sourceObserved
      sourceMeaning targetDiscipline)
    ((representedProgramRoute model program).toOperationalTranslation.targetImageObserved
      sourceMeaning targetDiscipline)

/-- Construct the joined program object.  Selection, representation, and the
observation square are established once; active execution later uses only the
retained direct map. -/
def selectObserveAndAdmit
    (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (model : PrimeModel)
    {source target : Language} (program : Program source target)
    (sourceMeaning : StateAt model source -> Prop)
    (targetDiscipline : GSLTObservation (SemanticTheoryAt model target)) :
    SelectedObservedProgram dependencies revision model program sourceMeaning
      targetDiscipline where
  elaboration := exactSelection (recognizedProgram program)
  evidenceElaboration :=
    (exactSelection (recognizedProgram program)).toRepresentation
  realization := realize model (decodedOfProgram program)
  admission :=
    (representedProgramRoute model program).admitObservedImage dependencies
      revision sourceMeaning targetDiscipline

/-! ## Revision-aligned composition -/

/-- The selected source meaning after the earlier route. -/
abbrev IntermediateMeaning (model : PrimeModel)
    {first middle : Language} (earlier : Program first middle)
    (sourceMeaning : StateAt model first -> Prop) :
    StateAt model middle -> Prop :=
  (programTranslation model earlier).ImageMeaning sourceMeaning

/-- The earlier stage observes through the later stage.  Consequently its
target object is definitionally the later stage's source object. -/
def selectEarlierForComposite
    (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (model : PrimeModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (sourceMeaning : StateAt model first -> Prop)
    (finalDiscipline : GSLTObservation (SemanticTheoryAt model last)) :
    SelectedObservedProgram dependencies revision model earlier sourceMeaning
      ((representedProgramRoute model later).pullbackObservation
        finalDiscipline) :=
  selectObserveAndAdmit dependencies revision model earlier sourceMeaning
    ((representedProgramRoute model later).pullbackObservation finalDiscipline)

/-- The later stage begins in the exact direct image of the earlier stage. -/
def selectLaterForComposite
    (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (model : PrimeModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (sourceMeaning : StateAt model first -> Prop)
    (finalDiscipline : GSLTObservation (SemanticTheoryAt model last)) :
    SelectedObservedProgram dependencies revision model later
      (IntermediateMeaning model earlier sourceMeaning) finalDiscipline :=
  selectObserveAndAdmit dependencies revision model later
    (IntermediateMeaning model earlier sourceMeaning) finalDiscipline

/-- Two typed programs admitted at possibly different raw revisions compose
at a common current dependency world.  The intermediate observed object is
shared because observation pullback is contravariant to route execution. -/
def admitCompositeAtCommonCurrent
    {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    (model : PrimeModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (sourceMeaning : StateAt model first -> Prop)
    (finalDiscipline : GSLTObservation (SemanticTheoryAt model last))
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :=
  ObservedAdmission.compAtCommonCurrent
    (selectEarlierForComposite dependencies earlierRevision model earlier later
      sourceMeaning finalDiscipline).admission
    (selectLaterForComposite dependencies laterRevision model earlier later
      sourceMeaning finalDiscipline).admission
    alignment

/-- Activate the already-composed admission at its common current world. -/
def activateComposite
    {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    (model : PrimeModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (sourceMeaning : StateAt model first -> Prop)
    (finalDiscipline : GSLTObservation (SemanticTheoryAt model last))
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :=
  ObservedAdmission.activateComposite
    (selectEarlierForComposite dependencies earlierRevision model earlier later
      sourceMeaning finalDiscipline).admission
    (selectLaterForComposite dependencies laterRevision model earlier later
      sourceMeaning finalDiscipline).admission
    alignment

/-- Hot execution is exactly later-after-earlier; elaboration, route
representation, and NIK currentness do not reappear in the runner. -/
theorem activeComposite_run
    {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    (model : PrimeModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (sourceMeaning : StateAt model first -> Prop)
    (finalDiscipline : GSLTObservation (SemanticTheoryAt model last))
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    (activateComposite model earlier later sourceMeaning finalDiscipline
      alignment).run =
      Function.comp (programTranslation model later).mapTerm
        (programTranslation model earlier).mapTerm :=
  rfl

/-- The direct composite is the interpretation of the authored path
composition, not merely an extensionally unrelated function composition. -/
theorem activeComposite_run_is_composedProgram
    {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    (model : PrimeModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (sourceMeaning : StateAt model first -> Prop)
    (finalDiscipline : GSLTObservation (SemanticTheoryAt model last))
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    (activateComposite model earlier later sourceMeaning finalDiscipline
      alignment).run =
      (programTranslation model (Quiver.Path.comp earlier later)).mapTerm := by
  rw [activeComposite_run]
  apply funext
  intro state
  change
    transportTerm (diagram model) (gsltInterpretation.map later)
        (transportTerm (diagram model) (gsltInterpretation.map earlier) state) =
      transportTerm (diagram model)
        (gsltInterpretation.map (Quiver.Path.comp earlier later)) state
  have mapped :
      gsltInterpretation.map (Quiver.Path.comp earlier later) =
        CategoryTheory.CategoryStruct.comp
          (gsltInterpretation.map earlier) (gsltInterpretation.map later) :=
    gsltInterpretation.map_comp earlier later
  rw [mapped]
  exact (transportTerm_comp (diagram model)
    (gsltInterpretation.map earlier) (gsltInterpretation.map later) state).symm

/-- The complete final observation square is retained by the active
composite.  No observation is recomputed during activation. -/
theorem activeComposite_observationAgreement
    {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    (model : PrimeModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (sourceMeaning : StateAt model first -> Prop)
    (finalDiscipline : GSLTObservation (SemanticTheoryAt model last))
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision)
    {source target : (SemanticTheoryAt model first).Term}
    (path : ExecutionPath (SemanticTheoryAt model first) source target) :
    ((representedProgramRoute model later).toOperationalTranslation.targetImageObserved
        (IntermediateMeaning model earlier sourceMeaning) finalDiscipline).observe
      ((admitCompositeAtCommonCurrent model earlier later sourceMeaning
          finalDiscipline alignment).refinement.refinement.realization.mapRoute
        path) =
    ((representedProgramRoute model earlier).toOperationalTranslation.sourceObserved
        sourceMeaning
        ((representedProgramRoute model later).pullbackObservation
          finalDiscipline)).observe path :=
  (activateComposite model earlier later sourceMeaning finalDiscipline
    alignment).observationAgreement path

/-- Loose composition retains the intermediate semantic state and both route
witnesses, while exact representation identifies the whole fibre with the
compiled composite result. -/
def compositeRouteWitnessEquiv
    (model : PrimeModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (source : StateAt model first) (target : StateAt model last) :
    LooseRelationEquipment.comp
        (representedProgramRoute model earlier).related
        (representedProgramRoute model later).related source target ≃
      EqWitness
        ((programTranslation model later).mapTerm
          ((programTranslation model earlier).mapTerm source)) target :=
  (Representation.horizontalComp
    (representedProgramRoute model earlier).representation
    (representedProgramRoute model later).representation).exact source target

/-! ## Current-signature controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.NIKRepresentedRouteObservation.Canary

/-- The current signature has one proper edge, so a factorization of its
promotion cannot contain two positive-length route programs. -/
theorem current_promotion_has_no_two_proper_stages
    (middle : Language)
    (earlier : Program .zero middle) (later : Program middle .prime) :
    ¬ (0 < earlier.length ∧ 0 < later.length) := by
  intro positive
  cases middle with
  | zero =>
      have same := zero_loop_eq_identity earlier
      have firstLength : earlier.length = 0 := by
        rw [same]
        rfl
      omega
  | prime =>
      have same := prime_loop_eq_identity later
      have laterLength : later.length = 0 := by
        rw [same]
        rfl
      omega

def eventCount (system : GSLT) : GSLTObservation system where
  collection :=
    { Container := List system.LabeledStep
      collect := some }
  Value := Nat
  readout := List.length

/-- A real promotion followed by target identity exercises the generic
typed/represented/admitted composition in the current finite signature. -/
theorem currentComposite_runs_promotion
    (model : PrimeModel) :
    (activateComposite
        (dependencies := LanguageOperationNIKAdmission.Canary.dependencies)
        (model := model) promoteProgram (identityProgram .prime)
        (fun _ : StateAt model .zero => True)
        (eventCount (SemanticTheoryAt model .prime))
        (CommonCurrent.refl LanguageOperationNIKAdmission.Canary.dependencies
          (false, false))).run =
      (programTranslation model promoteProgram).mapTerm := by
  rw [activeComposite_run_is_composedProgram]
  rw [zero_prime_eq_promote
    (Quiver.Path.comp promoteProgram (identityProgram .prime))]

/-- Raw authored ambiguity remains outside the selected composition law. -/
theorem raw_ambiguity_is_not_removed_by_typed_composition :
    ∃ program : Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.Program,
      ¬ Nonempty (ExactSelection (Profile.raw program)) :=
  GSLTILTypedOperationAdmission.Canary.raw_ambiguity_remains

/-- A relevant dependency change cannot be hidden by typed-route
composition; there is no common current world at which to activate it. -/
theorem relevant_revision_change_prevents_composition :
    ¬ ∃ currentRevision,
      CommonCurrent LanguageOperationNIKAdmission.Canary.dependencies
        (false, false) (true, false) currentRevision :=
  LanguageOperationNIKAdmission.Canary.relevant_change_has_no_alignment

end Canary

#print axioms recognizedProgram_wellTyped
#print axioms representedProgramRoute_toOperationalTranslation
#print axioms activeComposite_run
#print axioms activeComposite_run_is_composedProgram
#print axioms activeComposite_observationAgreement
#print axioms compositeRouteWitnessEquiv
#print axioms Canary.current_promotion_has_no_two_proper_stages
#print axioms Canary.currentComposite_runs_promotion
#print axioms Canary.raw_ambiguity_is_not_removed_by_typed_composition
#print axioms Canary.relevant_revision_change_prevents_composition

end Mettapedia.Languages.MeTTa.Prime.GSLTILTypedOperationComposition
