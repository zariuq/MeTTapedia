import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorReflection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Basic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Extension

/-!
# Qualified typing reaches actual public normal-profile answers

The operational answer theorem alone supplies no type-preservation licence.
An exact qualified package gives the general typing join. Independently,
the already proved vector package gives an instantiated join for old terms
of a checked fresh development, including functions and dependent types.
No qualification of arbitrary new definition rows is inferred from their
structural declaration check.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalTypedExecution

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg level1)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (N : Hosting.Nodes MSig [] ()) (supply : Nat → MClosed)

/-- Membership in the actual normal-profile public controller's observations. -/
def Answer (initial normal : Tower.Tm 0) : Prop :=
  ∃ next, (FrontierArrow.target (D := D) N (NormalProgram.program built D)).MultiStep
    (FrontierArrow.initialState (D := D) N (NormalProgram.program built D)
      (NormalProgram.query built initial)) next ∧
    NativePublic.Contains (FrontierArrow.answers N next) (encodeTm normal)

include supply in
theorem answer_iff (initial normal : Tower.Tm 0) :
    Answer built D N initial normal ↔
      DirectedAnswers.DirectedAnswer (Definitions.devPackage dev built.nativeRows) initial normal := by
  constructor
  · intro answered
    obtain ⟨actual, same, reached, normalForm⟩ :=
      (NormalEvaluatorReflection.public_native_iff built D supply N initial (encodeTm normal)).mp answered
    have equal : normal = actual := encodeTm_injective same
    subst actual
    exact ⟨reached, normalForm⟩
  · intro answer
    exact (NormalEvaluatorReflection.public_native_iff built D supply N initial (encodeTm normal)).mpr
      ⟨normal, rfl, answer.1, answer.2⟩

include supply in
theorem answer_typed_of_preservation {L : Type} [UniverseLevel.LevelOrder L]
    {setting : Setting Tower.Head L}
    (facts : FormFacts setting.R setting.roles)
    (roots : RootPreserving setting.R) (heads : HeadPreserving setting.R)
    (package : setting.R = Definitions.devPackage dev built.nativeRows)
    {initial normal A : Tower.Tm 0}
    (typing : Typed (Definitions.devPackage dev built.nativeRows) .nil initial A)
    (answered : Answer built D N initial normal) :
    Typed (Definitions.devPackage dev built.nativeRows) .nil normal A ∧
      Equal (Definitions.devPackage dev built.nativeRows) .nil initial normal A := by
  have nativeAnswer := (answer_iff built D N supply initial normal).mp answered
  have inSetting : ConversionCoherence.StepStar setting.R initial normal := by
    simpa only [package] using nativeAnswer.stepStar
  have typedInSetting : Typed setting.R .nil initial A := by
    simpa only [package] using typing
  simpa only [package] using
    Reduces.preserve (S := setting) facts roots heads .nil inSetting typedInSetting

include supply in
theorem answer_typed_of_qualified {L : Type} [UniverseLevel.LevelOrder L]
    {setting : Setting Tower.Head L} (qualified : Qualified setting)
    (package : setting.R = Definitions.devPackage dev built.nativeRows)
    {initial normal A : Tower.Tm 0}
    (typing : Typed (Definitions.devPackage dev built.nativeRows) .nil initial A)
    (answered : Answer built D N initial normal) :
    Typed (Definitions.devPackage dev built.nativeRows) .nil normal A ∧
      Equal (Definitions.devPackage dev built.nativeRows) .nil initial normal A := by
  exact answer_typed_of_preservation built D N supply qualified.facts qualified.roots qualified.heads
    package typing answered

include supply in
theorem old_answer_typed (checked : Definitions.devCheck dev = true)
    (fresh : Definitions.devFresh dev = true) {initial normal A : Tower.Tm 0}
    (old : Definitions.OldTerm dev initial) (typing : Typed pkg .nil initial A)
    (answered : Answer built D N initial normal) :
    Typed (Definitions.devPackage dev built.nativeRows) .nil normal A ∧
      Equal (Definitions.devPackage dev built.nativeRows) .nil initial normal A := by
  have nativeAnswer := (answer_iff built D N supply initial normal).mp answered
  have oldRun := (Definitions.dev_stepStar_old checked built.native nativeAnswer.stepStar old).1
  obtain ⟨typed, equal⟩ := Vectors.vectors_subjectReduction level1 .nil oldRun typing
  exact ⟨Definitions.typed_dev fresh built.nativeRows typed,
    Definitions.equal_dev fresh built.nativeRows equal⟩

include supply in
theorem vector_answer_typed {initial normal A : Tower.Tm 0}
    (typing : Typed pkg .nil initial A)
    (answered : Answer ExecutionControls.built D N initial normal) :
    Typed (Definitions.devPackage [] ExecutionControls.built.nativeRows) .nil normal A ∧
      Equal (Definitions.devPackage [] ExecutionControls.built.nativeRows) .nil initial normal A :=
  old_answer_typed ExecutionControls.built D N supply ExecutionControls.empty_checked (by decide)
    (fun _ member => False.elim (List.not_mem_nil member)) typing answered

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalTypedExecution

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalTypedExecution.answer_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalTypedExecution.answer_typed_of_preservation
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalTypedExecution.answer_typed_of_qualified
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalTypedExecution.vector_answer_typed
