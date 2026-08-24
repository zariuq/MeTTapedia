import Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
import Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission

/-!
# NIK admission of proof-relevant inference extensions

A learned presentation participates in NIK through two ordinary semantic
refinement cells, not through a special learning authority:

1. a validated extension transports every old derivation while preserving its
   exact erased proof artifact;
2. an independently supplied proof-relevant semantics interprets every target
   derivation while retaining that derivation beside the constructed meaning.

Both cells are indexed by dependency revisions and compose through the common
NIK admission doctrine.  The active map performs only the retained transport
and interpretation.  No checker, certificate, or profitability comparison is
an argument of active execution.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKInferenceExtensionAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferencePresentationExtension
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition

universe uState uMeaning

/-! ## Checked and interpreted proof states -/

/-- A goal together with its exact checked derivation. -/
structure CheckedState (presentation : ValidatedPresentation) where
  goal : Pattern
  derivation : Derivation presentation goal

/-- The proof-artifact execution family relates checked states that expose the
same indexed goal and exact raw proof.  It lives in `Type` so it can serve as a
proof-relevant loose arrow while its equality fields remain propositions. -/
structure CheckedExecutionEvidence {presentation : ValidatedPresentation}
    (first last : CheckedState presentation) : Type where
  goalEq : first.goal = last.goal
  eraseEq : first.derivation.erase = last.derivation.erase

/-- Lift the small proof-artifact evidence into the state universe selected by
the common indexed-execution doctrine. -/
def CheckedExecution {presentation : ValidatedPresentation}
    (first last : ULift.{uState} (CheckedState presentation)) : Type uState :=
  ULift (CheckedExecutionEvidence first.down last.down)

/-- The observation is the exact raw proof at the source occurrence. -/
def checkedObject (presentation : ValidatedPresentation) :
    IndexedObservedOperationalObject.{uState, 0} RawProof where
  operational :=
    { State := ULift.{uState} (CheckedState presentation)
      Execution := CheckedExecution
      Meaning := fun _ => True }
  observe := fun {first} {_last} _ => some first.down.derivation.erase

/-- Interpreted states retain the complete checked state; semantic evidence is
additional structure, never a replacement for the proof program. -/
structure InterpretedState (presentation : ValidatedPresentation)
    (Meaning : Pattern → Type uMeaning) where
  checked : CheckedState presentation
  evidence : Meaning checked.goal

def InterpretedExecution {presentation : ValidatedPresentation}
    {Meaning : Pattern → Type uMeaning}
    (first last : InterpretedState presentation Meaning) : Type uMeaning :=
  ULift (CheckedExecutionEvidence first.checked last.checked)

def interpretedObject (presentation : ValidatedPresentation)
    (Meaning : Pattern → Type uMeaning) :
    IndexedObservedOperationalObject.{uMeaning, 0} RawProof where
  operational :=
    { State := InterpretedState presentation Meaning
      Execution := InterpretedExecution
      Meaning := fun _ => True }
  observe := fun {first} {_last} _ => some first.checked.derivation.erase

/-! ## The two semantic cells -/

/-- Validated extension transports a checked state without changing its goal
or raw proof artifact. -/
def transportState {base : ValidatedPresentation}
    (extension : ValidatedExtension base) :
    CheckedState base → CheckedState extension.target
  | ⟨goal, derivation⟩ => ⟨goal, extension.transport derivation⟩

@[simp] theorem transportState_goal {base : ValidatedPresentation}
    (extension : ValidatedExtension base) (state : CheckedState base) :
    (transportState extension state).goal = state.goal :=
  rfl

@[simp] theorem transportState_erase {base : ValidatedPresentation}
    (extension : ValidatedExtension base) (state : CheckedState base) :
    (transportState extension state).derivation.erase =
      state.derivation.erase :=
  Derivation.erase_transport extension.refines state.derivation

/-- The proof-preserving presentation extension is an observation-preserving
indexed refinement. -/
def transportRefinement {base : ValidatedPresentation}
    (extension : ValidatedExtension base) :
    IndexedObservedRefinement (checkedObject base)
      (checkedObject extension.target) where
  refinement :=
    { mapState := fun state => ⟨transportState extension state.down⟩
      mapExecution := by
        intro first last execution
        refine ⟨⟨execution.down.goalEq, ?_⟩⟩
        rw [transportState_erase, transportState_erase]
        exact execution.down.eraseEq
      preservesMeaning := fun _ _ => trivial }
  commutes := by
    intro first last execution
    change some (transportState extension first.down).derivation.erase =
      some first.down.derivation.erase
    rw [transportState_erase]

/-- Proof-relevant interpretation adds semantic evidence while preserving the
exact checked derivation. -/
noncomputable def interpretState
    {base : ValidatedPresentation} {extension : ValidatedExtension base}
    {Meaning : Pattern → Type uMeaning}
    (semantics : SemanticExtension base extension Meaning) :
    CheckedState extension.target →
      InterpretedState extension.target Meaning
  | state =>
      ⟨state, semantics.interpret state.derivation⟩

@[simp] theorem interpretState_checked
    {base : ValidatedPresentation} {extension : ValidatedExtension base}
    {Meaning : Pattern → Type uMeaning}
    (semantics : SemanticExtension base extension Meaning)
    (state : CheckedState extension.target) :
    (interpretState semantics state).checked = state :=
  rfl

/-- The proof-relevant semantic interpretation is an observation-preserving
indexed refinement. -/
noncomputable def interpretRefinement
    {base : ValidatedPresentation} {extension : ValidatedExtension base}
    {Meaning : Pattern → Type uMeaning}
    (semantics : SemanticExtension base extension Meaning) :
    IndexedObservedRefinement (checkedObject extension.target)
      (interpretedObject extension.target Meaning) where
  refinement :=
    { mapState := fun state => interpretState semantics state.down
      mapExecution := fun execution => ⟨execution.down⟩
      preservesMeaning := fun _ _ => trivial }
  commutes := fun _ => rfl

/-! ## Revision-indexed admission and composition -/

def admitTransportAt {base : ValidatedPresentation}
    (extension : ValidatedExtension base)
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    IndexedObservedAdmittedAt dependencies revision
      (checkedObject base) (checkedObject extension.target) where
  refinement := transportRefinement extension

noncomputable def admitInterpretationAt
    {base : ValidatedPresentation} {extension : ValidatedExtension base}
    {Meaning : Pattern → Type uMeaning}
    (semantics : SemanticExtension base extension Meaning)
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    IndexedObservedAdmittedAt dependencies revision
      (checkedObject extension.target)
      (interpretedObject extension.target Meaning) where
  refinement := interpretRefinement semantics

/-- Extensions validated at different raw revisions compose only after both
dependency views agree with one common current revision. -/
noncomputable def admitCompositeAtCommonCurrent
    {base : ValidatedPresentation} {extension : ValidatedExtension base}
    {Meaning : Pattern → Type uMeaning}
    (semantics : SemanticExtension base extension Meaning)
    (dependencies : DependencySystem)
    {transportRevision interpretationRevision currentRevision :
      dependencies.Revision}
    (alignment : CommonCurrent dependencies transportRevision
      interpretationRevision currentRevision) :
    IndexedObservedAdmittedAt dependencies currentRevision
      (checkedObject base)
      (interpretedObject extension.target Meaning) :=
  IndexedObservedAdmittedAt.compAtCommonCurrent
    (admitTransportAt extension dependencies transportRevision)
    (admitInterpretationAt semantics dependencies interpretationRevision)
    alignment

noncomputable def activateComposite
    {base : ValidatedPresentation} {extension : ValidatedExtension base}
    {Meaning : Pattern → Type uMeaning}
    (semantics : SemanticExtension base extension Meaning)
    (dependencies : DependencySystem)
    {transportRevision interpretationRevision currentRevision :
      dependencies.Revision}
    (alignment : CommonCurrent dependencies transportRevision
      interpretationRevision currentRevision) :
    (admitCompositeAtCommonCurrent semantics dependencies alignment).Active
      currentRevision :=
  (admitCompositeAtCommonCurrent semantics dependencies alignment).activate
    (dependencies.sameDependencies_refl currentRevision)

/-- Active composition retains the original goal, the exact old raw proof,
and a target semantic inhabitant. -/
theorem activeComposite_contract
    {base : ValidatedPresentation} {extension : ValidatedExtension base}
    {Meaning : Pattern → Type uMeaning}
    (semantics : SemanticExtension base extension Meaning)
    (dependencies : DependencySystem)
    {transportRevision interpretationRevision currentRevision :
      dependencies.Revision}
    (alignment : CommonCurrent dependencies transportRevision
      interpretationRevision currentRevision)
    (state : CheckedState base) :
    let result :=
      (activateComposite semantics dependencies alignment).run ⟨state⟩
    result.checked.goal = state.goal ∧
      result.checked.derivation.erase = state.derivation.erase ∧
      Nonempty (Meaning result.checked.goal) := by
  dsimp [activateComposite, admitCompositeAtCommonCurrent,
    IndexedObservedAdmittedAt.Active.run,
    IndexedObservedAdmittedAt.compAtCommonCurrent,
    IndexedObservedRefinement.comp, IndexedRefinement.comp,
    admitTransportAt, admitInterpretationAt, transportRefinement,
    interpretRefinement]
  exact ⟨rfl, transportState_erase extension state,
    ⟨semantics.interpret (extension.transport state.derivation)⟩⟩

/-! ## Non-gating control -/

/-- Without any admitted extension, the original checked state and derivation
remain inhabited.  Admission adds a realization; its absence does not refute
the source proof. -/
theorem missing_admission_preserves_checked_state
    {presentation : ValidatedPresentation}
    (state : CheckedState presentation) :
    Nonempty (CheckedState presentation) :=
  ⟨state⟩

#print axioms transportRefinement
#print axioms interpretRefinement
#print axioms admitCompositeAtCommonCurrent
#print axioms activeComposite_contract
#print axioms missing_admission_preserves_checked_state

end Mettapedia.GSLT.LanguageDef.NIKInferenceExtensionAdmission
