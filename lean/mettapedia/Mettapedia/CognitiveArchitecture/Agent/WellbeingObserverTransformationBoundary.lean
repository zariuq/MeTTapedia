import Mettapedia.CognitiveArchitecture.Agent.PatienthoodWellbeing
import Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

/-!
# Observer-relative transformations and wellbeing appraisals

An observer-preserving transformation preserves exactly its declared view.
It preserves an additional appraisal only when that appraisal also factors
through the view.  This is an information-and-authority boundary, not a
definition of wellbeing and not a claim that any particular appraisal is
morally adequate.

The whole-mind canary uses two occurrence-distinct copies with equal payload
state.  State-only observation lawfully admits a representative, while an
observer that also exposes the existing occurrence-sensitive wellbeing
distinction refuses the same resolution.  An exact removal ledger likewise
accounts for a change without making every hidden appraisal invariant.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.WellbeingObserverTransformationBoundary

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

universe uSource uTarget uView uAppraisal

/-! ## Appraisal descent through an observer -/

/-- An appraisal is visible at an observer when one readout of the observer's
view reconstructs it exactly.  Visibility grants information, not execution,
resource, pruning, or moral authority. -/
def AppraisalVisibleAt
    {State : Type uSource} {View : Type uView} {Appraisal : Type uAppraisal}
    (appraisal : State -> Appraisal) (observer : Observer State View) : Prop :=
  Exists fun readout : View -> Appraisal =>
    forall state, readout (observer.observe state) = appraisal state

/-- Equal observed views must have equal values for every visible appraisal. -/
theorem appraisal_eq_of_visible
    {State : Type uSource} {View : Type uView} {Appraisal : Type uAppraisal}
    {appraisal : State -> Appraisal} {observer : Observer State View}
    (visible : AppraisalVisibleAt appraisal observer)
    {first second : State}
    (sameView : observer.observe first = observer.observe second) :
    appraisal first = appraisal second := by
  rcases visible with ⟨readout, agrees⟩
  exact (agrees first).symm.trans
    ((congrArg readout sameView).trans (agrees second))

/-- A single observer collision with different appraisals refutes exact
visibility. -/
theorem appraisal_not_visible_of_collision
    {State : Type uSource} {View : Type uView} {Appraisal : Type uAppraisal}
    {appraisal : State -> Appraisal} {observer : Observer State View}
    {first second : State}
    (sameView : observer.observe first = observer.observe second)
    (different : appraisal first ≠ appraisal second) :
    Not (AppraisalVisibleAt appraisal observer) := by
  intro visible
  exact different (appraisal_eq_of_visible visible sameView)

/-- A source and target presentation share an appraisal only through an
explicit common readout of their common view. -/
structure SharedAppraisal
    {Source : Type uSource} {Target : Type uTarget} {View : Type uView}
    {Appraisal : Type uAppraisal}
    (sourceObserver : Observer Source View)
    (targetObserver : Observer Target View)
    (sourceAppraisal : Source -> Appraisal)
    (targetAppraisal : Target -> Appraisal) where
  readout : View -> Appraisal
  source_agrees : forall source,
    readout (sourceObserver.observe source) = sourceAppraisal source
  target_agrees : forall target,
    readout (targetObserver.observe target) = targetAppraisal target

/-- A commuting representation square preserves every separately certified
shared appraisal. -/
theorem ObserverPreservingMap.preserves_shared_appraisal
    {Source : Type uSource} {Target : Type uTarget} {View : Type uView}
    {Appraisal : Type uAppraisal}
    {sourceObserver : Observer Source View}
    {targetObserver : Observer Target View}
    {sourceAppraisal : Source -> Appraisal}
    {targetAppraisal : Target -> Appraisal}
    (representation : ObserverPreservingMap Source Target View
      sourceObserver targetObserver)
    (shared : SharedAppraisal sourceObserver targetObserver
      sourceAppraisal targetAppraisal)
    (source : Source) :
    targetAppraisal (representation.transform source) =
      sourceAppraisal source := by
  calc
    targetAppraisal (representation.transform source) =
        shared.readout
          (targetObserver.observe (representation.transform source)) :=
      (shared.target_agrees (representation.transform source)).symm
    _ = shared.readout (sourceObserver.observe source) :=
      congrArg shared.readout (representation.preserves source)
    _ = sourceAppraisal source := shared.source_agrees source

/-- A collision already present in the source observer prevents every common
readout, independently of how the target appraisal is chosen. -/
theorem no_shared_appraisal_of_source_collision
    {Source : Type uSource} {Target : Type uTarget} {View : Type uView}
    {Appraisal : Type uAppraisal}
    {sourceObserver : Observer Source View}
    {targetObserver : Observer Target View}
    {sourceAppraisal : Source -> Appraisal}
    {targetAppraisal : Target -> Appraisal}
    {first second : Source}
    (sameView : sourceObserver.observe first = sourceObserver.observe second)
    (different : sourceAppraisal first ≠ sourceAppraisal second) :
    Not (Nonempty (SharedAppraisal sourceObserver targetObserver
      sourceAppraisal targetAppraisal)) := by
  rintro ⟨shared⟩
  apply different
  exact (shared.source_agrees first).symm.trans
    ((congrArg shared.readout sameView).trans
      (shared.source_agrees second))

/-! ## Accounted control still needs appraisal visibility -/

/-- An accounted transformation preserves an appraisal if that appraisal
factors through the transformation's declared control observer.  The removal
receipt alone is not used in the proof. -/
theorem accounted_preserves_visible_appraisal
    {State : Type*} {Execution : State -> State -> Type*}
    {architecture : CapabilityIndexedObservationArchitecture State Execution}
    {Identity Guard View Score Receipt Appraisal : Type*}
    {control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score}
    (transformation : AccountedTransformation control Receipt)
    (appraisal : List architecture.Event -> Appraisal)
    (visible : AppraisalVisibleAt appraisal control.contract.observer) :
    appraisal transformation.source = appraisal transformation.target := by
  rcases visible with ⟨readout, agrees⟩
  calc
    appraisal transformation.source =
        readout (control.contract.observer.observe transformation.source) :=
      (agrees transformation.source).symm
    _ = readout (control.contract.observer.observe transformation.target) :=
      congrArg readout transformation.preserves
    _ = appraisal transformation.target := agrees transformation.target

/-! ## Equal-state whole-mind copies as a discriminating canary -/

namespace Canary

open RevisionLineage
open RevisionLineage.Canary
open PatienthoodWellbeing.Canary

abbrev Mind := Node Owner Revision State

/-- Observe only the payload state, deliberately forgetting lineage identity. -/
def stateOnlyObserver : Observer Mind State where
  observe := Node.state

/-- The payload projection is a valid observer-preserving representation. -/
def stateProjection : ObserverPreservingMap Mind State State
    stateOnlyObserver (Observer.identity State) where
  transform := Node.state
  preserves := by intro mind; rfl

/-- A Boolean readout aligned with the existing occurrence-sensitive
`supported` wellbeing evidence in the canary. -/
def supportedAppraisal (mind : Mind) : Bool :=
  if mind.id = leftCopy.id then true else false

@[simp] theorem supportedAppraisal_left :
    supportedAppraisal leftCopy = true := by
  simp [supportedAppraisal]

@[simp] theorem supportedAppraisal_right :
    supportedAppraisal rightCopy = false := by
  simp [supportedAppraisal, if_neg (by decide : rightCopy.id ≠ leftCopy.id)]

/-- The Boolean appraisal is tied to the already-authored evidence family:
the left copy has `supported` evidence and the equal-state right copy does
not. -/
theorem appraisal_tracks_wellbeing_evidence :
    supportedAppraisal leftCopy = true /\
      Nonempty (wellbeing.Evidence () leftCopy.id .supported) /\
      supportedAppraisal rightCopy = false /\
      IsEmpty (wellbeing.Evidence () rightCopy.id .supported) := by
  refine ⟨supportedAppraisal_left, ⟨leftSupported⟩,
    supportedAppraisal_right, ?_⟩
  exact observational_equivalence_not_welfare_interchangeability.2.2

/-- State projection is lawful for state observation but cannot certify the
occurrence-sensitive wellbeing appraisal, for any target-state appraisal. -/
theorem state_projection_cannot_certify_supported_appraisal
    (targetAppraisal : State -> Bool) :
    Not (Nonempty (SharedAppraisal stateOnlyObserver
      (Observer.identity State) supportedAppraisal targetAppraisal)) := by
  apply no_shared_appraisal_of_source_collision
      (first := leftCopy) (second := rightCopy)
  · rfl
  · simp

/-- The complete live family of the two equal-state fork children. -/
def copyAlternatives : AlternativeFamily Unit Mind where
  accepts := fun _ mind => mind = leftCopy ∨ mind = rightCopy

/-- State-only observation may select a representative because both retained
copies have the same payload state. -/
def stateOnlyResolution :
    copyAlternatives.ObservationalResolution stateOnlyObserver where
  select := fun _ => leftCopy
  selected := by intro _; exact Or.inl rfl
  observes := by
    intro _ mind accepted
    rcases accepted with rfl | rfl <;> rfl

/-- An enriched observer exposes both payload state and the independently
authored occurrence-sensitive wellbeing appraisal. -/
def wellbeingSensitiveObserver : Observer Mind (State × Bool) where
  observe := fun mind => (mind.state, supportedAppraisal mind)

/-- The wellbeing-sensitive observer refuses the same representative:
retaining both alternatives and choosing one cannot preserve their distinct
appraisals. -/
theorem wellbeing_sensitive_resolution_refused :
    Not (Nonempty (copyAlternatives.ObservationalResolution
      wellbeingSensitiveObserver)) := by
  rintro ⟨resolution⟩
  have observesLeft := resolution.observes () (Or.inl rfl)
  have observesRight := resolution.observes () (Or.inr rfl)
  have copiesEqual :
      wellbeingSensitiveObserver.observe leftCopy =
        wellbeingSensitiveObserver.observe rightCopy :=
    observesLeft.symm.trans observesRight
  have appraisalsEqual := congrArg Prod.snd copiesEqual
  simp [wellbeingSensitiveObserver] at appraisalsEqual

/-- Paired control: the admissibility of resolution changes only when the
declared observation changes.  No global ban on selection is asserted. -/
theorem state_resolution_exists_but_wellbeing_resolution_refused :
    Nonempty (copyAlternatives.ObservationalResolution stateOnlyObserver) /\
      Not (Nonempty (copyAlternatives.ObservationalResolution
        wellbeingSensitiveObserver)) :=
  ⟨⟨stateOnlyResolution⟩, wellbeing_sensitive_resolution_refused⟩

/-! ## Accounting is not hidden-appraisal authority -/

open ObserverRelativeTransformationCrown.Canary
open ObserverRelativeControlFactorizationCanary

/-- A deliberately hidden property distinguishing the live source from the
empty target of the coarse accounted-removal canary. -/
def nonemptyLiveAppraisal
    (events : List CanaryEvent) : Bool :=
  !events.isEmpty

/-- The coarse transformation has an exact removal ledger, but its constant
observer cannot reconstruct a source/target-sensitive appraisal. -/
theorem accounted_removal_does_not_make_hidden_appraisal_visible :
    Not (AppraisalVisibleAt nonemptyLiveAppraisal
      coarseControl.contract.observer) := by
  apply appraisal_not_visible_of_collision
      (first := ([.left] : List CanaryEvent)) (second := [])
  · rfl
  · decide

/-- The negative visibility result coexists with exact occurrence accounting;
the ledger answers what was removed, not whether every hidden concern was
preserved. -/
theorem accounting_without_hidden_appraisal_authority :
    ((coarseDropAccounted.source :
        Multiset CapabilityIndexedObservationCanary.provenanceArchitecture.Event) =
      (coarseDropAccounted.target :
        Multiset CapabilityIndexedObservationCanary.provenanceArchitecture.Event) +
        coarseDropAccounted.removed) /\
      Not (AppraisalVisibleAt nonemptyLiveAppraisal
        coarseControl.contract.observer) :=
  ⟨coarseDropAccounted.no_silent_occurrence_loss,
    accounted_removal_does_not_make_hidden_appraisal_visible⟩

end Canary

#print axioms appraisal_eq_of_visible
#print axioms ObserverPreservingMap.preserves_shared_appraisal
#print axioms no_shared_appraisal_of_source_collision
#print axioms accounted_preserves_visible_appraisal
#print axioms Canary.appraisal_tracks_wellbeing_evidence
#print axioms Canary.state_projection_cannot_certify_supported_appraisal
#print axioms Canary.state_resolution_exists_but_wellbeing_resolution_refused
#print axioms Canary.accounting_without_hidden_appraisal_authority

end Mettapedia.CognitiveArchitecture.Agent.WellbeingObserverTransformationBoundary
