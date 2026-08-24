import Mettapedia.Languages.MeTTa.Prime.GSLTILTypedOperationComposition
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration

/-!
# Proof-relevant interaction transport along typed GSLT-IL routes

A represented language route preserves semantic steps, but interaction paths
carry more than their endpoints.  This module constructs the proof-relevant
pushforward presentation whose events retain their source site, endpoints, and
occurrence evidence.  Transported paths erase to the ordinary GSLT path map and
preserve their exact chronological length.

Independent component events therefore transport to two authenticated orders
with one common endpoint.  This is not a target-native scheduling license:
resource separation is additional structure and is never inferred from route
representability.  Conversely, raw nondeterministic branches require no
independence certificate.  A many-to-one translation may merge their visible
targets while the pushed-forward occurrence histories remain distinct.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILInteractionTransport

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedOperationComposition
open Mettapedia.Languages.MeTTa.Prime.LanguageOperationNIKAdmission
open Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration

universe uSite uEvent

/-! ## Exact pushforward of an interaction presentation -/

/-- One transported event retains the complete source occurrence that
generated it.  Its target endpoints are fixed intrinsically by the constructor,
so an event with invented translated endpoints is unconstructible.  Equal
visible endpoints therefore do not identify distinct source sites or
derivations. -/
inductive TransportedEvent
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source) :
    presentation.Site → target.Term → target.Term → Type _ where
  | ofSource {site : presentation.Site} {first last : source.Term}
      (evidence : presentation.Event site first last) :
      TransportedEvent translation presentation site
        (translation.mapTerm first) (translation.mapTerm last)

/-- Push an interaction presentation through an operational translation while
retaining source occurrence identity in every target event. -/
def transportedPresentation
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source) :
    InteractionPresentation target where
  Site := presentation.Site
  Event := TransportedEvent translation presentation
  sound := by
    intro site translatedSource translatedTarget event
    cases event with
    | ofSource evidence =>
        exact translation.mapStep (presentation.sound evidence)

/-- The canonical transported occurrence. -/
def transportEvent
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    {presentation : InteractionPresentation.{uSite, uEvent} source}
    {site : presentation.Site} {first last : source.Term}
    (event : presentation.Event site first last) :
    (transportedPresentation translation presentation).Event site
      (translation.mapTerm first) (translation.mapTerm last) :=
  .ofSource event

/-- Transport every authenticated occurrence in a finite interaction path. -/
def transportEventPath
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source) :
    {first last : source.Term} → EventPath presentation first last →
      EventPath (transportedPresentation translation presentation)
        (translation.mapTerm first) (translation.mapTerm last)
  | _, _, .nil term => .nil (translation.mapTerm term)
  | _, _, .cons event rest =>
      .cons (transportEvent translation event)
        (transportEventPath translation presentation rest)

@[simp] theorem transportEventPath_length
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    {first last : source.Term} (path : EventPath presentation first last) :
    EventPath.pathLength (transportedPresentation translation presentation)
        (transportEventPath translation presentation path) =
      EventPath.pathLength presentation path := by
  induction path with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [transportEventPath, EventPath.pathLength]
      simp only [inductionHypothesis]

@[simp] theorem transportEventPath_append
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    {first middle last : source.Term}
    (earlier : EventPath presentation first middle)
    (later : EventPath presentation middle last) :
    transportEventPath translation presentation
        (EventPath.append presentation earlier later) =
      EventPath.append (transportedPresentation translation presentation)
        (transportEventPath translation presentation earlier)
        (transportEventPath translation presentation later) := by
  induction earlier with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [EventPath.append, transportEventPath]
      rw [inductionHypothesis]

/-- Forward translation of the endpoint-only rewrite-path representation. -/
def mapRewritePath
    {source target : GSLT}
    (translation : OperationalTranslation source target) :
    {first last : source.Term} → source.RewritePath first last →
      target.RewritePath (translation.mapTerm first)
        (translation.mapTerm last)
  | _, _, .nil term => .nil (translation.mapTerm term)
  | _, _, .cons step rest =>
      .cons (translation.mapStep step) (mapRewritePath translation rest)

/-- Occurrence-preserving transport agrees exactly with ordinary GSLT path
transport after erasing occurrence identity. -/
@[simp] theorem transportEventPath_erase
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    {first last : source.Term} (path : EventPath presentation first last) :
    EventPath.erase (transportedPresentation translation presentation)
        (transportEventPath translation presentation path) =
      mapRewritePath translation (EventPath.erase presentation path) := by
  induction path with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [transportEventPath, EventPath.erase, mapRewritePath]
      rw [inductionHypothesis]

/-! ## Typed GSLT-IL programs transport interaction paths -/

/-- The proof-relevant interaction presentation induced by one intrinsically
endpoint-indexed Prime language-operation program. -/
def programTransportedPresentation
    (model : PrimeModel) {source target : Language}
    (program : Program source target)
    (presentation : InteractionPresentation (SemanticTheoryAt model source)) :
    InteractionPresentation (SemanticTheoryAt model target) :=
  transportedPresentation
    (representedProgramRoute model program).toOperationalTranslation
    presentation

/-- A typed program transports an authenticated source interaction without
rechecking it or replacing it by endpoint-only execution. -/
def transportProgramInteraction
    (model : PrimeModel) {source target : Language}
    (program : Program source target)
    (presentation : InteractionPresentation (SemanticTheoryAt model source))
    {first last : StateAt model source}
    (path : EventPath presentation first last) :
    EventPath (programTransportedPresentation model program presentation)
      ((programTranslation model program).mapTerm first)
      ((programTranslation model program).mapTerm last) :=
  transportEventPath
    (representedProgramRoute model program).toOperationalTranslation
    presentation path

/-- Erasing the transported interaction is exactly execution-path transport
along the typed program's operational interpretation. -/
theorem transportProgramInteraction_erase
    (model : PrimeModel) {source target : Language}
    (program : Program source target)
    (presentation : InteractionPresentation (SemanticTheoryAt model source))
    {first last : StateAt model source}
    (path : EventPath presentation first last) :
    EventPath.erase (programTransportedPresentation model program presentation)
        (transportProgramInteraction model program presentation path) =
      mapRewritePath (programTranslation model program)
        (EventPath.erase presentation path) := by
  exact transportEventPath_erase
    (representedProgramRoute model program).toOperationalTranslation
    presentation path

/-! ## Independent squares transport, but are not inferred -/

/-- The two chronological histories supplied by a genuinely separated
interleaving square after transport through an arbitrary operational route. -/
structure TransportedIndependentSquare
    {left right : GSLT}
    (leftPresentation : InteractionPresentation.{uSite, uEvent} left)
    (rightPresentation : InteractionPresentation.{uSite, uEvent} right)
    {target : GSLT}
    (translation : OperationalTranslation
      (GSLT.interleavingProduct left right) target)
    {leftSite : leftPresentation.Site}
    {rightSite : rightPresentation.Site}
    {leftSource leftTarget : left.Term}
    {rightSource rightTarget : right.Term}
    (leftEvent : leftPresentation.Event leftSite leftSource leftTarget)
    (rightEvent : rightPresentation.Event rightSite rightSource rightTarget) where
  leftThenRight : EventPath
    (transportedPresentation translation
      (fibredPresentation leftPresentation rightPresentation))
    (translation.mapTerm (leftSource, rightSource))
    (translation.mapTerm (leftTarget, rightTarget))
  rightThenLeft : EventPath
    (transportedPresentation translation
      (fibredPresentation leftPresentation rightPresentation))
    (translation.mapTerm (leftSource, rightSource))
    (translation.mapTerm (leftTarget, rightTarget))
  leftLength : EventPath.pathLength _ leftThenRight = 2
  rightLength : EventPath.pathLength _ rightThenLeft = 2

/-- An exact component separation square remains two authenticated histories
under route transport.  This transports established independence; it does not
derive a target resource-separation certificate. -/
def transportIndependentSquare
    {left right : GSLT}
    (leftPresentation : InteractionPresentation.{uSite, uEvent} left)
    (rightPresentation : InteractionPresentation.{uSite, uEvent} right)
    {target : GSLT}
    (translation : OperationalTranslation
      (GSLT.interleavingProduct left right) target)
    {leftSite : leftPresentation.Site}
    {rightSite : rightPresentation.Site}
    {leftSource leftTarget : left.Term}
    {rightSource rightTarget : right.Term}
    (leftEvent : leftPresentation.Event leftSite leftSource leftTarget)
    (rightEvent : rightPresentation.Event rightSite rightSource rightTarget) :
    TransportedIndependentSquare leftPresentation rightPresentation
      translation leftEvent rightEvent where
  leftThenRight := transportEventPath translation
    (fibredPresentation leftPresentation rightPresentation)
    (leftThenRightPath leftPresentation rightPresentation leftEvent rightEvent)
  rightThenLeft := transportEventPath translation
    (fibredPresentation leftPresentation rightPresentation)
    (rightThenLeftPath leftPresentation rightPresentation leftEvent rightEvent)
  leftLength := by simp
  rightLength := by simp

/-- A route reflects distinct branch targets only when its term map carries
the corresponding faithfulness capability.  Step preservation alone is not
such a reflection theorem. -/
theorem distinct_targets_of_injective_transport
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (injective : Function.Injective translation.mapTerm)
    {first second : source.Term} (different : first ≠ second) :
    translation.mapTerm first ≠ translation.mapTerm second :=
  injective.ne different

/-! ## Nondeterministic multiworld control -/

namespace Canary

inductive ForkState where
  | root
  | left
  | right
  deriving DecidableEq

def forkTheory : GSLT where
  Term := ForkState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    source = .root ∧ (target = .left ∨ target = .right)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

inductive ForkSite where
  | chooseLeft
  | chooseRight
  deriving DecidableEq

inductive ForkEvent : ForkSite → ForkState → ForkState → Type where
  | chooseLeft : ForkEvent .chooseLeft .root .left
  | chooseRight : ForkEvent .chooseRight .root .right

def forkPresentation : InteractionPresentation forkTheory where
  Site := ForkSite
  Event := ForkEvent
  sound := by
    intro site source target event
    cases event with
    | chooseLeft => exact ⟨rfl, Or.inl rfl⟩
    | chooseRight => exact ⟨rfl, Or.inr rfl⟩

def leftPath : EventPath forkPresentation ForkState.root ForkState.left :=
  .cons ForkEvent.chooseLeft
    (.nil (presentation := forkPresentation) ForkState.left)

def rightPath : EventPath forkPresentation ForkState.root ForkState.right :=
  .cons ForkEvent.chooseRight
    (.nil (presentation := forkPresentation) ForkState.right)

/-- Raw choice supplies two branch worlds but no independence diamond. -/
theorem fork_is_nondeterministic_without_diamond :
    forkTheory.Step .root .left ∧
      forkTheory.Step .root .right ∧
      ¬ ∃ join,
        forkTheory.Step .left join ∧ forkTheory.Step .right join := by
  constructor
  · exact ⟨rfl, Or.inl rfl⟩
  constructor
  · exact ⟨rfl, Or.inr rfl⟩
  · rintro ⟨join, leftStep, _rightStep⟩
    exact ForkState.noConfusion leftStep.1

/-- A deliberately many-to-one operational translation. -/
def collapseFork : OperationalTranslation forkTheory
    Mettapedia.GSLT.Core.InteractionEvent.Canary.loopTheory where
  mapTerm := fun _ => ()
  mapEquiv := fun _ => rfl
  mapStep := fun _ => trivial

def transportedLeftPath :=
  transportEventPath collapseFork forkPresentation leftPath

def transportedRightPath :=
  transportEventPath collapseFork forkPresentation rightPath

/-- Read the retained source sites from a transported history. -/
def originSites : {first last :
    Mettapedia.GSLT.Core.InteractionEvent.Canary.loopTheory.Term} →
    EventPath (transportedPresentation collapseFork forkPresentation)
      first last → List ForkSite
  | _, _, .nil _ => []
  | _, _, .cons (site := site) _ rest => site :: originSites rest

@[simp] theorem transportedLeftPath_sites :
    originSites transportedLeftPath = [.chooseLeft] :=
  by simp [transportedLeftPath, leftPath, transportEventPath, originSites]

@[simp] theorem transportedRightPath_sites :
    originSites transportedRightPath = [.chooseRight] :=
  by simp [transportedRightPath, rightPath, transportEventPath, originSites]

/-- Endpoint collapse does not collapse proof-relevant branch identity. -/
theorem collapsed_targets_retain_distinct_occurrence_worlds :
    collapseFork.mapTerm ForkState.left =
        collapseFork.mapTerm ForkState.right ∧
      transportedLeftPath ≠ transportedRightPath := by
  constructor
  · rfl
  · intro equal
    have siteEqual := congrArg originSites equal
    have impossible : [ForkSite.chooseLeft] = [ForkSite.chooseRight] :=
      transportedLeftPath_sites.symm.trans
        (siteEqual.trans transportedRightPath_sites)
    simp at impossible

end Canary

#print axioms transportEventPath_length
#print axioms transportEventPath_append
#print axioms transportEventPath_erase
#print axioms transportProgramInteraction_erase
#print axioms transportIndependentSquare
#print axioms distinct_targets_of_injective_transport
#print axioms Canary.fork_is_nondeterministic_without_diamond
#print axioms Canary.collapsed_targets_retain_distinct_occurrence_worlds

end Mettapedia.Languages.MeTTa.Prime.GSLTILInteractionTransport
