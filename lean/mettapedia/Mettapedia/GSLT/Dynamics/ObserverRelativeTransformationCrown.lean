import Mettapedia.GSLT.Dynamics.ObserverRelativeControlFactorization

/-!
# Observer-relative transformation capabilities

This module separates four operations that can otherwise be conflated by a
runtime control interface.

* Representation erasure is a commuting map between two presentations of the
  same declared observation.
* Resolving an alternative world chooses one covered representative only when
  the observer is constant on the complete accepted fibre.
* Activation chooses work to run now while retaining every other occurrence
  as deferred work.
* Pruning permanently removes occurrences only with observer preservation and
  an exact removal ledger.

The operations form a capability-indexed family.  Supplying one capability
does not supply the others.  In particular, an activation policy is not a
pruning authority, and a compact representation is not a resolution rule.

Every finite operational transformation below accounts for its source as the
sum of its still-live target and its explicitly receipted removals.  Budget
exhaustion remains an open observation and never becomes a closed negative
answer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.ControlInfluenceSeparation
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.Core.OpenTotalityObservation
open Mettapedia.GSLT.Dynamics

universe uSource uTarget uView uQuestion uWorld uState uExecution uIdentity
universe uGuard uScore uReceipt uActivationReceipt uPruningReceipt uCompact

/-! ## Lossy presentations require a commuting observation square -/

/-- A potentially lossy representation map which preserves exactly one
declared observation.  No inverse is assumed, and no stronger observation is
claimed to survive. -/
structure ObserverPreservingMap
    (Source : Type uSource) (Target : Type uTarget) (View : Type uView)
    (sourceObserver : Observer Source View)
    (targetObserver : Observer Target View) where
  transform : Source -> Target
  preserves : forall source,
    targetObserver.observe (transform source) = sourceObserver.observe source

namespace ObserverPreservingMap

variable {Source : Type uSource} {Middle : Type*} {Target : Type uTarget}
variable {View : Type uView}
variable {sourceObserver : Observer Source View}
variable {middleObserver : Observer Middle View}
variable {targetObserver : Observer Target View}

/-- Identity presentation preserves every observer. -/
def id (observer : Observer Source View) :
    ObserverPreservingMap Source Source View observer observer where
  transform := _root_.id
  preserves := by intro source; rfl

/-- Commuting observation squares compose. -/
def comp
    (first : ObserverPreservingMap Source Middle View
      sourceObserver middleObserver)
    (second : ObserverPreservingMap Middle Target View
      middleObserver targetObserver) :
    ObserverPreservingMap Source Target View sourceObserver targetObserver where
  transform := second.transform ∘ first.transform
  preserves := by
    intro source
    exact (second.preserves (first.transform source)).trans
      (first.preserves source)

@[simp] theorem id_transform (observer : Observer Source View)
    (source : Source) :
    (id observer).transform source = source :=
  rfl

@[simp] theorem comp_transform
    (first : ObserverPreservingMap Source Middle View
      sourceObserver middleObserver)
    (second : ObserverPreservingMap Middle Target View
      middleObserver targetObserver)
    (source : Source) :
    (first.comp second).transform source =
      second.transform (first.transform source) :=
  rfl

/-- Full source observation leaves no room for a many-to-one representation:
the commuting square constructs a left inverse observationally. -/
theorem injective_of_identity_source
    {fullTargetObserver : Observer Target Source}
    (representation : ObserverPreservingMap Source Target Source
      (Observer.identity Source) fullTargetObserver) :
    Function.Injective representation.transform := by
  intro first second sameTarget
  have firstPreserved := representation.preserves first
  have secondPreserved := representation.preserves second
  simpa [Observer.identity] using
    firstPreserved.symm.trans
      ((congrArg fullTargetObserver.observe sameTarget).trans secondPreserved)

end ObserverPreservingMap

/-! ## Resolution is selection over an observer-invariant fibre -/

/-- A proof-relevant family of alternative worlds indexed by a question. -/
structure AlternativeFamily (Question : Type uQuestion) (World : Type uWorld) where
  accepts : Question -> World -> Prop

namespace AlternativeFamily

variable {Question : Type uQuestion} {World : Type uWorld}

/-- Every question has at least one retained world. -/
def Covered (family : AlternativeFamily Question World) : Prop :=
  forall question, exists world, family.accepts question world

/-- The declared observer is constant on every complete alternative fibre. -/
def ObserverInvariant (family : AlternativeFamily Question World)
    {View : Type uView} (observer : Observer World View) : Prop :=
  forall question {first second},
    family.accepts question first -> family.accepts question second ->
      observer.observe first = observer.observe second

/-- A selected representative which remains connected to the retained
alternative relation and agrees observationally with every accepted world. -/
structure ObservationalResolution (family : AlternativeFamily Question World)
    {View : Type uView} (observer : Observer World View) where
  select : Question -> World
  selected : forall question, family.accepts question (select question)
  observes : forall question {world}, family.accepts question world ->
    observer.observe (select question) = observer.observe world

namespace ObservationalResolution

variable {family : AlternativeFamily Question World}
variable {View : Type uView} {observer : Observer World View}

/-- Resolution implies both coverage and observer invariance. -/
theorem covered_and_invariant
    (resolution : family.ObservationalResolution observer) :
    family.Covered /\ family.ObserverInvariant observer := by
  constructor
  · intro question
    exact ⟨resolution.select question, resolution.selected question⟩
  · intro question first second firstAccepted secondAccepted
    exact (resolution.observes question firstAccepted).symm.trans
      (resolution.observes question secondAccepted)

/-- Coverage and fibre invariance construct a selected observational
representative without identifying or deleting the other worlds. -/
noncomputable def ofCoveredInvariant
    (covered : family.Covered)
    (invariant : family.ObserverInvariant observer) :
    family.ObservationalResolution observer := by
  let select : Question -> World := fun question =>
    Classical.choose (covered question)
  have selected : forall question, family.accepts question (select question) :=
    fun question => Classical.choose_spec (covered question)
  exact
    { select := select
      selected := selected
      observes := fun question {_} accepted =>
        invariant question (selected question) accepted }

/-- Exact existence criterion for observer-relative world resolution. -/
theorem nonempty_iff_covered_and_invariant
    (family : AlternativeFamily Question World)
    (observer : Observer World View) :
    Nonempty (family.ObservationalResolution observer) <->
      family.Covered /\ family.ObserverInvariant observer := by
  constructor
  · rintro ⟨resolution⟩
    exact resolution.covered_and_invariant
  · rintro ⟨covered, invariant⟩
    exact ⟨ofCoveredInvariant covered invariant⟩

/-- At the identity observer, a resolution proves every accepted fibre thin.
This is a local statement about the selected family, not global proof
irrelevance. -/
theorem fibre_subsingleton_of_identity
    (resolution : family.ObservationalResolution
      (Observer.identity World))
    (question : Question) :
    Subsingleton {world : World // family.accepts question world} := by
  constructor
  intro first second
  apply Subtype.ext
  have firstEqual : resolution.select question = first.1 := by
    simpa [Observer.identity] using
      resolution.observes question first.2
  have secondEqual : resolution.select question = second.1 := by
    simpa [Observer.identity] using
      resolution.observes question second.2
  exact firstEqual.symm.trans secondEqual

end ObservationalResolution

end AlternativeFamily

/-! ## Finite operational changes retain or receipt every occurrence -/

section AccountedTransformation

variable {State : Type uState} {Execution : State -> State -> Type uExecution}
variable {architecture :
  CapabilityIndexedObservationArchitecture State Execution}
variable {Identity : Type uIdentity} {Guard : Type uGuard}
variable {View : Type uView} {Score : Type uScore}

/-- An observer-preserving finite control transformation with an exact
occurrence-removal ledger.  The target is the complete still-live list;
`removed` is never silently discarded. -/
structure AccountedTransformation
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (Receipt : Type uReceipt) where
  source : List architecture.Event
  target : List architecture.Event
  removed : Multiset architecture.Event
  receipt : Receipt
  preserves :
    control.contract.observer.observe source =
      control.contract.observer.observe target
  accounting :
    (source : Multiset architecture.Event) =
      (target : Multiset architecture.Event) + removed

namespace AccountedTransformation

variable {control : ObserverRelativeControlFactorization architecture Identity
  Guard View Score}

/-- Forget only the packaged law, yielding the existing exact pruning change. -/
def toPruningChange {Receipt : Type uReceipt}
    (transformation : AccountedTransformation control Receipt) :
    PruningChange architecture.Event Receipt where
  source := transformation.source
  target := transformation.target
  receipt := transformation.receipt
  removed := transformation.removed
  accounting := transformation.accounting

/-- Every accounted transformation is already an admitted pruning at its
declared observer. -/
def toAdmittedPruning {Receipt : Type uReceipt}
    (transformation : AccountedTransformation control Receipt) :
    control.AdmittedPruning Receipt :=
  ⟨transformation.toPruningChange, transformation.preserves⟩

/-- Identity changes neither the live list nor its observation. -/
def identity (control : ObserverRelativeControlFactorization architecture
    Identity Guard View Score) (source : List architecture.Event) :
    AccountedTransformation control Unit where
  source := source
  target := source
  removed := 0
  receipt := ()
  preserves := rfl
  accounting := by simp

/-- Accounted observer-preserving transformations compose, accumulating
their removal ledgers. -/
def comp {FirstReceipt : Type*} {SecondReceipt : Type*}
    (first : AccountedTransformation control FirstReceipt)
    (second : AccountedTransformation control SecondReceipt)
    (boundary : first.target = second.source) :
    AccountedTransformation control (FirstReceipt × SecondReceipt) where
  source := first.source
  target := second.target
  removed := first.removed + second.removed
  receipt := (first.receipt, second.receipt)
  preserves := first.preserves.trans (by
    rw [boundary]
    exact second.preserves)
  accounting := by
    calc
      (first.source : Multiset architecture.Event) =
          (first.target : Multiset architecture.Event) + first.removed :=
        first.accounting
      _ = (second.source : Multiset architecture.Event) + first.removed := by
        rw [boundary]
      _ = ((second.target : Multiset architecture.Event) + second.removed) +
          first.removed := by rw [second.accounting]
      _ = (second.target : Multiset architecture.Event) +
          (first.removed + second.removed) := by ac_rfl

/-- An admitted activation becomes an accounted transformation with no
removed occurrences.  Reordering active and deferred work is accepted only
when the declared observer cannot distinguish the recombination. -/
def ofActivation {Receipt : Type uReceipt}
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (partition : ActivationPartition architecture.Event Receipt)
    (lawful : control.contract.Preserves
      { source := partition.source
        target := partition.active ++ partition.deferred
        receipt := partition.receipt }) :
    AccountedTransformation control Receipt where
  source := partition.source
  target := partition.active ++ partition.deferred
  removed := 0
  receipt := partition.receipt
  preserves := lawful
  accounting := by
    simpa using partition.recombinedBag.symm

/-- Existing admitted pruning embeds without changing any data or proof. -/
def ofPruning {Receipt : Type uReceipt}
    (pruning : control.AdmittedPruning Receipt) :
    AccountedTransformation control Receipt where
  source := pruning.1.source
  target := pruning.1.target
  removed := pruning.1.removed
  receipt := pruning.1.receipt
  preserves := pruning.2
  accounting := pruning.1.accounting

/-- The accounting equation is the no-silent-loss law: every source
occurrence is still live or explicitly present in the removal ledger. -/
theorem no_silent_occurrence_loss {Receipt : Type uReceipt}
    (transformation : AccountedTransformation control Receipt) :
    (transformation.source : Multiset architecture.Event) =
      (transformation.target : Multiset architecture.Event) +
        transformation.removed :=
  transformation.accounting

/-- With an empty removal ledger, the complete live occurrence bag is
preserved. -/
theorem source_bag_eq_target_bag_of_removed_eq_zero
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation control Receipt)
    (noneRemoved : transformation.removed = 0) :
    (transformation.source : Multiset architecture.Event) =
      (transformation.target : Multiset architecture.Event) := by
  simpa [noneRemoved] using transformation.accounting

/-- Exact ordered occurrence observation permits no event-list change. -/
theorem source_eq_target_at_exact_occurrence_stream
    (base : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (exact : base.occurrence.Exact)
    {Receipt : Type uReceipt}
    (transformation :
      AccountedTransformation base.withOccurrenceStream Receipt) :
    transformation.source = transformation.target := by
  exact base.source_eq_target_of_exact_occurrence_stream exact
    ⟨{ source := transformation.source
       target := transformation.target
       receipt := transformation.receipt },
      transformation.preserves⟩

/-- Exact occurrence-bag observation permits reordering but no permanent
removal. -/
theorem removed_eq_zero_at_exact_occurrence_bag
    (base : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (exact : base.occurrence.Exact)
    {Receipt : Type uReceipt}
    (transformation :
      AccountedTransformation base.withOccurrenceBag Receipt) :
    transformation.removed = 0 := by
  exact base.removed_eq_zero_of_exact_occurrence_bag exact
    transformation.toAdmittedPruning

end AccountedTransformation

/-! ## Capabilities remain separate requests -/

/-- A partial pruning authority.  It may conservatively refuse a proposal;
every accepted proposal is observationally lawful. -/
structure PruningAuthority
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (Receipt : Type uPruningReceipt) where
  accepts : PruningChange architecture.Event Receipt -> Prop
  sound : forall pruning, accepts pruning ->
    control.contract.Preserves pruning.toChange

namespace PruningAuthority

/-- Accepted authority yields the common accounted transformation. -/
def authorize {Receipt : Type uPruningReceipt}
    {control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score}
    (authority : PruningAuthority control Receipt)
    (pruning : PruningChange architecture.Event Receipt)
    (accepted : authority.accepts pruning) :
    AccountedTransformation control Receipt :=
  AccountedTransformation.ofPruning
    ⟨pruning, authority.sound pruning accepted⟩

end PruningAuthority

/-- A total activation policy.  Its partition keeps unselected occurrences
deferred, and its recombined live list must preserve the declared observer. -/
structure ActivationAuthority
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (Receipt : Type uActivationReceipt) where
  partition : List architecture.Event ->
    ActivationPartition architecture.Event Receipt
  source_eq : forall source, (partition source).source = source
  lawful : forall source, control.contract.Preserves
    { source := (partition source).source
      target := (partition source).active ++ (partition source).deferred
      receipt := (partition source).receipt }

namespace ActivationAuthority

/-- Apply an admitted activation without gaining any removal authority. -/
def apply {Receipt : Type uActivationReceipt}
    {control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score}
    (authority : ActivationAuthority control Receipt)
    (source : List architecture.Event) :
    AccountedTransformation control Receipt :=
  AccountedTransformation.ofActivation control (authority.partition source)
    (authority.lawful source)

@[simp] theorem apply_source {Receipt : Type uActivationReceipt}
    {control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score}
    (authority : ActivationAuthority control Receipt)
    (source : List architecture.Event) :
    (authority.apply source).source = source :=
  authority.source_eq source

@[simp] theorem apply_removed {Receipt : Type uActivationReceipt}
    {control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score}
    (authority : ActivationAuthority control Receipt)
    (source : List architecture.Event) :
    (authority.apply source).removed = 0 :=
  rfl

end ActivationAuthority

/-- The four independently requested transformation capabilities. -/
inductive CapabilityKind where
  | eraseRepresentation
  | resolveAlternative
  | activateDeferred
  | prunePermanently
  deriving DecidableEq, Repr

/-- Parameters shared by one family of transformation requests.  The
alternative worlds are complete live event histories, so resolution is
directly scoped to the same client observer as operational control. -/
structure Requests
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score) where
  Compact : Type uCompact
  compactObserver : Observer Compact View
  Question : Type uQuestion
  alternatives : AlternativeFamily Question (List architecture.Event)
  ActivationReceipt : Type uActivationReceipt
  PruningReceipt : Type uPruningReceipt

/-- The dependent capability family.  Each constructor wraps exactly one
kind of authority, so no capability can be reused at another index. -/
inductive Requests.Capability
    {control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score}
    (requests : Requests control) : CapabilityKind -> Type _ where
  | eraseRepresentation :
      ObserverPreservingMap (List architecture.Event) requests.Compact View
        control.contract.observer requests.compactObserver ->
      requests.Capability .eraseRepresentation
  | resolveAlternative :
      requests.alternatives.ObservationalResolution control.contract.observer ->
      requests.Capability .resolveAlternative
  | activateDeferred :
      ActivationAuthority control requests.ActivationReceipt ->
      requests.Capability .activateDeferred
  | prunePermanently :
      PruningAuthority control requests.PruningReceipt ->
      requests.Capability .prunePermanently

end AccountedTransformation

/-! ## Exhaustion remains open -/

/-- No transformation capability can reinterpret empty exhausted output as a
closed negative answer. -/
theorem exhausted_empty_is_not_refutation
    {Occurrence Residual Revision Coverage Bound Receipt Fault : Type*}
    {CaptureAdmitted : Residual -> Revision -> Prop}
    (bound : Bound) (receipt : Receipt) :
    Not (Observation.EstablishesClosedAbsence
      (Observation.withoutCapture (Residual := Residual)
        (Revision := Revision) (Coverage := Coverage) (Fault := Fault)
        (CaptureAdmitted := CaptureAdmitted) ([] : List Occurrence)
        (.exhausted bound receipt))) :=
  Observation.exhausted_not_establishesClosedAbsence [] bound receipt

/-! ## Positive and negative controls -/

namespace Canary

def coarseBool : Observer Bool Unit where
  observe := fun _ => ()

def unitView : Observer Unit Unit := Observer.identity Unit

/-- Boolean representation may collapse completely at the explicitly
constant observation. -/
def coarseCollapse : ObserverPreservingMap Bool Unit Unit coarseBool unitView where
  transform := fun _ => ()
  preserves := by intro value; cases value <;> rfl

/-- The same collapse is impossible at full Boolean observation. -/
theorem no_exact_bool_collapse :
    Not (Nonempty (ObserverPreservingMap Bool Unit Bool
      (Observer.identity Bool) ({ observe := fun _ => false } : Observer Unit Bool))) := by
  rintro ⟨representation⟩
  have injective := representation.injective_of_identity_source
  have impossible : false = true := injective rfl
  exact Bool.noConfusion impossible

def boolAlternatives : AlternativeFamily Unit Bool where
  accepts := fun _ world => world = false ∨ world = true

private theorem boolAccepted (world : Bool) :
    boolAlternatives.accepts () world := by
  cases world <;> simp [boolAlternatives]

/-- A coarse observer may select one representative while retaining both
worlds in the authored alternative family. -/
def coarseBoolResolution :
    boolAlternatives.ObservationalResolution coarseBool where
  select := fun _ => false
  selected := fun _ => by simp [boolAlternatives]
  observes := by intro question world accepted; rfl

/-- Full observation refuses the same two-world resolution. -/
theorem no_identity_bool_resolution :
    Not (Nonempty (boolAlternatives.ObservationalResolution
      (Observer.identity Bool))) := by
  rintro ⟨resolution⟩
  have falseEqual : resolution.select () = false := by
    simpa [Observer.identity] using
      resolution.observes () (boolAccepted false)
  have trueEqual : resolution.select () = true := by
    simpa [Observer.identity] using
      resolution.observes () (boolAccepted true)
  exact Bool.noConfusion (falseEqual.symm.trans trueEqual)

open ObserverRelativeControlFactorizationCanary

def constantContract : Contract CanaryEvent Unit Unit where
  observer := { observe := fun _ => () }
  demand := { completion := .completeBag }

def coarseControl : ObserverRelativeControlFactorization
    CapabilityIndexedObservationCanary.provenanceArchitecture
    CanaryEvent Unit Unit Nat where
  occurrence := identityIndex
  contract := constantContract
  schedule := CapabilityIndexedObservationCanary.lengthScheduler

def coarseDrop : PruningChange CanaryEvent Unit where
  source := [.left]
  target := []
  receipt := ()
  removed := {.left}
  accounting := by simp

/-- Coarse observation may authorize permanent removal, but the occurrence
remains explicit in the removal ledger. -/
def coarseDropAccounted : AccountedTransformation coarseControl Unit :=
  AccountedTransformation.ofPruning
    ⟨coarseDrop, by rfl⟩

theorem coarse_drop_is_accounted :
    (coarseDropAccounted.source :
        Multiset CapabilityIndexedObservationCanary.provenanceArchitecture.Event) =
      (coarseDropAccounted.target :
        Multiset CapabilityIndexedObservationCanary.provenanceArchitecture.Event) +
        coarseDropAccounted.removed :=
  coarseDropAccounted.no_silent_occurrence_loss

/-- Exact occurrence-bag observation refuses the same permanent removal. -/
theorem exact_occurrence_bag_refuses_coarse_drop_shape :
    Not (exists transformation :
      AccountedTransformation control.withOccurrenceBag Unit,
      transformation.source = [.left] /\
      transformation.target = [] /\
      transformation.removed = {.left}) := by
  rintro ⟨transformation, sourceEqual, targetEqual, removedEqual⟩
  have noRemoval :=
    transformation.removed_eq_zero_at_exact_occurrence_bag
      control identityIndex_exact
  rw [removedEqual] at noRemoval
  simp at noRemoval

end Canary

#print axioms ObserverPreservingMap.comp
#print axioms ObserverPreservingMap.injective_of_identity_source
#print axioms AlternativeFamily.ObservationalResolution.nonempty_iff_covered_and_invariant
#print axioms AlternativeFamily.ObservationalResolution.fibre_subsingleton_of_identity
#print axioms AccountedTransformation.comp
#print axioms AccountedTransformation.no_silent_occurrence_loss
#print axioms AccountedTransformation.removed_eq_zero_at_exact_occurrence_bag
#print axioms exhausted_empty_is_not_refutation
#print axioms Canary.no_exact_bool_collapse
#print axioms Canary.no_identity_bool_resolution
#print axioms Canary.exact_occurrence_bag_refuses_coarse_drop_shape

end Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown
