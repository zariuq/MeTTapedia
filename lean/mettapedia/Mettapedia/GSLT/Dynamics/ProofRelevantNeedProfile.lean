import Mathlib.Data.Finset.Basic
import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Dynamics.ProofRelevantNeed

/-!
# Modular profiles for proof-relevant need

The cell protocol supplies a maximal vocabulary of exact events.  A language
does not acquire that whole vocabulary by importing it.  Instead it may choose
independently:

* an executable operator fragment;
* a demand-right algebra and a held set of rights;
* an exact decomposition of guest outcomes into cached values, cached stable
  faults, and retryable faults;
* an event valuation such as cost, provenance, evidence, or priority.

These axes are deliberately not bundled into a distinguished `Prime` object.
Operator inclusion gives forward operational translations between fragment
GSLTs.  Rights attenuate fail-closed.  Outcome decompositions are lossless
isomorphisms rather than unproved classifiers.
-/

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Core.InteractionEvent

universe uCell uOrigin uValue uStableFault uRetryableFault uRight uGuest

/-! ## Exact operator fragments -/

/-- The finite event vocabulary of the generic protocol. -/
inductive Operation where
  | allocate
  | resample
  | beginEvaluation
  | commitValue
  | commitStableFault
  | retry
  | observeValue
  | observeStableFault
  | inspectOrigin
deriving DecidableEq, Repr, Fintype

namespace Event

/-- Forget payload and occurrence identity while retaining the exact protocol
operator used by an event. -/
def operation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault} :
    Event Cell Origin Value StableFault RetryableFault -> Operation
  | .allocate _ _ => .allocate
  | .resample _ _ _ => .resample
  | .beginEvaluation _ _ => .beginEvaluation
  | .commitValue _ _ _ => .commitValue
  | .commitStableFault _ _ _ => .commitStableFault
  | .retry _ _ _ => .retry
  | .observeValue _ _ _ => .observeValue
  | .observeStableFault _ _ _ => .observeStableFault
  | .inspectOrigin _ _ => .inspectOrigin

end Event

abbrev OperatorSet := Finset Operation

/-- An exact event whose operator was selected by a language fragment. -/
abbrev AdmittedEvent
    (operators : OperatorSet)
    (Cell : Type uCell) (Origin : Type uOrigin) (Value : Type uValue)
    (StableFault : Type uStableFault)
    (RetryableFault : Type uRetryableFault) :=
  { event : Event Cell Origin Value StableFault RetryableFault //
    event.operation ∈ operators }

/-- Restrict the generic protocol to a selected finite operator vocabulary.
The state carrier is unchanged; only exact event sites are admitted. -/
def fragmentTheory
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (operators : OperatorSet) (RetryableFault : Type uRetryableFault)
    (cell : Cell) : GSLT where
  Term := CellState Origin Value StableFault
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    Nonempty (Σ site : AdmittedEvent operators Cell Origin Value StableFault
      RetryableFault, Step RetryableFault cell source site.1 target)
  rewrites_resp_left := by
    intro source source' target equal edge
    subst source'
    exact ⟨target, edge, rfl⟩
  rewrites_resp_right := by
    intro source target target' edge equal
    subst target'
    exact edge

/-- Proof-relevant sites for an exact operator fragment. -/
def fragmentPresentation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (operators : OperatorSet) (RetryableFault : Type uRetryableFault)
    (cell : Cell) : InteractionPresentation
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) operators RetryableFault cell) where
  Site := AdmittedEvent operators Cell Origin Value StableFault RetryableFault
  Event := fun site source target =>
    Step RetryableFault cell source site.1 target
  sound := fun evidence => ⟨⟨_, evidence⟩⟩

theorem fragmentPresentation_complete
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (operators : OperatorSet) (RetryableFault : Type uRetryableFault)
    (cell : Cell) :
    (fragmentPresentation (Origin := Origin) (Value := Value)
      (StableFault := StableFault) operators RetryableFault cell).Complete := by
  intro source target edge
  rcases edge with ⟨⟨site, evidence⟩⟩
  exact ⟨⟨site, evidence⟩⟩

/-- Adding operators preserves every old equation and exact protocol step.
This is the forward, non-reflecting arrow appropriate to an open extension. -/
def fragmentInclusion
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {smaller larger : OperatorSet} (included : smaller ⊆ larger)
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    OperationalTranslation
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) smaller RetryableFault cell)
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) larger RetryableFault cell) where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  mapStep := by
    intro source target edge
    rcases edge with ⟨⟨site, evidence⟩⟩
    exact ⟨⟨⟨site.1, included site.2⟩, evidence⟩⟩

theorem fragmentInclusion_refl
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} (operators : OperatorSet)
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    fragmentInclusion (Origin := Origin) (Value := Value)
      (StableFault := StableFault) (fun _ member => member)
      RetryableFault cell =
    OperationalTranslation.id
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) operators RetryableFault cell) := by
  apply OperationalTranslation.ext
  rfl

theorem fragmentInclusion_trans
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {first middle last : OperatorSet}
    (firstMiddle : first ⊆ middle) (middleLast : middle ⊆ last)
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    fragmentInclusion (Origin := Origin) (Value := Value)
      (StableFault := StableFault)
      (fun _ member => middleLast (firstMiddle member)) RetryableFault cell =
    OperationalTranslation.comp
      (fragmentInclusion (Origin := Origin) (Value := Value)
        (StableFault := StableFault) firstMiddle RetryableFault cell)
      (fragmentInclusion (Origin := Origin) (Value := Value)
        (StableFault := StableFault) middleLast RetryableFault cell) := by
  apply OperationalTranslation.ext
  rfl

/-- Pure call-by-need: cache successful values and permit origin inspection,
but expose neither fault class. -/
def pureNeedOperators : OperatorSet :=
  {.allocate, .resample, .beginEvaluation, .commitValue,
    .observeValue, .inspectOrigin}

/-- Add stable-fault memoization without adding retry. -/
def stableFaultNeedOperators : OperatorSet :=
  pureNeedOperators ∪ {.commitStableFault, .observeStableFault}

/-- The maximal protocol vocabulary.  A concrete language may select any
smaller fragment. -/
def allNeedOperators : OperatorSet := Finset.univ

theorem pureNeedOperators_subset_stableFault :
    pureNeedOperators ⊆ stableFaultNeedOperators := by
  intro operation member
  simp [stableFaultNeedOperators, member]

theorem stableFaultNeedOperators_subset_all :
    stableFaultNeedOperators ⊆ allNeedOperators := by
  intro operation member
  simp [allNeedOperators]

/-! ## Demand boundaries are an independent axis -/

/-- A demand algebra assigns a finite set of rights required to invoke each
public protocol operation.  It does not choose which operations exist. -/
structure DemandBoundary where
  Right : Type uRight
  decEq : DecidableEq Right
  required : Operation -> Finset Right

namespace DemandBoundary

/-- Executable form of permission checking. -/
def permits (boundary : DemandBoundary.{uRight})
    (held : Finset boundary.Right) (operation : Operation) : Bool := by
  letI := boundary.decEq
  exact decide (boundary.required operation ⊆ held)

/-- A held set permits an operation exactly when it contains every declared
right required by that operation. -/
def Permits (boundary : DemandBoundary.{uRight})
    (held : Finset boundary.Right) (operation : Operation) : Prop :=
  boundary.permits held operation = true

theorem permits_iff (boundary : DemandBoundary.{uRight})
    (held : Finset boundary.Right) (operation : Operation) :
    boundary.Permits held operation ↔
      boundary.required operation ⊆ held := by
  letI := boundary.decEq
  simp [Permits, permits]

/-- Attenuation is fail-closed: it returns precisely the requested subset or
rejects the escalation. -/
def restrict? (boundary : DemandBoundary.{uRight})
    (current requested : Finset boundary.Right) :
    Option (Finset boundary.Right) := by
  letI := boundary.decEq
  exact if requested ⊆ current then some requested else none

theorem restrict_some_subset (boundary : DemandBoundary.{uRight})
    {current requested granted : Finset boundary.Right}
    (restricted : boundary.restrict? current requested = some granted) :
    granted ⊆ current := by
  letI := boundary.decEq
  unfold restrict? at restricted
  split at restricted <;> simp_all

theorem restrict_some_eq_requested (boundary : DemandBoundary.{uRight})
    {current requested granted : Finset boundary.Right}
    (restricted : boundary.restrict? current requested = some granted) :
    granted = requested := by
  letI := boundary.decEq
  unfold restrict? at restricted
  split at restricted <;> simp_all

theorem restrict_escalation_fails (boundary : DemandBoundary.{uRight})
    {current requested : Finset boundary.Right}
    (escalates : ¬ requested ⊆ current) :
    boundary.restrict? current requested = none := by
  letI := boundary.decEq
  simp [restrict?, escalates]

/-- Apply a demand boundary to a separately chosen operator vocabulary. -/
def publicOperators (boundary : DemandBoundary.{uRight})
    (operators : OperatorSet) (held : Finset boundary.Right) : OperatorSet := by
  exact operators.filter fun operation =>
    boundary.permits held operation = true

theorem publicOperators_mono_rights (boundary : DemandBoundary.{uRight})
    (operators : OperatorSet) {smaller larger : Finset boundary.Right}
    (included : smaller ⊆ larger) :
    boundary.publicOperators operators smaller ⊆
      boundary.publicOperators operators larger := by
  letI := boundary.decEq
  intro operation member
  simp only [publicOperators, Finset.mem_filter] at member ⊢
  refine ⟨member.1, ?_⟩
  change boundary.Permits larger operation
  apply (boundary.permits_iff larger operation).2
  have permittedSmaller : boundary.Permits smaller operation := member.2
  have requiredSmaller :=
    (boundary.permits_iff smaller operation).1 permittedSmaller
  exact fun right required => included (requiredSmaller required)

theorem publicOperators_mono_vocabulary
    (boundary : DemandBoundary.{uRight})
    {smaller larger : OperatorSet} (held : Finset boundary.Right)
    (included : smaller ⊆ larger) :
    boundary.publicOperators smaller held ⊆
      boundary.publicOperators larger held := by
  letI := boundary.decEq
  intro operation member
  simp only [publicOperators, Finset.mem_filter] at member ⊢
  exact ⟨included member.1, member.2⟩

end DemandBoundary

/-- One useful demand vocabulary; it is an instance, not part of the generic
cell protocol. -/
inductive StandardRight where
  | force
  | inspect
  | resample
deriving DecidableEq, Repr

/-- A conventional boundary in which allocation is internal, forcing covers
evaluation/commit/observation, inspection is separate, and resampling is a
separate capability. -/
def standardDemandBoundary : DemandBoundary where
  Right := StandardRight
  decEq := inferInstance
  required
    | .allocate => ∅
    | .resample => {.resample}
    | .beginEvaluation => {.force}
    | .commitValue => {.force}
    | .commitStableFault => {.force}
    | .retry => {.force}
    | .observeValue => {.force}
    | .observeStableFault => {.force}
    | .inspectOrigin => {.inspect}

/-! ## Exact guest-outcome decompositions -/

/-- A language chooses its Need outcome algebra by giving an exact
decomposition, not merely a one-way classifier. -/
structure OutcomeAlgebra (GuestOutcome : Type uGuest) where
  Value : Type uValue
  StableFault : Type uStableFault
  RetryableFault : Type uRetryableFault
  encode : GuestOutcome -> Outcome Value StableFault RetryableFault
  decode : Outcome Value StableFault RetryableFault -> GuestOutcome
  decode_encode : ∀ outcome, decode (encode outcome) = outcome
  encode_decode : ∀ outcome, encode (decode outcome) = outcome

namespace OutcomeAlgebra

/-- The already-polarized outcome sum is its own exact algebra. -/
def identity (Value : Type uValue) (StableFault : Type uStableFault)
    (RetryableFault : Type uRetryableFault) :
    OutcomeAlgebra (Outcome Value StableFault RetryableFault) where
  Value := Value
  StableFault := StableFault
  RetryableFault := RetryableFault
  encode := id
  decode := id
  decode_encode := fun _ => rfl
  encode_decode := fun _ => rfl

/-- A pure guest has successful values and no fault constructors. -/
def pure (Value : Type uValue) : OutcomeAlgebra Value where
  Value := Value
  StableFault := Empty
  RetryableFault := Empty
  encode := .value
  decode
    | .value value => value
    | .stableFault impossible => nomatch impossible
    | .retryableFault impossible => nomatch impossible
  decode_encode := fun _ => rfl
  encode_decode := by
    intro outcome
    cases outcome with
    | value => rfl
    | stableFault impossible => exact nomatch impossible
    | retryableFault impossible => exact nomatch impossible

/-- A guest with memoized faults but no retryable fault class. -/
def stableFault (Value : Type uValue) (StableFault : Type uStableFault) :
    OutcomeAlgebra (Sum Value StableFault) where
  Value := Value
  StableFault := StableFault
  RetryableFault := Empty
  encode
    | .inl value => .value value
    | .inr fault => .stableFault fault
  decode
    | .value value => .inl value
    | .stableFault fault => .inr fault
    | .retryableFault impossible => nomatch impossible
  decode_encode := by intro outcome; cases outcome <;> rfl
  encode_decode := by
    intro outcome
    cases outcome with
    | value => rfl
    | stableFault => rfl
    | retryableFault impossible => exact nomatch impossible

end OutcomeAlgebra

/-! ## Separating canaries -/

namespace ProfileCanary

abbrev DemoState := CellState Nat Nat Nat

theorem evaluating_to_suspended_is_retry
    {event : Event Nat Nat Nat Nat Nat}
    (evidence : Step Nat 0 (.evaluating 7) event (.suspended 7)) :
    event.operation = .retry := by
  cases evidence
  rfl

def retryStepInAll :
    (fragmentTheory (Origin := Nat) (Value := Nat) (StableFault := Nat)
      allNeedOperators Nat 0).Step (.evaluating 7) (.suspended 7) :=
  ⟨⟨⟨.retry 0 7 99, by simp [allNeedOperators]⟩, .retry 7 99⟩⟩

/-- Negative canary: the pure fragment genuinely omits retry. -/
theorem retryStepNotInPure :
    ¬ (fragmentTheory (Origin := Nat) (Value := Nat) (StableFault := Nat)
      pureNeedOperators Nat 0).Step (.evaluating 7) (.suspended 7) := by
  rintro ⟨⟨site, evidence⟩⟩
  have retryOperator := evaluating_to_suspended_is_retry evidence
  have admitted := site.property
  rw [retryOperator] at admitted
  simp [pureNeedOperators] at admitted

/-- Therefore no identity-on-states forward translation can erase the retry
operator from the maximal fragment into the pure fragment. -/
theorem no_identity_translation_all_to_pure :
    ¬ ∃ translation : OperationalTranslation
      (fragmentTheory (Origin := Nat) (Value := Nat) (StableFault := Nat)
        allNeedOperators Nat 0)
      (fragmentTheory (Origin := Nat) (Value := Nat) (StableFault := Nat)
        pureNeedOperators Nat 0),
      translation.mapTerm = id := by
  rintro ⟨translation, identityMap⟩
  have mapped := translation.mapStep retryStepInAll
  simp only [identityMap, id_eq] at mapped
  exact retryStepNotInPure mapped

def inspectRights : Finset StandardRight := {.inspect}
def forceInspectRights : Finset StandardRight := {.force, .inspect}

theorem inspect_only_exposes_inspection :
    Operation.inspectOrigin ∈
      standardDemandBoundary.publicOperators allNeedOperators inspectRights ∧
    Operation.beginEvaluation ∉
      standardDemandBoundary.publicOperators allNeedOperators inspectRights := by
  decide

theorem adding_force_exposes_evaluation :
    Operation.beginEvaluation ∈
      standardDemandBoundary.publicOperators allNeedOperators
        forceInspectRights := by
  decide

theorem force_cannot_be_minted_from_inspection :
    standardDemandBoundary.restrict? inspectRights forceInspectRights = none := by
  decide

theorem pureOutcome_is_value (value : Nat) :
    (OutcomeAlgebra.pure Nat).encode value = Outcome.value value :=
  rfl

end ProfileCanary

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed
