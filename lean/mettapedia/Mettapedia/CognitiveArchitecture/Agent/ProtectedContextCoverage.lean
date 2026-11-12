import Std

/-!
# Protected context coverage with recoverable provenance

Durable evidence is a read-only lookup from occurrence identity to payload.
Occurrence identity includes its source and revision; equal payloads at distinct
identities are not coalesced.  A task policy separately names the occurrences
required in the current context.  This does not require every historical byte
in every prompt.

A successful bounded projection contains either the full payload or a reference
for every required occurrence.  A reference is not claimed to be prompt text:
the composed contract separately requires a consumer whose fetch operation
agrees with the same durable history.  Inline and reference encoding costs are
explicit inputs in abstract cost units; a token bound requires supplying an
actual token-cost model.  Missing identities, temporarily unavailable sources,
and insufficient budgets are distinct explicit errors.  In particular,
returning an empty successful view after dropping required evidence is not an
admissible compaction rule.

Projection and assembly are pure functions of a history snapshot.  The composed
runner returns that same history alongside its result, making noninterference
with durable evidence part of the checked interface.  These are model theorems,
not a verification claim about a particular native ledger or renderer.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.ProtectedContextCoverage

universe u v

variable {Id : Type u} {Payload : Type v}

/-- Immutable evidence addressed by occurrence identity. -/
structure History (Id : Type u) (Payload : Type v) where
  read : Id → Option Payload

/-- One resolved occurrence; the identity is retained alongside its payload. -/
structure Occurrence (Id : Type u) (Payload : Type v) where
  id : Id
  payload : Payload
  deriving DecidableEq, Repr

/-- A prompt item is either full evidence or a supported provenance reference. -/
inductive Item (Id : Type u) (Payload : Type v) where
  | inline (occurrence : Occurrence Id Payload)
  | reference (id : Id)
  deriving DecidableEq, Repr

namespace Item

def id : Item Id Payload → Id
  | .inline occurrence => occurrence.id
  | .reference id => id

/-- Inline evidence is already resolved; a reference uses durable provenance. -/
def resolve [DecidableEq Id] (history : History Id Payload) : Item Id Payload → Option Payload
  | .inline occurrence => some occurrence.payload
  | .reference id => history.read id

end Item

/-- Failure to prepare a required view is never identified with empty history. -/
inductive PreparationError (Id : Type u) where
  | absent (id : Id)
  | unavailable (id : Id)
  | insufficientBudget
  deriving DecidableEq, Repr

/-- Resolve the policy's required occurrences in policy order. -/
def resolveRequired [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) : List Id →
      Except (PreparationError Id) (List (Occurrence Id Payload))
  | [] => .ok []
  | id :: rest =>
      match history.read id with
      | none => .error (.absent id)
      | some payload =>
          if available id then
            match resolveRequired history available rest with
            | .ok occurrences => .ok (⟨id, payload⟩ :: occurrences)
            | .error error => .error error
          else .error (.unavailable id)

def inlineItems (occurrences : List (Occurrence Id Payload)) : List (Item Id Payload) :=
  occurrences.map Item.inline

def referenceItems (occurrences : List (Occurrence Id Payload)) : List (Item Id Payload) :=
  occurrences.map fun occurrence => .reference occurrence.id

def itemCost (measure : Payload → Nat) (referenceCost : Id → Nat) : Item Id Payload → Nat
  | .inline occurrence => measure occurrence.payload + 1
  | .reference id => referenceCost id

def viewCost (measure : Payload → Nat) (referenceCost : Id → Nat) (fixed : Nat)
    (items : List (Item Id Payload)) : Nat :=
  fixed + (items.map (itemCost measure referenceCost)).sum

/-- Full inline evidence is preferred.  If it does not fit, the algorithm may
use references only when the complete required reference index fits.  No item
is silently removed to make a view appear successful. -/
def project [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) (required : List Id) (measure : Payload → Nat)
    (referenceCost : Id → Nat) (fixed budget : Nat) : Except (PreparationError Id) (List (Item Id Payload)) :=
  match resolveRequired history available required with
  | .error error => .error error
  | .ok occurrences =>
      let inline := inlineItems occurrences
      if viewCost measure referenceCost fixed inline ≤ budget then
        .ok inline
      else
        let references := referenceItems occurrences
        if viewCost measure referenceCost fixed references ≤ budget then
          .ok references
        else .error .insufficientBudget

structure Prompt (Id : Type u) (Payload : Type v) where
  items : List (Item Id Payload)
  deriving DecidableEq, Repr

/-- Protected assembly adds no evidence and drops no projected item. -/
def assemble (items : List (Item Id Payload)) : Prompt Id Payload := ⟨items⟩

/-- The concrete record → project → assemble pipeline. -/
def prepare [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) (required : List Id) (measure : Payload → Nat)
    (referenceCost : Id → Nat) (fixed budget : Nat) : Except (PreparationError Id) (Prompt Id Payload) :=
  (project history available required measure referenceCost fixed budget).map assemble

/-- The runner exposes history preservation rather than relying on an informal
promise that formatting has no storage effects. -/
structure RunResult (Id : Type u) (Payload : Type v) where
  history : History Id Payload
  outcome : Except (PreparationError Id) (Prompt Id Payload)

def run [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) (required : List Id) (measure : Payload → Nat)
    (referenceCost : Id → Nat) (fixed budget : Nat) : RunResult Id Payload :=
  ⟨history, prepare history available required measure referenceCost fixed budget⟩

@[simp] theorem run_preserves_history [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) (required : List Id) (measure : Payload → Nat)
    (referenceCost : Id → Nat) (fixed budget : Nat) :
    (run history available required measure referenceCost fixed budget).history = history := rfl

/-- Coverage is occurrence-indexed: each required identity has a durable payload
and a projected item with that same provenance resolving to that payload. -/
def Covers [DecidableEq Id] (history : History Id Payload)
    (items : List (Item Id Payload)) (required : List Id) : Prop :=
  ∀ id ∈ required, ∃ occurrence : Occurrence Id Payload,
    occurrence.id = id ∧ history.read id = some occurrence.payload ∧
      ∃ item ∈ items, item.id = id ∧ item.resolve history = some occurrence.payload

/-- The eventual reference consumer is an explicit part of the contract. -/
structure Consumer (Id : Type u) (Payload : Type v) where
  fetch : Id → Option Payload

/-- Consumer fetchability means agreement with durable occurrence payloads,
not merely the existence of an arbitrary resolver in the proof. -/
def ConsumerAgrees (history : History Id Payload) (consumer : Consumer Id Payload) : Prop :=
  ∀ id, consumer.fetch id = history.read id

namespace Item

def resolveConsumer (consumer : Consumer Id Payload) : Item Id Payload → Option Payload
  | .inline occurrence => some occurrence.payload
  | .reference id => consumer.fetch id

end Item

/-- Coverage observed by the declared consumer.  References carry provenance,
not immediate inline text; consumer resolution is what supplies their payload. -/
def ConsumerCovers (history : History Id Payload) (consumer : Consumer Id Payload)
    (items : List (Item Id Payload)) (required : List Id) : Prop :=
  ∀ id ∈ required, ∃ occurrence : Occurrence Id Payload,
    occurrence.id = id ∧ history.read id = some occurrence.payload ∧
      ∃ item ∈ items, item.id = id ∧
        item.resolveConsumer consumer = some occurrence.payload

/-! ## Resolution and general coverage -/

theorem resolveRequired_sound [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) (required : List Id)
    (occurrences : List (Occurrence Id Payload))
    (resolved : resolveRequired history available required = .ok occurrences) :
    occurrences.map Occurrence.id = required ∧
      ∀ occurrence ∈ occurrences, history.read occurrence.id = some occurrence.payload := by
  induction required generalizing occurrences with
  | nil =>
      simp only [resolveRequired, Except.ok.injEq] at resolved
      subst occurrences
      exact ⟨rfl, by simp⟩
  | cons id rest ih =>
      simp only [resolveRequired] at resolved
      split at resolved
      · contradiction
      · rename_i payload read
        split at resolved
        · rename_i sourceAvailable
          split at resolved
          · rename_i tail tailResolved
            cases resolved
            have tailSound := ih tail tailResolved
            constructor
            · simp only [List.map_cons]
              rw [tailSound.1]
            · intro occurrence member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact read
              · exact tailSound.2 occurrence member
          · contradiction
        · contradiction

theorem covers_inline [DecidableEq Id] (history : History Id Payload)
    (required : List Id) (occurrences : List (Occurrence Id Payload))
    (sound : occurrences.map Occurrence.id = required ∧
      ∀ occurrence ∈ occurrences, history.read occurrence.id = some occurrence.payload) :
    Covers history (inlineItems occurrences) required := by
  intro id member
  have mapped : id ∈ occurrences.map Occurrence.id := by
    rw [sound.1]
    exact member
  obtain ⟨occurrence, occurrenceMember, identity⟩ := List.mem_map.mp mapped
  refine ⟨occurrence, identity, ?_, ?_⟩
  · rw [← identity]
    exact sound.2 occurrence occurrenceMember
  · refine ⟨.inline occurrence, ?_, identity, rfl⟩
    exact List.mem_map.mpr ⟨occurrence, occurrenceMember, rfl⟩

theorem covers_references [DecidableEq Id] (history : History Id Payload)
    (required : List Id) (occurrences : List (Occurrence Id Payload))
    (sound : occurrences.map Occurrence.id = required ∧
      ∀ occurrence ∈ occurrences, history.read occurrence.id = some occurrence.payload) :
    Covers history (referenceItems occurrences) required := by
  intro id member
  have mapped : id ∈ occurrences.map Occurrence.id := by
    rw [sound.1]
    exact member
  obtain ⟨occurrence, occurrenceMember, identity⟩ := List.mem_map.mp mapped
  refine ⟨occurrence, identity, ?_, ?_⟩
  · rw [← identity]
    exact sound.2 occurrence occurrenceMember
  · refine ⟨.reference occurrence.id, ?_, identity, ?_⟩
    · exact List.mem_map.mpr ⟨occurrence, occurrenceMember, rfl⟩
    · exact sound.2 occurrence occurrenceMember

theorem covers_consumer [DecidableEq Id] (history : History Id Payload)
    (consumer : Consumer Id Payload) (agrees : ConsumerAgrees history consumer)
    (items : List (Item Id Payload)) (required : List Id)
    (covered : Covers history items required) :
    ConsumerCovers history consumer items required := by
  intro id member
  obtain ⟨occurrence, identity, durable, item, itemMember, itemIdentity, resolved⟩ :=
    covered id member
  refine ⟨occurrence, identity, durable, item, itemMember, itemIdentity, ?_⟩
  cases item with
  | inline inlineOccurrence => exact resolved
  | reference referenceId =>
      simp only [Item.resolve] at resolved
      simp only [Item.resolveConsumer]
      rw [agrees]
      exact resolved

/-- Every successful projection covers all required occurrences, whether it
selected inline evidence or the bounded reference index. -/
theorem project_ready_covers [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) (required : List Id) (measure : Payload → Nat)
    (referenceCost : Id → Nat) (fixed budget : Nat) (items : List (Item Id Payload))
    (ready : project history available required measure referenceCost fixed budget = .ok items) :
    Covers history items required := by
  unfold project at ready
  split at ready
  · contradiction
  · rename_i occurrences resolved
    have sound := resolveRequired_sound history available required occurrences resolved
    simp only at ready
    split at ready
    · cases ready
      exact covers_inline history required occurrences sound
    · split at ready
      · cases ready
        exact covers_references history required occurrences sound
      · contradiction

theorem project_ready_bounded [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) (required : List Id) (measure : Payload → Nat)
    (referenceCost : Id → Nat) (fixed budget : Nat) (items : List (Item Id Payload))
    (ready : project history available required measure referenceCost fixed budget = .ok items) :
    viewCost measure referenceCost fixed items ≤ budget := by
  unfold project at ready
  split at ready
  · contradiction
  · simp only at ready
    split at ready
    · rename_i fits
      cases ready
      exact fits
    · split at ready
      · rename_i fits
        cases ready
        exact fits
      · contradiction

theorem prepare_ok_iff_project [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) (required : List Id) (measure : Payload → Nat)
    (referenceCost : Id → Nat) (fixed budget : Nat) (prompt : Prompt Id Payload) :
    prepare history available required measure referenceCost fixed budget = .ok prompt ↔
      project history available required measure referenceCost fixed budget = .ok prompt.items := by
  cases prompt
  constructor
  · intro prepared
    unfold prepare at prepared
    cases result : project history available required measure referenceCost fixed budget with
    | error error =>
        rw [result] at prepared
        contradiction
    | ok items =>
        rw [result] at prepared
        cases prepared
        rfl
  · intro projected
    unfold prepare
    rw [projected]
    rfl

/-- Composed record → project → assemble correctness: successful preparation is
bounded in the supplied encoding units, occurrence-complete for the declared
consumer with resolvable provenance, and leaves durable history untouched. -/
theorem prepare_composes [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) (required : List Id) (measure : Payload → Nat)
    (referenceCost : Id → Nat) (fixed budget : Nat)
    (consumer : Consumer Id Payload) (agrees : ConsumerAgrees history consumer)
    (prompt : Prompt Id Payload)
    (ready : prepare history available required measure referenceCost fixed budget = .ok prompt) :
    viewCost measure referenceCost fixed prompt.items ≤ budget ∧
      ConsumerCovers history consumer prompt.items required ∧
        (run history available required measure referenceCost fixed budget).history = history := by
  have projected := (prepare_ok_iff_project history available required measure referenceCost fixed budget prompt).mp ready
  exact ⟨project_ready_bounded history available required measure referenceCost fixed budget prompt.items projected,
    covers_consumer history consumer agrees prompt.items required
      (project_ready_covers history available required measure referenceCost fixed budget prompt.items projected),
    run_preserves_history history available required measure referenceCost fixed budget⟩

/-! ## Non-destructive correction -/

/-- Add a fresh revision without overwriting any existing occurrence. -/
def addFresh [DecidableEq Id] (history : History Id Payload)
    (id : Id) (payload : Payload) : History Id Payload :=
  if (history.read id).isSome then history else
    ⟨fun key => if key = id then some payload else history.read key⟩

theorem addFresh_read_new [DecidableEq Id] (history : History Id Payload)
    (id : Id) (payload : Payload) (fresh : history.read id = none) :
    (addFresh history id payload).read id = some payload := by
  simp [addFresh, fresh]

theorem addFresh_read_old [DecidableEq Id] (history : History Id Payload)
    (newId oldId : Id) (payload : Payload) (different : oldId ≠ newId) :
    (addFresh history newId payload).read oldId = history.read oldId := by
  unfold addFresh
  split <;> simp [different]

theorem correction_retains_original [DecidableEq Id] (history : History Id Payload)
    (originalId correctionId : Id) (original correction : Payload)
    (different : originalId ≠ correctionId)
    (before : history.read originalId = some original)
    (fresh : history.read correctionId = none) :
    let revised := addFresh history correctionId correction
    revised.read originalId = some original ∧ revised.read correctionId = some correction := by
  exact ⟨(addFresh_read_old history correctionId originalId correction different).trans before,
    addFresh_read_new history correctionId correction fresh⟩

/-! ## A silent-truncation counterexample -/

/-- This intentionally defective rule is retained only as a mathematical
counterexample: on overflow it reports success after deleting every item. -/
def legacyProject [DecidableEq Id] (history : History Id Payload)
    (available : Id → Bool) (required : List Id) (measure : Payload → Nat)
    (referenceCost : Id → Nat) (fixed budget : Nat) : Except (PreparationError Id) (List (Item Id Payload)) :=
  match resolveRequired history available required with
  | .error error => .error error
  | .ok occurrences =>
      let inline := inlineItems occurrences
      if viewCost measure referenceCost fixed inline ≤ budget then .ok inline else .ok []

/-! ## Finite controls -/

namespace Controls

abbrev TextHistory := History String String

def ofList : List (String × String) → TextHistory
  | [] => ⟨fun _ => none⟩
  | (id, payload) :: rest =>
      ⟨fun key => if key = id then some payload else (ofList rest).read key⟩

def markerId : String := "guide:0:0"
def marker : String := "ORIGINAL_FINDING_RETAINED"
def markerHistory : TextHistory := ofList [(markerId, marker)]

/-- The concrete required finding reaches the assembled prompt inline when its
full measured representation fits exactly. -/
theorem marker_record_project_assemble :
    prepare markerHistory (fun _ => true) [markerId] String.length (fun _ => 1) 0 (marker.length + 1) =
      .ok ⟨[.inline ⟨markerId, marker⟩]⟩ := by
  rfl

/-- At a smaller budget the same evidence remains covered by a resolvable
reference; it is not reported as absent and is not silently dropped. -/
theorem marker_reference_at_budget_boundary :
    prepare markerHistory (fun _ => true) [markerId] String.length (fun _ => 1) 0 1 =
      .ok ⟨[.reference markerId]⟩ := by
  rfl

def markerConsumer : Consumer String String := ⟨markerHistory.read⟩

theorem marker_reference_is_consumer_fetchable :
    ConsumerAgrees markerHistory markerConsumer ∧
      (Item.reference markerId).resolveConsumer markerConsumer = some marker := by
  exact ⟨fun _ => rfl, rfl⟩

theorem reference_encoding_cost_is_not_assumed_to_be_one :
    prepare markerHistory (fun _ => true) [markerId] String.length (fun _ => 2) 0 1 =
      .error .insufficientBudget := by
  rfl

theorem zero_budget_is_explicitly_not_ready :
    prepare markerHistory (fun _ => true) [markerId] String.length (fun _ => 1) 0 0 =
      .error .insufficientBudget := by
  rfl

theorem unavailable_is_not_absent :
    prepare markerHistory (fun _ => false) [markerId] String.length (fun _ => 1) 0 1000 =
      .error (.unavailable markerId) ∧
    prepare markerHistory (fun _ => true) ["missing"] String.length (fun _ => 1) 0 1000 =
      .error (.absent "missing") := by
  exact ⟨rfl, rfl⟩

theorem legacy_rule_silently_drops_required_marker :
    legacyProject markerHistory (fun _ => true) [markerId] String.length (fun _ => 1) 0 0 = .ok [] ∧
      ¬ Covers markerHistory [] [markerId] := by
  constructor
  · rfl
  · intro covered
    obtain ⟨occurrence, _, _, item, itemMember, _, _⟩ := covered markerId (by simp)
    simp at itemMember

/-- Equal text from two sources remains two occurrence-indexed prompt items. -/
theorem equal_text_distinct_sources :
    let history := ofList [("source-a:0:0", "same observation"),
      ("source-b:0:0", "same observation")]
    let required := ["source-a:0:0", "source-b:0:0"]
    ∃ prompt, prepare history (fun _ => true) required String.length (fun _ => 1) 0 1000 = .ok prompt ∧
      prompt.items.map Item.id = required := by
  exact ⟨⟨[.inline ⟨"source-a:0:0", "same observation"⟩,
    .inline ⟨"source-b:0:0", "same observation"⟩]⟩, rfl, rfl⟩

/-- Adding revision 2 as a correction does not erase revision 1. -/
theorem original_plus_correction :
    let revised := addFresh markerHistory "guide:0:1" "corrected"
    revised.read markerId = some marker ∧ revised.read "guide:0:1" = some "corrected" := by
  decide

end Controls

#print axioms resolveRequired_sound
#print axioms project_ready_covers
#print axioms project_ready_bounded
#print axioms covers_consumer
#print axioms prepare_composes
#print axioms correction_retains_original
#print axioms Controls.marker_record_project_assemble
#print axioms Controls.marker_reference_at_budget_boundary
#print axioms Controls.marker_reference_is_consumer_fetchable
#print axioms Controls.reference_encoding_cost_is_not_assumed_to_be_one
#print axioms Controls.zero_budget_is_explicitly_not_ready
#print axioms Controls.unavailable_is_not_absent
#print axioms Controls.legacy_rule_silently_drops_required_marker
#print axioms Controls.equal_text_distinct_sources
#print axioms Controls.original_plus_correction

end Mettapedia.CognitiveArchitecture.Agent.ProtectedContextCoverage
