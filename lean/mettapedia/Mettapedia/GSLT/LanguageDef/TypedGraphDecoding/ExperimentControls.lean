import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2OEISFragment
import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedFrontier
import Mathlib.Tactic

/-!
# Experiment controls for GSLT-derived typed graph decoding

This module closes three treatment boundaries used by the MM2 and A-P
successor experiment:

* the A-P arity mask is the one-sort instance of the typed frontier;
* a learned reference carrier can rank only actions retained by the hard mask;
* checkpoints are bound to the source, cursor, mask, and carrier-feature
  versions that determined their training observations.

The hard-mask model uses `Option` support.  `none` means absent, rather than a
large finite score.  A negative fixture records why a finite sentinel alone
cannot serve as a proof that an illegal action is absent from beam search.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.ExperimentControls

open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedFrontier

/-! ## A-P as the arity-only placebo -/

namespace APPlacebo

inductive APSort where
  | expression
  deriving Repr, DecidableEq

abbrev Head := Fin 16

/-- Frozen A-P operator arities in operator-id order. -/
def arity (head : Head) : Nat :=
  match head.1 with
  | 0 | 1 | 2 | 10 | 11 => 0
  | 3 | 4 | 5 | 6 | 7 | 12 | 14 => 2
  | 8 | 9 => 3
  | 13 => 5
  | 15 => 1
  | _ => 0

def signature : Signature where
  SortType := APSort
  Head := Head
  resultSort := fun _ => .expression
  childSorts := fun head => List.replicate (arity head) .expression

def sortCost : APSort → Nat := fun _ => 1

/-- The source-independent formula used by the current A-P implementation.
`position` is the number of already selected constructors. -/
def legacyLegal (maxActions position openHoles : Nat) (head : Head) : Prop :=
  position + openHoles + arity head ≤ maxActions

def frontierState (maxActions position openHoles : Nat) : State signature :=
  { holes := List.replicate openHoles .expression
    remaining := maxActions - position }

def frontierAction (head : Head) : Action signature :=
  { holeIndex := 0, head := head }

@[simp] theorem required_next_frontier
    (maxActions position openHoles : Nat) (head : Head) :
    signature.required sortCost
        (signature.nextHoles
          (frontierState maxActions position openHoles)
          (frontierAction head)) =
      arity head + (openHoles - 1) := by
  dsimp [signature, Signature.required, Signature.nextHoles,
    frontierState, frontierAction, sortCost]
  unfold sortCost
  simp

/-- On every reachable incomplete state, typed-frontier legality is exactly
the existing bounded arity predicate.  Consequently replacing the A-P mask
by this derived one is a semantic placebo, not a second treatment. -/
theorem frontierLegal_iff_legacyLegal
    (maxActions position openHoles : Nat) (head : Head)
    (positionWithin : position < maxActions)
    (incomplete : 0 < openHoles) :
    signature.Legal sortCost
        (frontierState maxActions position openHoles)
        (frontierAction head) ↔
      legacyLegal maxActions position openHoles head := by
  have budgetEquivalent :
      1 + signature.required sortCost
          (signature.nextHoles
            (frontierState maxActions position openHoles)
            (frontierAction head)) ≤ maxActions - position ↔
        legacyLegal maxActions position openHoles head := by
    rw [required_next_frontier]
    unfold legacyLegal
    omega
  constructor
  · rintro ⟨_expected, _lookup, _sortMatches, budget⟩
    exact budgetEquivalent.mp budget
  · intro legacy
    refine ⟨APSort.expression, ?_, rfl, budgetEquivalent.mpr legacy⟩
    simp [frontierState, frontierAction, incomplete]

/-- Complete states expose EOS rather than another constructor action. -/
theorem complete_frontier_has_no_constructor_legal
    (maxActions position : Nat) (head : Head) :
    ¬ signature.Legal sortCost
      (frontierState maxActions position 0) (frontierAction head) := by
  simp [Signature.Legal, frontierState, frontierAction]

/-- Negative control: changing the budget inequality from `≤` to `<` is not
placebo-equivalent at the exact completion boundary. -/
theorem strict_budget_variant_differs :
    legacyLegal 1 0 1 ⟨0, by decide⟩ ∧
      ¬ (0 + 1 + arity ⟨0, by decide⟩ < 1) := by
  constructor <;> norm_num [legacyLegal, arity]

end APPlacebo

/-! ## Cursor event vocabulary -/

/-- Sparse language-semantic events exported by an MM2 action cursor.
Events are evidence for a carrier; the cursor's legal set remains the sole
admissibility authority. -/
inductive MM2CursorEvent (Address Name Provider : Type*) where
  | ruleBegin (address : Address)
  | ruleEnd (address : Address)
  | patternBind (name : Name)
  | templateUse (name : Name)
  | definition (address : Address)
  | reference (address : Address)
  | reflectiveCapture (address : Address)
  | demand (address : Address)
  | producer (address : Address)
  | providerObligation (provider : Provider)
  deriving Repr, DecidableEq

/-- Only address-bearing events can read or write reference-addressed memory. -/
def MM2CursorEvent.address? {Address Name Provider : Type*} :
    MM2CursorEvent Address Name Provider → Option Address
  | .ruleBegin address | .ruleEnd address | .definition address |
      .reference address | .reflectiveCapture address | .demand address |
      .producer address => some address
  | .patternBind _ | .templateUse _ | .providerObligation _ => none

@[simp] theorem patternBind_has_no_carrier_address
    {Address Name Provider : Type*} (name : Name) :
    (MM2CursorEvent.patternBind name :
      MM2CursorEvent Address Name Provider).address? = none := rfl

@[simp] theorem reference_has_exact_carrier_address
    {Address Name Provider : Type*} (address : Address) :
    (MM2CursorEvent.reference address :
      MM2CursorEvent Address Name Provider).address? = some address := rfl

/-! ## Cursor-authorized sparse workspace updates -/

namespace CursorWorkspace

universe uAddress uName uProvider uContent

variable {Address : Type uAddress} {Name : Type uName}
  {Provider : Type uProvider} {Content : Type uContent}
  [DecidableEq Address]

/-- A sparse carrier update is authorized only by an address-bearing cursor
event whose address is present in the task-local reference table. -/
def writeIfPresent (present : Finset Address)
    (event : MM2CursorEvent Address Name Provider)
    (update : Address → Content → Content)
    (workspace : Address → Content) : Address → Content :=
  match event.address? with
  | none => workspace
  | some address =>
      if address ∈ present then
        Function.update workspace address (update address (workspace address))
      else workspace

/-- Binding and provider-obligation events do not accidentally perform a
reference-memory write. -/
theorem no_address_event_is_identity (present : Finset Address)
    (event : MM2CursorEvent Address Name Provider)
    (update : Address → Content → Content)
    (workspace : Address → Content)
    (noAddress : event.address? = none) :
    writeIfPresent present event update workspace = workspace := by
  simp [writeIfPresent, noAddress]

/-- An address absent from the authenticated task-local table cannot be
written even if the cursor emits an address-bearing event. -/
theorem absent_address_is_identity (present : Finset Address)
    (event : MM2CursorEvent Address Name Provider)
    (update : Address → Content → Content)
    (workspace : Address → Content) (address : Address)
    (atAddress : event.address? = some address)
    (absent : address ∉ present) :
    writeIfPresent present event update workspace = workspace := by
  simp [writeIfPresent, atAddress, absent]

/-- An authorized event updates exactly its named slot. -/
theorem writeIfPresent_at_authorized_address (present : Finset Address)
    (event : MM2CursorEvent Address Name Provider)
    (update : Address → Content → Content)
    (workspace : Address → Content) (address : Address)
    (atAddress : event.address? = some address)
    (presentAddress : address ∈ present) :
    writeIfPresent present event update workspace address =
      update address (workspace address) := by
  simp [writeIfPresent, atAddress, presentAddress]

/-- The same authorized update leaves every other address unchanged. -/
theorem writeIfPresent_at_other_address (present : Finset Address)
    (event : MM2CursorEvent Address Name Provider)
    (update : Address → Content → Content)
    (workspace : Address → Content) (address other : Address)
    (atAddress : event.address? = some address)
    (presentAddress : address ∈ present) (different : other ≠ address) :
    writeIfPresent present event update workspace other = workspace other := by
  simp [writeIfPresent, atAddress, presentAddress, different]

/-- Negative control: a broadcast update does not implement cursor-addressed
memory.  It changes the other slot that the sparse update preserves. -/
theorem broadcast_write_violates_address_isolation :
    let present : Finset Bool := {false, true}
    let workspace : Bool → Nat := fun _ => 0
    let update : Bool → Nat → Nat := fun _ value => value + 1
    let event : MM2CursorEvent Bool Unit Unit := .reference false
    writeIfPresent present event update workspace false = 1 ∧
      writeIfPresent present event update workspace true = 0 ∧
      (fun _ : Bool => 1) true = 1 := by
  decide +kernel

end CursorWorkspace

/-! ## Hard-mask and carrier non-interference -/

namespace CarrierMask

universe uAction

variable {Action : Type uAction} [DecidableEq Action]

/-- An absent action has no score.  This is the semantic hard-mask carrier. -/
def maskedScore (legal : Finset Action) (base carrier : Action → ℝ)
    (action : Action) : Option ℝ :=
  if action ∈ legal then some (base action + carrier action) else none

/-- A scalar output gate makes the carrier contribution explicit. -/
def gatedCarrier (gate : ℝ) (readout : Action → ℝ) (action : Action) : ℝ :=
  gate * readout action

omit [DecidableEq Action] in
@[simp] theorem gatedCarrier_zero (readout : Action → ℝ) :
    gatedCarrier 0 readout = 0 := by
  funext action
  simp [gatedCarrier]

def support [Fintype Action] (score : Action → Option ℝ) : Finset Action :=
  Finset.univ.filter fun action => (score action).isSome

/-- Arbitrary learned carrier values cannot add or remove actions when the
hard mask owns support. -/
theorem support_maskedScore [Fintype Action] (legal : Finset Action)
    (base carrier : Action → ℝ) :
    support (maskedScore legal base carrier) = legal := by
  ext action
  simp [support, maskedScore]

/-- A zero carrier is observationally identical to the carrier-free scores
on legal actions and remains absent on illegal actions. -/
theorem cold_carrier_identity (legal : Finset Action) (base : Action → ℝ) :
    maskedScore legal base (fun _ => 0) =
      fun action => if action ∈ legal then some (base action) else none := by
  funext action
  by_cases member : action ∈ legal <;> simp [maskedScore, member]

/-- A zero output gate gives the exact carrier-free hard-masked scorer even
when the hidden workspace and its readout are nonzero. -/
theorem zero_gate_maskedScore_identity (legal : Finset Action)
    (base readout : Action → ℝ) :
    maskedScore legal base (gatedCarrier 0 readout) =
      fun action => if action ∈ legal then some (base action) else none := by
  funext action
  by_cases member : action ∈ legal <;>
    simp [maskedScore, gatedCarrier, member]

/-- A beam is support-respecting when every retained action has a real score.
This condition must be enforced by filtering, not inferred from magnitude. -/
def BeamRespectsSupport (score : Action → Option ℝ)
    (beam : List Action) : Prop :=
  ∀ action ∈ beam, (score action).isSome = true

theorem legal_of_mem_supportRespectingBeam
    (legal : Finset Action) (base carrier : Action → ℝ)
    (beam : List Action)
    (respects : BeamRespectsSupport (maskedScore legal base carrier) beam)
    {action : Action} (member : action ∈ beam) :
    action ∈ legal := by
  have scored := respects action member
  simpa [maskedScore] using scored

/-- Masking before or after a learned update is equivalent in the support
model because absent actions cannot be modified. -/
def addCarrier (carrier : Action → ℝ) :
    Option ℝ → Action → Option ℝ
  | none, _ => none
  | some score, action => some (score + carrier action)

theorem addCarrier_masked_base_eq_maskedScore
    (legal : Finset Action) (base carrier : Action → ℝ) (action : Action) :
    addCarrier carrier
        (if action ∈ legal then some (base action) else none) action =
      maskedScore legal base carrier action := by
  by_cases member : action ∈ legal <;>
    simp [addCarrier, maskedScore, member]

/-- A finite sentinel is merely a low score: a later finite bias can make an
illegal action outrank a legal zero score. -/
theorem finite_sentinel_can_be_resurrected :
    (-1000000000 : ℝ) + 2000000000 > 0 := by
  norm_num

/-- Even when the finite sentinel is written last, it does not encode absence.
With two actions, a width-two candidate list necessarily retains the illegal
action despite its lower finite score. -/
theorem finite_sentinel_two_wide_list_is_not_support_safe :
    let legal : Finset (Fin 2) := {0}
    let finiteScore : Fin 2 → ℝ := fun action =>
      if action ∈ legal then 0 else -1000000000
    let beam : List (Fin 2) := [0, 1]
    finiteScore 0 > finiteScore 1 ∧
      beam.Nodup ∧ beam.length = 2 ∧
      1 ∈ beam ∧ 1 ∉ legal := by
  norm_num

end CarrierMask

/-! ## Source-bound checkpoint compatibility -/

/-- Every semantic input that changes legality or carrier meaning has its own
identity.  Distinct fields prevent one digest from masquerading as another. -/
structure DecoderSemanticVersion where
  languageSourceIdentity : String
  profileIdentity : String
  contextIdentity : String
  actionEncodingIdentity : String
  cursorIdentity : String
  maskIdentity : String
  carrierFeatureIdentity : String
  deriving Repr, DecidableEq

structure CheckpointBinding where
  checkpointIdentity : String
  semanticVersion : DecoderSemanticVersion
  deriving Repr, DecidableEq

def CheckpointBinding.CanEvaluateWith (checkpoint : CheckpointBinding)
    (runtime : DecoderSemanticVersion) : Prop :=
  checkpoint.semanticVersion = runtime

theorem checkpoint_rejects_changed_mask (checkpoint : CheckpointBinding)
    (runtime : DecoderSemanticVersion)
    (changedMask : checkpoint.semanticVersion.maskIdentity ≠ runtime.maskIdentity) :
    ¬ checkpoint.CanEvaluateWith runtime := by
  intro compatible
  have maskEquality := congrArg DecoderSemanticVersion.maskIdentity compatible
  exact changedMask maskEquality

theorem checkpoint_rejects_changed_cursor (checkpoint : CheckpointBinding)
    (runtime : DecoderSemanticVersion)
    (changedCursor :
      checkpoint.semanticVersion.cursorIdentity ≠ runtime.cursorIdentity) :
    ¬ checkpoint.CanEvaluateWith runtime := by
  intro compatible
  exact changedCursor
    (congrArg DecoderSemanticVersion.cursorIdentity compatible)

private def versionFixture : DecoderSemanticVersion := {
  languageSourceIdentity := "mm2-language-v1"
  profileIdentity := "oeis-reflective-v1"
  contextIdentity := "oeis-context-v1"
  actionEncodingIdentity := "preorder-v1"
  cursorIdentity := "mm2-cursor-v1"
  maskIdentity := "mm2-mask-v1"
  carrierFeatureIdentity := "reference-events-v1"
}

private def checkpointFixture : CheckpointBinding := {
  checkpointIdentity := "checkpoint-a"
  semanticVersion := versionFixture
}

private def changedMaskFixture : DecoderSemanticVersion :=
  { versionFixture with maskIdentity := "mm2-mask-v2" }

theorem changed_mask_fixture_is_incompatible :
    ¬ checkpointFixture.CanEvaluateWith changedMaskFixture := by
  intro compatible
  have maskEquality :=
    congrArg DecoderSemanticVersion.maskIdentity compatible
  change ("mm2-mask-v1" : String) = "mm2-mask-v2" at maskEquality
  exact (by decide : ("mm2-mask-v1" : String) ≠ "mm2-mask-v2") maskEquality

#print axioms APPlacebo.frontierLegal_iff_legacyLegal
#print axioms APPlacebo.complete_frontier_has_no_constructor_legal
#print axioms APPlacebo.strict_budget_variant_differs
#print axioms CarrierMask.support_maskedScore
#print axioms CarrierMask.cold_carrier_identity
#print axioms CarrierMask.zero_gate_maskedScore_identity
#print axioms CarrierMask.legal_of_mem_supportRespectingBeam
#print axioms CursorWorkspace.no_address_event_is_identity
#print axioms CursorWorkspace.absent_address_is_identity
#print axioms CursorWorkspace.writeIfPresent_at_other_address
#print axioms CursorWorkspace.broadcast_write_violates_address_isolation
#print axioms CarrierMask.finite_sentinel_can_be_resurrected
#print axioms CarrierMask.finite_sentinel_two_wide_list_is_not_support_safe
#print axioms checkpoint_rejects_changed_mask
#print axioms checkpoint_rejects_changed_cursor
#print axioms changed_mask_fixture_is_incompatible

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.ExperimentControls
