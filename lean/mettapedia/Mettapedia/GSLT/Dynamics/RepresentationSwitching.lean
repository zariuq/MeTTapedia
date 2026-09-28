import Mettapedia.GSLT.Dynamics.RegionHoleRealizationTransformation
import Mettapedia.GraphTheory.Representation.CostModel

/-!
# Switching realizations during an ordered computation

A realization comparison is not yet an execution which alternates between
representations. Here the engine is an additional path index. Execution may
cross a certified representation boundary between any two source operations.
Erasing those boundaries retains the exact Region/Hole plan. Its denotation
agrees with the mixed execution after decoding the final residual state.

The target observation must include everything the continuation can observe.
In particular, equality of the latest returned value is not an adequate
decoder for a suspended search. Conversion costs are retained separately:
erasing a switch from the semantic plan does not erase its resource receipt.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RepresentationSwitching

open RegionHolePlan
open Mettapedia.GraphTheory.Representation

universe uObj uRegion uHole uTargetObj uTarget uEngine

variable {Obj : Type uObj} {Region : Obj → Obj → Type uRegion}
  {Hole : Obj → Obj → Type uHole}
  {TargetObj : Type uTargetObj} {Target : TargetObj → TargetObj → Type uTarget}
  {Engine : Type uEngine}
  {source : IndexedCategory Obj Region}
  {target : IndexedCategory TargetObj Target}

/-- The common reference interprets residual computation, not just an answer.
Every engine supplies its local region and hole squares through the existing
realization-transformation interface. -/
structure Family (source : IndexedCategory Obj Region)
    (Hole : Obj → Obj → Type uHole)
    (target : IndexedCategory TargetObj Target) (Engine : Type uEngine) where
  reference : Realization source Hole target
  engine : Engine → Realization source Hole target
  decode : (mode : Engine) → RealizationTransformation (engine mode) reference

/-- A boundary is licensed by preservation of the whole decoded state.
Resource costs are additional data, never evidence of semantic admission. -/
structure Transfer (family : Family source Hole target Engine)
    (originMode destinationMode : Engine) (position : Obj) where
  convert : Target ((family.engine originMode).objectMap position)
    ((family.engine destinationMode).objectMap position)
  commutes : target.compose convert ((family.decode destinationMode).component position) =
    (family.decode originMode).component position
  resources : Resources

/-- A typed route through engines and source program positions. The switch
constructor cannot change the source position or consume an authored hole. -/
inductive Execution (family : Family source Hole target Engine) :
    Engine → Obj → Engine → Obj → Type (max uObj uRegion uHole uTarget uEngine)
  | done (mode : Engine) (position : Obj) : Execution family mode position mode position
  | region {mode last : Engine} {X Y Z : Obj}
      (arrow : Region X Y) (rest : Execution family mode Y last Z) :
      Execution family mode X last Z
  | hole {mode last : Engine} {X Y Z : Obj}
      (opening : Hole X Y) (rest : Execution family mode Y last Z) :
      Execution family mode X last Z
  | switch {originMode destinationMode last : Engine} {X Y : Obj}
      (boundary : Transfer family originMode destinationMode X)
      (rest : Execution family destinationMode X last Y) : Execution family originMode X last Y

namespace Execution

variable {family : Family source Hole target Engine}

/-- Execute a source plan entirely in one realization. This is the reference
choice available when an optimized boundary is not admitted. -/
def stay (mode : Engine) : {X Y : Obj} → Plan Obj Region Hole X Y →
    Execution family mode X mode Y
  | _, _, .nil position => .done mode position
  | _, _, .region arrow rest => .region arrow (stay mode rest)
  | _, _, .hole opening rest => .hole opening (stay mode rest)

def erase : {originMode destinationMode : Engine} → {X Y : Obj} →
    Execution family originMode X destinationMode Y → Plan Obj Region Hole X Y
  | _, _, _, _, .done _ position => .nil position
  | _, _, _, _, .region arrow rest => .region arrow rest.erase
  | _, _, _, _, .hole opening rest => .hole opening rest.erase
  | _, _, _, _, .switch _ rest => rest.erase

def denote : {originMode destinationMode : Engine} → {X Y : Obj} →
    Execution family originMode X destinationMode Y →
    Target ((family.engine originMode).objectMap X) ((family.engine destinationMode).objectMap Y)
  | mode, _, position, _, .done _ _ => target.identity ((family.engine mode).objectMap position)
  | mode, _, _, _, .region arrow rest =>
      target.compose ((family.engine mode).mapRegion arrow) rest.denote
  | mode, _, _, _, .hole opening rest =>
      target.compose ((family.engine mode).mapHole opening) rest.denote
  | _, _, _, _, .switch boundary rest =>
      target.compose boundary.convert rest.denote

@[simp] theorem erase_stay (mode : Engine) {X Y : Obj}
    (plan : Plan Obj Region Hole X Y) : (stay (family := family) mode plan).erase = plan := by
  induction plan with
  | nil => rfl
  | region arrow rest ih => simp [stay, erase, ih]
  | hole opening rest ih => simp [stay, erase, ih]

def append : {first middle last : Engine} → {X Y Z : Obj} →
    Execution family first X middle Y → Execution family middle Y last Z →
    Execution family first X last Z
  | _, _, _, _, _, _, .done _ _, later => later
  | _, _, _, _, _, _, .region arrow rest, later => .region arrow (rest.append later)
  | _, _, _, _, _, _, .hole opening rest, later => .hole opening (rest.append later)
  | _, _, _, _, _, _, .switch boundary rest, later =>
      .switch boundary (rest.append later)

/-- Arbitrarily many switches, including a return to an earlier engine,
preserve the complete declared observation. No inverse on raw storage is
required, and no appeal to pointer identity is made. -/
theorem denote_decode {originMode destinationMode : Engine} {X Y : Obj}
    (execution : Execution family originMode X destinationMode Y) :
    target.compose execution.denote ((family.decode destinationMode).component Y) =
      target.compose ((family.decode originMode).component X)
        (Plan.denote family.reference execution.erase) := by
  induction execution with
  | done mode position => simp [denote, erase,
      target.identity_compose, target.compose_identity]
  | @region mode last X Y Z arrow rest ih =>
      simp only [denote, erase, Plan.denote]
      rw [target.compose_assoc, ih, ← target.compose_assoc,
        (family.decode mode).region_naturality, target.compose_assoc]
  | @hole mode last X Y Z opening rest ih =>
      simp only [denote, erase, Plan.denote]
      rw [target.compose_assoc, ih, ← target.compose_assoc,
        (family.decode mode).hole_naturality, target.compose_assoc]
  | switch boundary rest ih =>
      simp only [denote, erase]
      rw [target.compose_assoc, ih, ← target.compose_assoc, boundary.commutes]

theorem erase_append {first middle last : Engine} {X Y Z : Obj}
    (earlier : Execution family first X middle Y)
    (later : Execution family middle Y last Z) :
    (earlier.append later).erase = earlier.erase.append later.erase := by
  induction earlier with
  | done => rfl
  | region arrow rest ih => simp [append, erase, Plan.append, ih]
  | hole opening rest ih => simp [append, erase, Plan.append, ih]
  | switch boundary rest ih => simp [append, erase, ih]

/-- The receipt charges every selected operation and every conversion.
State-dependent accounts can be obtained by indexing source objects by their
boundary state; this function does not assert hardware cost accuracy. -/
def resources
    (regionCost : Engine → {X Y : Obj} → Region X Y → Resources)
    (holeCost : Engine → {X Y : Obj} → Hole X Y → Resources) :
    {originMode destinationMode : Engine} → {X Y : Obj} →
      Execution family originMode X destinationMode Y → Resources
  | _, _, _, _, .done _ _ => .zero
  | mode, _, _, _, .region arrow rest =>
      (regionCost mode arrow).seq (rest.resources regionCost holeCost)
  | mode, _, _, _, .hole opening rest =>
      (holeCost mode opening).seq (rest.resources regionCost holeCost)
  | _, _, _, _, .switch boundary rest =>
      boundary.resources.seq (rest.resources regionCost holeCost)

def switchCount : {first last : Engine} → {X Y : Obj} →
    Execution family first X last Y → Nat
  | _, _, _, _, .done _ _ => 0
  | _, _, _, _, .region _ rest => rest.switchCount
  | _, _, _, _, .hole _ rest => rest.switchCount
  | _, _, _, _, .switch _ rest => rest.switchCount + 1

/-- A scheduling charge is separate from source-language fuel. Requiring a
positive charge prevents a bounded-work policy from hiding arbitrarily many
representation changes in semantically silent transitions. -/
def PaidSwitches : {first last : Engine} → {X Y : Obj} →
    Execution family first X last Y → Prop
  | _, _, _, _, .done _ _ => True
  | _, _, _, _, .region _ rest => rest.PaidSwitches
  | _, _, _, _, .hole _ rest => rest.PaidSwitches
  | _, _, _, _, .switch boundary rest =>
      0 < boundary.resources.time ∧ rest.PaidSwitches

theorem switchCount_le_work
    (regionCost : Engine → {X Y : Obj} → Region X Y → Resources)
    (holeCost : Engine → {X Y : Obj} → Hole X Y → Resources)
    {first last : Engine} {X Y : Obj}
    (execution : Execution family first X last Y)
    (paid : execution.PaidSwitches) :
    execution.switchCount ≤ (execution.resources regionCost holeCost).time := by
  induction execution with
  | done => simp [switchCount, resources, Resources.zero]
  | region arrow rest ih | hole arrow rest ih =>
      have smaller := ih paid
      simp only [switchCount, resources, Resources.seq]
      omega
  | switch boundary rest ih =>
      have smaller := ih paid.2
      have positive := paid.1
      simp only [switchCount, resources, Resources.seq]
      omega

theorem resources_append
    (regionCost : Engine → {X Y : Obj} → Region X Y → Resources)
    (holeCost : Engine → {X Y : Obj} → Hole X Y → Resources)
    {first middle last : Engine} {X Y Z : Obj}
    (earlier : Execution family first X middle Y)
    (later : Execution family middle Y last Z) :
    (earlier.append later).resources regionCost holeCost =
      (earlier.resources regionCost holeCost).seq
        (later.resources regionCost holeCost) := by
  induction earlier with
  | done => simp [append, resources]
  | region arrow rest ih => simp [append, resources, ih, Resources.seq_assoc]
  | hole opening rest ih => simp [append, resources, ih, Resources.seq_assoc]
  | switch boundary rest ih => simp [append, resources, ih, Resources.seq_assoc]

end Execution

/-- Runtime refusal leaves the source object available. A successful guard
must preserve the same residual observation as a certified total boundary. -/
structure GuardedTransfer {Source Target Observation : Type*}
    (sourceView : Source → Observation) (targetView : Target → Observation) where
  attempt : Source → Option Target
  correct : ∀ state converted, attempt state = some converted →
    targetView converted = sourceView state

namespace GuardedTransfer

variable {Source Target Observation : Type*}
  {sourceView : Source → Observation} {targetView : Target → Observation}

def choose (transfer : GuardedTransfer sourceView targetView) (state : Source) :
    Sum Source Target :=
  match transfer.attempt state with
  | none => .inl state
  | some converted => .inr converted

theorem choose_preserves (transfer : GuardedTransfer sourceView targetView)
    (state : Source) :
    Sum.elim sourceView targetView (transfer.choose state) = sourceView state := by
  cases attempted : transfer.attempt state with
  | none => simp [choose, attempted]
  | some converted =>
      simpa [choose, attempted] using transfer.correct state converted attempted

end GuardedTransfer

/-- Conversion followed by execution is profitable exactly when execution
savings repay conversion. Semantic erasure alone says nothing about this. -/
theorem profitable_iff (conversion referenceWork targetWork saving : Nat)
    (saved : referenceWork = targetWork + saving) :
    conversion + targetWork < referenceWork ↔ conversion < saving := by omega

/-- Returning to a previous representation can have positive cost even if
the complete semantic round trip is the identity. -/
theorem roundTrip_not_free (outward inward : Resources)
    (positive : 0 < outward.time + inward.time) :
    (outward.seq inward).time ≠ Resources.zero.time := by
  simp only [Resources.seq, Resources.zero]
  omega

#print axioms Execution.denote_decode
#print axioms Execution.resources_append
#print axioms Execution.switchCount_le_work
#print axioms GuardedTransfer.choose_preserves

end Mettapedia.GSLT.Dynamics.RepresentationSwitching
