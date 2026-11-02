import Mettapedia.Machines.LiveRegionAdmission

/-!
# Live admission under interleaved environment changes

Execution pages and environment actions remain separate events. Each
environment action supplies its actual update, reference update and a local
decoding square. Arbitrary histories, and schedulers depending on decoded
live outcomes, preserve the full reference receipt: logical operation count,
current provider state, client continuation and completion status.

This is an interleaving model, not a C memory model or an atomicity proof.
The theorem does not enlarge atomic regions or erase permitted yield points.
Physical work, validation and transfer costs are not logical operation counts.
No fairness or eventual completion follows from an arbitrary scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.InterleavedRegions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}
variable {actual reference : Provider P}

abbrev Change (M : Provider P) :=
  {base : Base} → {index : Index base} → M.State base index → M.State base index

/-- The boundary acts on the current state, including states reached after
earlier publication. It cannot substitute an original invocation state. -/
structure Boundary (decode : Hom actual reference) where
  changeActual : Change actual
  changeReference : Change reference
  commutes : ∀ {base index} (state : actual.State base index),
    decode.map (changeActual state) = changeReference (decode.map state)

def operations (M : Provider P) : Charge M := fun _ _ => 1

variable {Return : (base : Base) → Index base → Type u}
variable (client : Client (P := P) (Return := Return)) (decode : Hom actual reference)

abbrev Receipt (M : Provider P) (base : Base) := Nat × Outcome M client base

def mapReceipt {base : Base} (receipt : Receipt client actual base) : Receipt client reference base :=
  (receipt.1, decode.outcome client receipt.2)

theorem boundary_exact (boundary : Boundary decode) {base : Base}
    (outcome : Outcome actual client base) :
    decode.outcome client (Outcome.mapState client boundary.changeActual outcome) =
      Outcome.mapState client boundary.changeReference (decode.outcome client outcome) := by
  cases outcome with
  | paused packet =>
      rcases packet with ⟨index, control, state⟩
      simp [Hom.outcome, Outcome.mapState, boundary.commutes]
  | done result =>
      rcases result with ⟨index, answer, state⟩
      simp [Hom.outcome, Outcome.mapState, boundary.commutes]

inductive Event (decode : Hom actual reference) where
  | page (allowance : Nat)
  | environment (boundary : Boundary decode)

def actualEvent {decode : Hom actual reference} (event : Event decode) {base : Base} :
    Receipt client actual base → Receipt client actual base
  | receipt => match event with
    | .page allowance => resume actual client (operations actual) allowance receipt
    | .environment boundary =>
        (receipt.1, Outcome.mapState client boundary.changeActual receipt.2)

def referenceEvent {decode : Hom actual reference} (event : Event decode) {base : Base} :
    Receipt client reference base → Receipt client reference base
  | receipt => match event with
    | .page allowance => resume reference client (operations reference) allowance receipt
    | .environment boundary =>
        (receipt.1, Outcome.mapState client boundary.changeReference receipt.2)

theorem event_exact (event : Event decode) {base : Base} (receipt : Receipt client actual base) :
    mapReceipt client decode (actualEvent client event receipt) =
      referenceEvent client event (mapReceipt client decode receipt) := by
  cases event with
  | page allowance =>
      simpa only [mapReceipt, actualEvent, referenceEvent] using
        decode.resume_account client (operations actual) (operations reference)
          (fun _ _ => rfl) allowance receipt
  | environment boundary =>
      exact Prod.ext rfl (boundary_exact client decode boundary receipt.2)

def actualHistory {decode : Hom actual reference} (history : List (Event decode)) {base : Base}
    (receipt : Receipt client actual base) : Receipt client actual base :=
  history.foldl (fun current event => actualEvent client event current) receipt

def referenceHistory {decode : Hom actual reference} (history : List (Event decode)) {base : Base}
    (receipt : Receipt client reference base) : Receipt client reference base :=
  history.foldl (fun current event => referenceEvent client event current) receipt

/-- Full residual correspondence holds at every prefix, not just at the end. -/
theorem history_exact (history : List (Event decode)) {base : Base}
    (receipt : Receipt client actual base) :
    mapReceipt client decode (actualHistory client history receipt) =
      referenceHistory client history (mapReceipt client decode receipt) := by
  induction history generalizing receipt with
  | nil => rfl
  | cons event rest ih =>
      change mapReceipt client decode (actualHistory client rest (actualEvent client event receipt)) = _
      rw [ih, event_exact]
      rfl

theorem actualHistory_append (first later : List (Event decode)) {base : Base}
    (receipt : Receipt client actual base) :
    actualHistory client (first ++ later) receipt =
      actualHistory client later (actualHistory client first receipt) := by
  simp [actualHistory, List.foldl_append]

theorem adjacent_pages_compose (first later : Nat) {base : Base}
    (receipt : Receipt client actual base) :
    actualHistory client [Event.page (decode := decode) first, .page later] receipt =
      actualEvent client (Event.page (decode := decode) (first + later)) receipt := by
  exact (resume_add actual client (operations actual) first later receipt).symm

/-- Scheduling decisions may depend on the actual reached reference outcome,
including a reply-selected continuation. No source spelling enters this type. -/
abbrev Scheduler (Control : Type u) (base : Base) :=
  Control → Receipt client reference base → Option (Event decode × Control)

def driveActual {Control : Type u} {base : Base} (schedule : Scheduler client decode Control base) :
    Nat → Control → Receipt client actual base → Control × Receipt client actual base
  | 0, control, receipt => (control, receipt)
  | fuel + 1, control, receipt =>
      match schedule control (mapReceipt client decode receipt) with
      | none => (control, receipt)
      | some (event, next) => driveActual schedule fuel next (actualEvent client event receipt)

def driveReference {Control : Type u} {base : Base} (schedule : Scheduler client decode Control base) :
    Nat → Control → Receipt client reference base → Control × Receipt client reference base
  | 0, control, receipt => (control, receipt)
  | fuel + 1, control, receipt =>
      match schedule control receipt with
      | none => (control, receipt)
      | some (event, next) => driveReference schedule fuel next (referenceEvent client event receipt)

theorem adaptive_schedule_exact {Control : Type u} {base : Base}
    (schedule : Scheduler client decode Control base) (fuel : Nat) (control : Control)
    (receipt : Receipt client actual base) :
    let result := driveActual client decode schedule fuel control receipt
    (result.1, mapReceipt client decode result.2) =
      driveReference client decode schedule fuel control (mapReceipt client decode receipt) := by
  induction fuel generalizing control receipt with
  | zero => rfl
  | succ fuel ih =>
      cases chosen : schedule control (mapReceipt client decode receipt) with
      | none => simp [driveActual, driveReference, chosen]
      | some pair =>
          rcases pair with ⟨event, next⟩
          simp only [driveActual, driveReference, chosen]
          rw [← event_exact client decode event receipt]
          exact ih next (actualEvent client event receipt)

/-- A live partial worker can be re-admitted after any current-state update.
This keeps the update separate from the following protocol operation. -/
def workerBoundary (worker : LiveAdmission.PartialWorker reference) (change : Change reference) :
    Boundary worker.hom where
  changeActual := change
  changeReference := change
  commutes _ := rfl

end Mettapedia.Machines.Cursor.InterleavedRegions
