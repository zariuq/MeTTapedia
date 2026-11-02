import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Live, request-indexed admission of partial workers

A worker is tried at the current protocol state, not at an outer source
spelling. Successful workers preserve the actual reply and successor state;
refusal runs the reference operation. The existing indexed cursor protocol
then supplies arbitrary adaptive clients, capabilities and live residuals.

A prepared planner may cache its selected code and complete executed read
certificate. Tickets are indexed by their request and planner. Validation
allows reuse across unrelated changes; a changed dependency reruns planning.
Neither a stale positive nor a stale negative admission decision is authority.
Planner read certificates are optimization evidence, not source effect traces.
Native allocation, atomicity and cost correspondence remain separate duties.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LiveAdmission

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u, u, u, u} Base Index}

abbrev Response (M : Provider P) {base : Base} {index : Index base}
    (request : P.Shape base index) :=
  Σ reply : P.Position request, M.State base (P.next request reply)

structure PartialWorker (reference : Provider P) where
  attempt : {base : Base} → {index : Index base} →
    reference.State base index → (request : P.Shape base index) → Option (Response reference request)
  correct : ∀ {base index} (state : reference.State base index) (request : P.Shape base index)
    (result : Response reference request), attempt state request = some result →
      result = reference.step state request

namespace PartialWorker

variable {reference : Provider P}

def execute (worker : PartialWorker reference) {base : Base} {index : Index base}
    (state : reference.State base index) (request : P.Shape base index) : Response reference request :=
  (worker.attempt state request).getD (reference.step state request)

theorem execute_exact (worker : PartialWorker reference) {base : Base} {index : Index base}
    (state : reference.State base index) (request : P.Shape base index) :
    worker.execute state request = reference.step state request := by
  cases h : worker.attempt state request with
  | none => simp [execute, h]
  | some result => simpa [execute, h] using worker.correct state request result h

theorem refused_uses_reference (worker : PartialWorker reference) {base : Base} {index : Index base}
    (state : reference.State base index) (request : P.Shape base index)
    (refused : worker.attempt state request = none) :
    worker.execute state request = reference.step state request := by simp [execute, refused]

def provider (worker : PartialWorker reference) : Provider P where
  State := reference.State
  step := worker.execute

def hom (worker : PartialWorker reference) : Hom worker.provider reference where
  map state := state
  step state request := by
    change worker.execute state request = reference.step state request
    exact worker.execute_exact state request

/-- Try another certified worker on refusal, without changing the input. -/
def orElse (first second : PartialWorker reference) : PartialWorker reference where
  attempt state request := (first.attempt state request).orElse (fun _ => second.attempt state request)
  correct state request result accepted := by
    cases h : first.attempt state request with
    | none => exact second.correct state request result (by simpa [h] using accepted)
    | some value =>
        have same : value = result := by simpa [h] using accepted
        exact same ▸ first.correct state request value h

/-- An empty portfolio means reference execution, not an empty source answer. -/
def noWorker : PartialWorker reference where
  attempt _ _ := none
  correct _ _ _ impossible := by cases impossible

def portfolio : List (PartialWorker reference) → PartialWorker reference
  | [] => noWorker
  | first :: rest => first.orElse (portfolio rest)

theorem orElse_admission (first second : PartialWorker reference) {base : Base} {index : Index base}
    (state : reference.State base index) (request : P.Shape base index) :
    ((first.orElse second).attempt state request).isSome =
      ((first.attempt state request).isSome || (second.attempt state request).isSome) := by
  cases selected : first.attempt state request <;> simp [orElse, selected]

theorem portfolio_admission (workers : List (PartialWorker reference)) {base : Base} {index : Index base}
    (state : reference.State base index) (request : P.Shape base index) :
    ((portfolio workers).attempt state request).isSome =
      workers.any (fun worker => (worker.attempt state request).isSome) := by
  induction workers with
  | nil => rfl
  | cons first rest ih => simp [portfolio, orElse_admission, ih]

theorem orElse_assoc (first second third : PartialWorker reference) {base : Base} {index : Index base}
    (state : reference.State base index) (request : P.Shape base index) :
    ((first.orElse second).orElse third).attempt state request =
      (first.orElse (second.orElse third)).attempt state request := by
  cases h : first.attempt state request <;> simp [orElse, h]

theorem portfolio_append (first later : List (PartialWorker reference))
    {base : Base} {index : Index base} (state : reference.State base index)
    (request : P.Shape base index) :
    (portfolio (first ++ later)).attempt state request =
      ((portfolio first).orElse (portfolio later)).attempt state request := by
  induction first with
  | nil => simp [portfolio, orElse, noWorker]
  | cons head rest ih =>
      simp only [List.cons_append, portfolio, orElse_assoc]
      cases h : head.attempt state request <;> simp [orElse, h, ih]

theorem extending_portfolio_keeps_admission (first later : List (PartialWorker reference))
    {base : Base} {index : Index base} (state : reference.State base index)
    (request : P.Shape base index) (accepted : ((portfolio first).attempt state request).isSome = true) :
    ((portfolio (first ++ later)).attempt state request).isSome = true := by
  rw [portfolio_append, orElse_admission, accepted]
  rfl

/-- The client may create later requests from replies; no outer AST test is used. -/
theorem advance_exact (worker : PartialWorker reference)
    {Return : (base : Base) → Index base → Type u}
    (client : Client (P := P) (Return := Return))
    (actualCharge : Charge worker.provider) (referenceCharge : Charge reference)
    (fuel : Nat) {base : Base} (packet : Packet worker.provider client base) :
    worker.hom.outcome client (advance worker.provider client actualCharge fuel packet).2 =
      (advance reference client referenceCharge fuel (worker.hom.packet client packet)).2 :=
  worker.hom.advance client actualCharge referenceCharge fuel packet

end PartialWorker

variable {Key Value Code : Type u}

/-- Planning is a pure adaptive read program. Code execution is separately
proved against one current reference transition. -/
structure Planner (reference : Provider P) (Key Value Code : Type u) where
  view : {base : Base} → {index : Index base} → reference.State base index → Key → Value
  query : {base : Base} → {index : Index base} → P.Shape base index →
    ReadOnlyQuery.Program Key Value (Option Code)
  execute : {base : Base} → {index : Index base} → reference.State base index →
    (request : P.Shape base index) → Code → Response reference request
  correct : ∀ {base index} (state : reference.State base index) (request : P.Shape base index)
    (code : Code), (ReadOnlyQuery.run (view state) (query request)).answer = some code →
      execute state request code = reference.step state request

namespace Planner

variable {reference : Provider P} (planner : Planner reference Key Value Code)

/-- The origin is proof-only: runtime data are selected code and observed reads. -/
structure Ticket {base : Base} {index : Index base} (request : P.Shape base index) where
  observed : ReadOnlyQuery.Observation Key Value (Option Code)
  justified : ∃ prior : reference.State base index,
    ReadOnlyQuery.run (planner.view prior) (planner.query request) = observed

def prepare {base : Base} {index : Index base} (state : reference.State base index)
    (request : P.Shape base index) : planner.Ticket request :=
  ⟨ReadOnlyQuery.run (planner.view state) (planner.query request), state, rfl⟩

def replay [DecidableEq Value] {base : Base} {index : Index base}
    (state : reference.State base index) (request : P.Shape base index)
    (ticket : planner.Ticket request) : Option Code :=
  if ReadOnlyQuery.checkReads (planner.view state) ticket.observed.reads then ticket.observed.answer
  else (ReadOnlyQuery.run (planner.view state) (planner.query request)).answer

theorem replay_exact [DecidableEq Value] {base : Base} {index : Index base}
    (state : reference.State base index) (request : P.Shape base index)
    (ticket : planner.Ticket request) :
    planner.replay state request ticket =
      (ReadOnlyQuery.run (planner.view state) (planner.query request)).answer := by
  unfold replay
  split
  · rename_i valid
    obtain ⟨prior, origin⟩ := ticket.justified
    have agrees : ReadOnlyQuery.checkReads (planner.view state)
        (ReadOnlyQuery.run (planner.view prior) (planner.query request)).reads = true := by
      simpa only [origin] using valid
    have equal := ReadOnlyQuery.validated_answer (planner.view prior) (planner.view state)
      (planner.query request) agrees
    simpa only [origin] using equal.symm
  · rfl

def worker : PartialWorker reference where
  attempt state request :=
    (ReadOnlyQuery.run (planner.view state) (planner.query request)).answer.map
      (planner.execute state request)
  correct state request result accepted := by
    obtain ⟨code, planned, equal⟩ := Option.map_eq_some_iff.mp accepted
    exact equal ▸ planner.correct state request code planned

/-- A cache is indexed by this exact planner and request. A source/profile
change needs a new planner or an independently justified transport. -/
def cachedWorker [DecidableEq Value]
    (lookup : {base : Base} → {index : Index base} →
      (request : P.Shape base index) → Option (planner.Ticket request)) : PartialWorker reference where
  attempt state request :=
    let selected := match lookup request with
      | none => (ReadOnlyQuery.run (planner.view state) (planner.query request)).answer
      | some ticket => planner.replay state request ticket
    selected.map (planner.execute state request)
  correct state request result accepted := by
    cases found : lookup request with
    | none => exact planner.worker.correct state request result (by simpa [worker, found] using accepted)
    | some ticket =>
        have actual : (ReadOnlyQuery.run (planner.view state) (planner.query request)).answer.map
            (planner.execute state request) = some result := by
          simpa [found, planner.replay_exact] using accepted
        exact planner.worker.correct state request result actual

theorem cached_attempt_eq_live [DecidableEq Value]
    (lookup : {base : Base} → {index : Index base} →
      (request : P.Shape base index) → Option (planner.Ticket request))
    {base : Base} {index : Index base} (state : reference.State base index)
    (request : P.Shape base index) :
    (planner.cachedWorker lookup).attempt state request = planner.worker.attempt state request := by
  cases found : lookup request <;> simp [cachedWorker, worker, found, planner.replay_exact]

end Planner

end Mettapedia.Machines.Cursor.LiveAdmission
