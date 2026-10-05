import Mettapedia.TypeTheory.IndexedPolynomialCoalgebra
import Mathlib.Tactic

/-!
# Indexed cursor protocols and live residual execution

An existing indexed polynomial is read as a protocol: a shape is a request,
a position is its reply, and `next` is the capability index after that reply.
The client is the existing polynomial coalgebra, so recursive clients need
not terminate. A provider supplies one total protocol transition; waiting,
failure, exhaustion and errors must be explicit replies when applicable.

The scheduler budget counts inspections, not CPU time or a dialect's fuel.
Charges are independent natural-valued receipts supplied by a realization.
The exact chunking law preserves the actual residual and accumulated charges;
it never restarts a client from its original state. Nothing here selects a
search order or makes one physical cursor representation mandatory.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable (P : IndexedPolynomial.{u, u, u, u} Base Index)

/-- A realization of the protocol, with representation-specific indexed state. -/
structure Provider where
  State : (base : Base) → Index base → Type u
  step : {base : Base} → {index : Index base} → State base index →
    (request : P.Shape base index) →
      Σ reply : P.Position request, State base (P.next request reply)

variable {P}

/-- A receipt for an operation; its physical interpretation is a separate
runtime obligation. It may measure allocations, bytes, work, or source fuel. -/
abbrev Charge (M : Provider P) :=
  {base : Base} → {index : Index base} → M.State base index →
    P.Shape base index → Nat

variable {Return : (base : Base) → Index base → Type u}

/-- Reuse the polynomial coalgebra instead of introducing another client AST. -/
abbrev Client := CoalgebraicPlans.Realizer (P := P) (H := Return)

variable (M : Provider P) (C : Client (P := P) (Return := Return))

/-- Live client control and provider state, at their common capability index. -/
abbrev Packet (base : Base) :=
  Σ index : Index base, C.V base index × M.State base index

abbrev Finished (base : Base) :=
  Σ index : Index base, Return base index × M.State base index

/-- Scheduler suspension is distinct from successful completion. Other
outcomes are carried by the declared reply and return types, never erased. -/
inductive Outcome (base : Base) where
  | paused (packet : Packet M C base)
  | done (result : Finished M (Return := Return) base)

/-- Transport only provider state, preserving the client continuation and
completion status. This operation alone asserts no relation between the
providers' transitions; `Hom` supplies that stronger obligation. -/
def Outcome.mapState {source target : Provider P}
    (map : {base : Base} → {index : Index base} →
      source.State base index → target.State base index) {base : Base} :
    Outcome source C base → Outcome target C base
  | .paused ⟨index, control, state⟩ => .paused ⟨index, control, map state⟩
  | .done ⟨index, value, state⟩ => .done ⟨index, value, map state⟩

@[simp] theorem Outcome.mapState_id {base : Base} (value : Outcome M C base) :
    Outcome.mapState C (source := M) (target := M) (fun state => state) value = value := by
  cases value with
  | paused packet => rcases packet with ⟨index, control, state⟩; rfl
  | done result => rcases result with ⟨index, value, state⟩; rfl

theorem Outcome.mapState_comp {source middle target : Provider P}
    (first : {base : Base} → {index : Index base} →
      source.State base index → middle.State base index)
    (second : {base : Base} → {index : Index base} →
      middle.State base index → target.State base index)
    {base : Base} (value : Outcome source C base) :
    Outcome.mapState C second (Outcome.mapState C first value) =
      Outcome.mapState C (fun state => second (first state)) value := by
  cases value with
  | paused packet => rcases packet with ⟨index, control, state⟩; rfl
  | done result => rcases result with ⟨index, value, state⟩; rfl

variable (charge : Charge M)

/-- Execute a bounded prefix. A returned value does not execute a provider
operation. A request executes once and resumes its own reply-indexed child. -/
def advance : Nat → {base : Base} → Packet M C base → Nat × Outcome M C base
  | 0, _, packet => (0, .paused packet)
  | fuel + 1, base, ⟨index, control, state⟩ =>
      match C.str base index control with
      | ⟨.inl value, _⟩ => (0, .done ⟨index, value, state⟩)
      | ⟨.inr request, children⟩ =>
          let response := M.step state request
          let rest := advance fuel ⟨_, children response.1, response.2⟩
          (charge state request + rest.1, rest.2)

/-- Resume precisely the retained packet. Completed results are inert. -/
def resume (fuel : Nat) {base : Base}
    (previous : Nat × Outcome M C base) : Nat × Outcome M C base :=
  match previous.2 with
  | .done result => (previous.1, .done result)
  | .paused packet =>
      let rest := advance M C charge fuel packet
      (previous.1 + rest.1, rest.2)

@[simp] theorem advance_zero {base : Base} (packet : Packet M C base) :
    advance M C charge 0 packet = (0, .paused packet) := rfl

@[simp] theorem resume_done (fuel spent : Nat) {base : Base}
    (result : Finished M (Return := Return) base) :
    resume M C charge fuel (spent, .done result) = (spent, .done result) := rfl

@[simp] theorem resume_zero {base : Base} (previous : Nat × Outcome M C base) :
    resume M C charge 0 previous = previous := by
  rcases previous with ⟨spent, outcome⟩
  cases outcome <;> simp [resume, advance]

theorem resume_add_charge (fuel extra : Nat) {base : Base}
    (previous : Nat × Outcome M C base) :
    resume M C charge fuel (extra + previous.1, previous.2) =
      (extra + (resume M C charge fuel previous).1,
        (resume M C charge fuel previous).2) := by
  rcases previous with ⟨spent, outcome⟩
  cases outcome <;> simp [resume, Nat.add_assoc]

/-- Any split of a scheduler budget executes the same requests, retains the
same residual, and accumulates the same charges. -/
theorem advance_add (earlier later : Nat) {base : Base}
    (packet : Packet M C base) :
    advance M C charge (earlier + later) packet =
      resume M C charge later (advance M C charge earlier packet) := by
  induction earlier generalizing packet with
  | zero => simp [advance, resume]
  | succ earlier ih =>
      rcases packet with ⟨index, control, state⟩
      rw [Nat.succ_add]
      cases h : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp [advance, h, resume]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [advance, h]
              dsimp only [withHoles]
              rw [ih]
              exact (resume_add_charge M C charge later (charge state request) _).symm

/-- Repeated suspension/resumption is associative, including completed runs. -/
theorem resume_add (earlier later : Nat) {base : Base}
    (previous : Nat × Outcome M C base) :
    resume M C charge (earlier + later) previous =
      resume M C charge later (resume M C charge earlier previous) := by
  rcases previous with ⟨spent, outcome⟩
  cases outcome with
  | done result => rfl
  | paused packet =>
      change (spent + (advance M C charge (earlier + later) packet).1,
        (advance M C charge (earlier + later) packet).2) = _
      rw [advance_add]
      exact (resume_add_charge M C charge later spent _).symm

/-- A representation map must preserve the actual response and successor
state for every request. This is a local implementation obligation, not an
assumed whole-program equivalence. Charges need not be equal. -/
structure Hom (source target : Provider P) where
  map : {base : Base} → {index : Index base} →
    source.State base index → target.State base index
  step : ∀ {base index} (state : source.State base index)
    (request : P.Shape base index),
    (⟨(source.step state request).1,
      map (source.step state request).2⟩ :
        Σ reply, target.State base (P.next request reply)) =
      target.step (map state) request

namespace Hom

variable {source target third : Provider P}

def id (M : Provider P) : Hom M M where
  map state := state
  step state request := by cases M.step state request; rfl

def comp (first : Hom source target) (second : Hom target third) :
    Hom source third where
  map state := second.map (first.map state)
  step state request := by
    have a := first.step state request
    have b := second.step (first.map state) request
    rw [← a] at b
    exact b

def packet (h : Hom source target) {base : Base}
    (value : Packet source C base) : Packet target C base :=
  ⟨value.1, value.2.1, h.map value.2.2⟩

def finished (h : Hom source target) {base : Base}
    (value : Finished source (Return := Return) base) :
    Finished target (Return := Return) base :=
  ⟨value.1, value.2.1, h.map value.2.2⟩

def outcome (h : Hom source target) {base : Base} :
    Outcome source C base → Outcome target C base :=
  Outcome.mapState C h.map

/-- Every adaptive, potentially recursive client preserves its full bounded
observation, including residual control and finished state, under a lawful
representation map. This is equality, so it excludes invented responses. -/
theorem advance (h : Hom source target)
    (sourceCharge : Charge source) (targetCharge : Charge target)
    (fuel : Nat) {base : Base} (value : Packet source C base) :
    h.outcome C (Cursor.advance source C sourceCharge fuel value).2 =
      (Cursor.advance target C targetCharge fuel (h.packet C value)).2 := by
  induction fuel generalizing value with
  | zero => rfl
  | succ fuel ih =>
      rcases value with ⟨index, control, state⟩
      change h.outcome C
        (Cursor.advance source C sourceCharge (fuel + 1)
          ⟨index, control, state⟩).2 =
        (Cursor.advance target C targetCharge (fuel + 1)
          ⟨index, control, h.map state⟩).2
      cases eq : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl result => simp only [Cursor.advance, eq, outcome, Outcome.mapState]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [Cursor.advance, eq]
              dsimp only [withHoles]
              rw [← h.step state request]
              exact ih ⟨_, children (source.step state request).1,
                (source.step state request).2⟩

/-- A local equality of receipts transports through any adaptive client. -/
theorem advance_charge
    {Base : Type u} {Index : Base → Type u}
    {P : IndexedPolynomial.{u, u, u, u} Base Index}
    {Return : (base : Base) → Index base → Type u}
    {source target : Provider P}
    (C : Client (P := P) (Return := Return)) (h : Hom source target)
    (sourceCost : Charge source) (targetCost : Charge target)
    (localCharge : ∀ {base index} (state : source.State base index)
      (request : P.Shape base index), sourceCost state request = targetCost (h.map state) request)
    (fuel : Nat) {base : Base} (packet : Packet source C base) :
    (Cursor.advance source C sourceCost fuel packet).1 =
      (Cursor.advance target C targetCost fuel (h.packet C packet)).1 := by
  induction fuel generalizing packet with
  | zero => rfl
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      change (Cursor.advance source C sourceCost (fuel + 1) ⟨index, control, state⟩).1 =
        (Cursor.advance target C targetCost (fuel + 1) ⟨index, control, h.map state⟩).1
      cases eq : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp [Cursor.advance, eq]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [Cursor.advance, eq]
              dsimp only [withHoles]
              rw [← h.step state request, localCharge]
              exact congrArg (fun n => targetCost (h.map state) request + n)
                (ih ⟨_, children (source.step state request).1, (source.step state request).2⟩)

/-- Local transition and charge correspondence preserves the full bounded
account, including unfinished client control and provider state. -/
theorem advance_account (h : Hom source target)
    (sourceCost : Charge source) (targetCost : Charge target)
    (localCharge : ∀ {base index} (state : source.State base index)
      (request : P.Shape base index), sourceCost state request = targetCost (h.map state) request)
    (fuel : Nat) {base : Base} (value : Packet source C base) :
    ((Cursor.advance source C sourceCost fuel value).1,
        h.outcome C (Cursor.advance source C sourceCost fuel value).2) =
      Cursor.advance target C targetCost fuel (h.packet C value) := by
  apply Prod.ext
  · exact h.advance_charge C sourceCost targetCost localCharge fuel value
  · exact h.advance C sourceCost targetCost fuel value

/-- Moving a saved account transports its already paid charge without
replaying the prefix. Every future bounded resume retains the same complete
outcome and pays exactly the corresponding future provider operations. -/
theorem resume_account (h : Hom source target)
    (sourceCost : Charge source) (targetCost : Charge target)
    (localCharge : ∀ {base index} (state : source.State base index)
      (request : P.Shape base index), sourceCost state request = targetCost (h.map state) request)
    (fuel : Nat) {base : Base} (previous : Nat × Outcome source C base) :
    ((Cursor.resume source C sourceCost fuel previous).1,
        h.outcome C (Cursor.resume source C sourceCost fuel previous).2) =
      Cursor.resume target C targetCost fuel (previous.1, h.outcome C previous.2) := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done result => rfl
  | paused packet =>
      change (paid + (Cursor.advance source C sourceCost fuel packet).1,
          h.outcome C (Cursor.advance source C sourceCost fuel packet).2) =
        (paid + (Cursor.advance target C targetCost fuel (h.packet C packet)).1,
          (Cursor.advance target C targetCost fuel (h.packet C packet)).2)
      apply Prod.ext
      · exact congrArg (paid + ·) (h.advance_charge C sourceCost targetCost localCharge fuel packet)
      · exact h.advance C sourceCost targetCost fuel packet

end Hom

end Mettapedia.Machines.Cursor
