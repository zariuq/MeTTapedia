import Mettapedia.TypeTheory.IndexedPolynomialCoalgebra
import Mettapedia.GSLT.Logic.AbstractSeparationLogic
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

/-! The existing primitive program tree also supplies a cursor client.
The comparison below retains stateful actions and independent charges; the
provider's physical realization and its termination remain separate duties. -/

namespace Mettapedia.Machines.Cursor.PrimitiveProgram

open Mettapedia.TypeTheory
open CategoryTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

universe u

variable {Op : Type u} {Ret : Op → Type u} {Answer Fault World : Type u}

/-- Faults are replies, not fabricated inhabitants of a primitive's result type. -/
abbrev protocol (Op : Type u) (Ret : Op → Type u) (Fault : Type u) :
    IndexedPolynomial PUnit.{u+1} (fun _ => PUnit.{u+1}) where
  Shape _ _ := Op
  Position operation := Except Fault (Ret operation)
  next _ _ := PUnit.unit

/-- The existing primitive tree exposes one actual layer. The concrete
codomain keeps response-dependent children explicit through the categorical
carrier. No alternate program syntax is introduced. -/
def expose (control : Except Fault (Prog Op Ret Answer)) :
    ((protocol Op Ret Fault).withHoles (fun _ _ => Except Fault Answer)).Extension
      (fun _ _ => Except Fault (Prog Op Ret Answer)) PUnit.unit PUnit.unit :=
  match control with
  | .error fault => ⟨.inl (.error fault), PEmpty.elim⟩
  | .ok (.ret answer) => ⟨.inl (.ok answer), PEmpty.elim⟩
  | .ok (.call operation next) => ⟨.inr operation, fun reply => match reply with
      | .error fault => .error fault
      | .ok value => .ok (next value)⟩

/-- The existing program supplies its actual dependent continuation to the
existing indexed polynomial coalgebra. A fault is a retained terminal value. -/
abbrev client (Op : Type u) (Ret : Op → Type u) (Answer Fault : Type u) :
    Client (P := protocol Op Ret Fault) (Return := fun _ _ => Except Fault Answer) where
  V _ _ := Except Fault (Prog Op Ret Answer)
  str := fun _ _ => ↾(expose (Op := Op) (Ret := Ret) (Answer := Answer) (Fault := Fault))

abbrev provider (step : World → (operation : Op) → World × Except Fault (Ret operation)) :
    Provider (protocol Op Ret Fault) where
  State _ _ := World
  step world operation := let response := step world operation; ⟨response.2, response.1⟩

abbrev charge (cost : World → Op → Nat)
    (step : World → (operation : Op) → World × Except Fault (Ret operation)) :
    Charge (provider step) := fun world operation => cost world operation

/-- Read the actual existing cursor outcome, preserving final or residual
control, fault status and the complete provider world. -/
def readOutcome (step : World → (operation : Op) → World × Except Fault (Ret operation)) :
    Outcome (provider step) (client Op Ret Answer Fault) PUnit.unit →
      (Except Fault Answer ⊕ Except Fault (Prog Op Ret Answer)) × World
  | .paused ⟨_, control, world⟩ => (.inr control, world)
  | .done ⟨_, answer, world⟩ => (.inl answer, world)

/-- Independent direct bounded execution of the original program syntax.
No indexed cursor operation is used to define its expected result. -/
def direct (step : World → (operation : Op) → World × Except Fault (Ret operation))
    (cost : World → Op → Nat) : Nat → Except Fault (Prog Op Ret Answer) → World →
      Nat × ((Except Fault Answer ⊕ Except Fault (Prog Op Ret Answer)) × World)
  | 0, control, world => (0, (.inr control, world))
  | _ + 1, .error fault, world => (0, (.inl (.error fault), world))
  | _ + 1, .ok (.ret answer), world => (0, (.inl (.ok answer), world))
  | fuel + 1, .ok (.call operation next), world =>
      let response := step world operation
      let rest := direct step cost fuel
        (match response.2 with
        | .error fault => .error fault
        | .ok value => .ok (next value)) response.1
      (cost world operation + rest.1, rest.2)

/-- Both algorithms inspect the same dependent replies and preserve the full
world and residual, including faults and cumulative charges. -/
theorem advance_is_direct
    (step : World → (operation : Op) → World × Except Fault (Ret operation))
    (cost : World → Op → Nat) (fuel : Nat)
    (control : Except Fault (Prog Op Ret Answer)) (world : World) :
    let result := advance (provider step) (client Op Ret Answer Fault) (charge cost step)
      fuel ⟨PUnit.unit, control, world⟩
    (result.1, readOutcome step result.2) = direct step cost fuel control world := by
  induction fuel generalizing control world with
  | zero => rfl
  | succ fuel ih =>
      cases control with
      | error fault => rfl
      | ok program =>
          cases program with
          | ret answer => rfl
          | call operation next =>
              have head : (client Op Ret Answer Fault).str PUnit.unit PUnit.unit
                  (.ok (.call operation next)) =
                  ⟨.inr operation, fun reply => match reply with
                    | .error fault => .error fault
                    | .ok value => .ok (next value)⟩ := by
                rfl
              simp only [advance, head]
              rcases responseLaw : step world operation with ⟨following, reply⟩
              cases reply with
              | error fault =>
                  simpa only [provider, charge, protocol, withHoles, direct, responseLaw] using
                    congrArg
                      (fun value : Nat × ((Except Fault Answer ⊕ Except Fault (Prog Op Ret Answer)) × World) =>
                        (cost world operation + value.1, value.2))
                      (ih (.error fault) following)
              | ok value =>
                  simpa only [provider, charge, protocol, withHoles, direct, responseLaw] using
                    congrArg
                      (fun value : Nat × ((Except Fault Answer ⊕ Except Fault (Prog Op Ret Answer)) × World) =>
                        (cost world operation + value.1, value.2))
                      (ih (.ok (next value)) following)


/-- Reconstruct the same existing outcome; the singleton capability index
carries no hidden quotient. -/
def restoreOutcome (step : World → (operation : Op) → World × Except Fault (Ret operation)) :
    (Except Fault Answer ⊕ Except Fault (Prog Op Ret Answer)) × World →
      Outcome (provider step) (client Op Ret Answer Fault) PUnit.unit
  | (.inl answer, world) => .done ⟨PUnit.unit, answer, world⟩
  | (.inr control, world) => .paused ⟨PUnit.unit, control, world⟩

@[simp] theorem restoreOutcome_readOutcome
    (step : World → (operation : Op) → World × Except Fault (Ret operation))
    (value : Outcome (provider step) (client Op Ret Answer Fault) PUnit.unit) :
    restoreOutcome step (readOutcome step value) = value := by
  cases value with
  | paused packet => rcases packet with ⟨index, control, world⟩; cases index; rfl
  | done result => rcases result with ⟨index, answer, world⟩; cases index; rfl

@[simp] theorem readOutcome_restoreOutcome
    (step : World → (operation : Op) → World × Except Fault (Ret operation))
    (value : (Except Fault Answer ⊕ Except Fault (Prog Op Ret Answer)) × World) :
    readOutcome step (restoreOutcome step value) = value := by
  rcases value with ⟨outcome, world⟩
  cases outcome <;> rfl

theorem readOutcome_injective
    (step : World → (operation : Op) → World × Except Fault (Ret operation)) :
    Function.Injective (readOutcome (Answer := Answer) step) := by
  intro left right equal
  have same := congrArg (restoreOutcome step) equal
  simpa only [restoreOutcome_readOutcome] using same


/-- The implementation obligation is local to one primitive. It specifies a
permitted reply and successor only where the independent action is safe. -/
def ProviderSound
    (act : (operation : Op) → Action World (Ret operation))
    (step : World → (operation : Op) → World × Except Fault (Ret operation)) : Prop :=
  ∀ world operation, (act operation).Safe world →
    ∃ value following, step world operation = (following, .ok value) ∧
      (act operation).Step world value following

/-- A successful bounded execution is a permitted execution of the original
program. A pause retains a safe continuation; no fault is hidden as success. -/
def SafeOutcome (act : (operation : Op) → Action World (Ret operation))
    (program : Prog Op Ret Answer) (initial : World) :
    (Except Fault Answer ⊕ Except Fault (Prog Op Ret Answer)) × World → Prop
  | (.inl (.ok answer), following) => program.Runs act initial answer following
  | (.inl (.error _), _) => False
  | (.inr (.ok residual), following) => residual.Safe act following
  | (.inr (.error _), _) => False

/-- A local primitive realization law lifts to fault avoidance and stateful
execution for every bounded prefix, with the original reply-dependent child. -/
theorem direct_safe_outcome
    (act : (operation : Op) → Action World (Ret operation))
    (step : World → (operation : Op) → World × Except Fault (Ret operation))
    (localLaw : ProviderSound act step) (cost : World → Op → Nat)
    (fuel : Nat) (program : Prog Op Ret Answer) (world : World)
    (safe : program.Safe act world) :
    SafeOutcome act program world (direct step cost fuel (.ok program) world).2 := by
  induction fuel generalizing program world with
  | zero => exact safe
  | succ fuel ih =>
      cases program with
      | ret answer => exact ⟨rfl, rfl⟩
      | call operation next =>
          obtain ⟨value, following, stepLaw, permitted⟩ := localLaw world operation safe.1
          have kept := ih (next value) following (safe.2 value following permitted)
          simp only [direct, stepLaw] at kept ⊢
          rcases hrest : direct step cost fuel (.ok (next value)) following with ⟨spent, outcome, final⟩
          rw [hrest] at kept
          cases outcome with
          | inl answer =>
              cases answer with
              | error fault => exact kept
              | ok answer => exact ⟨value, following, permitted, kept⟩
          | inr control =>
              cases control with
              | error fault => exact kept
              | ok residual => exact kept

/-- The existing cursor's concrete bounded execution satisfies the same
independent action semantics, rather than merely agreeing on printed values. -/
theorem advance_safe_outcome
    (act : (operation : Op) → Action World (Ret operation))
    (step : World → (operation : Op) → World × Except Fault (Ret operation))
    (localLaw : ProviderSound act step) (cost : World → Op → Nat)
    (fuel : Nat) (program : Prog Op Ret Answer) (world : World)
    (safe : program.Safe act world) :
    SafeOutcome act program world
      (readOutcome step (advance (provider step) (client Op Ret Answer Fault)
        (charge cost step) fuel ⟨PUnit.unit, .ok program, world⟩).2) := by
  have correspondence := congrArg Prod.snd (advance_is_direct step cost fuel (.ok program) world)
  exact Eq.mpr (congrArg (SafeOutcome act program world) correspondence)
    (direct_safe_outcome act step localLaw cost fuel program world safe)

end Mettapedia.Machines.Cursor.PrimitiveProgram
