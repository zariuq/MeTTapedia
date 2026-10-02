import Mettapedia.GSLT.LanguageDef.HostCallMachine
import Mettapedia.Machines.Cursor.Protocol

/-!
# Fault-aware query replies in the indexed cursor language

The existing indexed polynomial cursor protocol can carry all query outcomes:
normal exhaustion, an ordered answer with its live residual, suspension with
its live residual, and a fault. The performed world is retained on every reply.
Logical refinements and occurrence identities remain in the answer type.

This adapter exposes an existing pull service; it does not interpret typing
rules or add another query engine. A client is the existing polynomial
coalgebra, which chooses what to do with each reply. `Hom.advance` transports
all bounded interactions from a local representation law, while `chunk_exact`
retains the actual packet under budget splitting. The protocol does not infer
termination, enforce pointer ownership, or choose search order.

Authored coGSLT declarations can specify mode/admission evidence over this
operational interface. Such declarations are additional information, not a
replacement for the reply semantics or an automatic compilation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlOutcomeCursor

open Mettapedia.TypeTheory
open Mettapedia.Machines.Cursor
open HostCalls (Pull)

variable {Source Target Answer World Fault : Type}

def mapPull (map : Source → Target) : Pull Source Answer → Pull Target Answer
  | .done => .done
  | .yield answer rest => .yield answer (map rest)
  | .suspend rest => .suspend (map rest)

def mapOutcome (map : Source → Target) :
    Except Fault (Pull Source Answer) → Except Fault (Pull Target Answer) :=
  Except.map (mapPull map)

def protocol (Answer Fault : Type) : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Except Fault (Pull Unit Answer)
  next _ _ := ()

def provider (pull : Source → World → World × Except Fault (Pull Source Answer)) :
    Provider (protocol Answer Fault) where
  State _ _ := Source × World
  step state _ :=
    let pulled := pull state.1 state.2
    match pulled.2 with
    | .error error => ⟨.error error, (state.1, pulled.1)⟩
    | .ok .done => ⟨.ok .done, (state.1, pulled.1)⟩
    | .ok (.yield answer rest) => ⟨.ok (.yield answer ()), (rest, pulled.1)⟩
    | .ok (.suspend rest) => ⟨.ok (.suspend ()), (rest, pulled.1)⟩

def poll (pull : Source → World → World × Except Fault (Pull Source Answer))
    (state : Source × World) : Except Fault (Pull Unit Answer) × (Source × World) :=
  let response := (provider pull).step (base := ()) (index := ()) state ()
  (response.1, response.2)

theorem returned_world (pull : Source → World → World × Except Fault (Pull Source Answer))
    (cursor : Source) (world : World) :
    (poll pull (cursor, world)).2.2 = (pull cursor world).1 := by
  cases pulled : pull cursor world with
  | mk world' result =>
      cases result with
      | error error => simp [poll, provider, pulled]
      | ok reply => cases reply <;> simp [poll, provider, pulled]

theorem retains_suspension
    (pull : Source → World → World × Except Fault (Pull Source Answer))
    {cursor rest : Source} {world world' : World}
    (waiting : pull cursor world = (world', .ok (.suspend rest))) :
    poll pull (cursor, world) =
      (.ok (.suspend ()), (rest, world')) := by simp [poll, provider, waiting]

theorem retains_fault
    (pull : Source → World → World × Except Fault (Pull Source Answer))
    {cursor : Source} {world world' : World} {error : Fault}
    (faulted : pull cursor world = (world', .error error)) :
    poll pull (cursor, world) =
      (.error error, (cursor, world')) := by simp [poll, provider, faulted]

/-- Representation refinement preserves full replies and logical residuals.
The local law is a primitive provider equation, not assumed client equivalence. -/
def hom
    (source : Source → World → World × Except Fault (Pull Source Answer))
    (target : Target → World → World × Except Fault (Pull Target Answer))
    (map : Source → Target)
    (localLaw : ∀ cursor world,
      target (map cursor) world =
        ((source cursor world).1, mapOutcome map (source cursor world).2)) :
    Hom (provider source) (provider target) where
  map state := (map state.1, state.2)
  step state request := by
    rcases state with ⟨cursor, world⟩
    cases pulled : source cursor world with
    | mk world' result =>
        have targetPull := localLaw cursor world
        rw [pulled] at targetPull
        cases result with
        | error error => simp [provider, pulled, targetPull, mapOutcome, Except.map]
        | ok reply =>
            cases reply <;>
              simp [provider, pulled, targetPull, mapOutcome, Except.map, mapPull]

theorem chunk_exact
    (pull : Source → World → World × Except Fault (Pull Source Answer))
    {Return : (base : Unit) → Unit → Type}
    (client : Client (P := protocol Answer Fault) (Return := Return))
    (charge : Charge (provider pull)) (first later : Nat)
    (packet : Packet (provider pull) client ()) :
    advance (provider pull) client charge (first + later) packet =
      resume (provider pull) client charge later
        (advance (provider pull) client charge first packet) :=
  advance_add _ _ _ first later packet

/-- Local query refinement reuses the existing theorem for every client,
including clients that react to faults, retain bindings or suspend after yields. -/
theorem clients_preserved
    (source : Source → World → World × Except Fault (Pull Source Answer))
    (target : Target → World → World × Except Fault (Pull Target Answer))
    (map : Source → Target)
    (localLaw : ∀ cursor world,
      target (map cursor) world =
        ((source cursor world).1, mapOutcome map (source cursor world).2))
    {Return : (base : Unit) → Unit → Type}
    (client : Client (P := protocol Answer Fault) (Return := Return))
    (sourceCharge : Charge (provider source)) (targetCharge : Charge (provider target))
    (budget : Nat) (packet : Packet (provider source) client ()) :
    (hom source target map localLaw).outcome client
        (advance (provider source) client sourceCharge budget packet).2 =
      (advance (provider target) client targetCharge budget
        ((hom source target map localLaw).packet client packet)).2 :=
  Hom.advance client _ sourceCharge targetCharge budget packet

namespace Controls

def delayed : Nat → Nat → Nat × Except String (Pull Nat (Nat × Nat))
  | 0, world => (world + 1, .ok (.suspend 1))
  | 1, world => (world + 1, .ok (.yield (7, 1) 2))
  | _, world => (world + 1, .error "query fault")

theorem reply_keeps_its_live_cursor_and_effect :
    poll delayed (0, 4) = (.ok (.suspend ()), (1, 5)) := rfl

theorem answer_keeps_its_binding_witness :
    poll delayed (1, 5) = (.ok (.yield (7, 1) ()), (2, 6)) := rfl

theorem fault_is_not_empty_completion :
    (poll delayed (2, 6)).1 ≠ .ok .done := by
  intro impossible
  cases impossible

theorem terminal_fault_keeps_the_performed_world :
    (poll delayed (2, 6)).2.2 = 7 := rfl

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlOutcomeCursor
