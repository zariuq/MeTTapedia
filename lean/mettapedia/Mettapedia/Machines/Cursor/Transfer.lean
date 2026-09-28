import Mettapedia.Machines.Cursor.Protocol

/-!
# Guarded transfer between cursor realizations

A family of providers shares a protocol and has locally proved maps to one
reference provider. An offer can replace the live state before an operation,
provided its reference state is unchanged. Refusal keeps the original state.
The resulting mixed provider realizes every client through the same reference
map. No uniform physical state, replay, or preferred backend is required.

These are semantic transfer laws. A C adapter must establish ownership,
snapshot and relocation obligations in its provider state and its local map.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u, u, u, u} Base Index}
variable {Backend : Type u}

/-- Physical alternatives share only the protocol, not a memory layout. -/
def familyProvider (family : Backend → Provider P) : Provider P where
  State base index := Σ backend, (family backend).State base index
  step value request :=
    let response := (family value.1).step value.2 request
    ⟨response.1, value.1, response.2⟩

def familyHom (family : Backend → Provider P) (reference : Provider P)
    (laws : ∀ backend, Hom (family backend) reference) :
    Hom (familyProvider family) reference where
  map value := (laws value.1).map value.2
  step value request := by
    rcases value with ⟨backend, state⟩
    exact (laws backend).step state request

/-- An optional proposal at a request boundary. It may inspect the requested
operation and retain whatever optimizer history is present in the state. -/
abbrev Offer (M : Provider P) := {base : Base} → {index : Index base} →
  M.State base index → P.Shape base index → Option (M.State base index)

def choose {M : Provider P} (offer : Offer M) {base : Base} {index : Index base}
    (state : M.State base index) (request : P.Shape base index) : M.State base index :=
  (offer state request).getD state

/-- Only successful offers need a transfer proof. A refusal cannot alter
the live state, advance a producer, or execute a host operation. -/
def SoundOffer {M reference : Provider P} (decode : Hom M reference)
    (offer : Offer M) : Prop :=
  ∀ {base index} (state next : M.State base index) (request : P.Shape base index),
    offer state request = some next → decode.map next = decode.map state

@[simp] theorem choose_refused {M : Provider P} (offer : Offer M)
    {base : Base} {index : Index base} (state : M.State base index)
    (request : P.Shape base index) (refused : offer state request = none) :
    choose offer state request = state := by simp [choose, refused]

theorem choose_preserves {M reference : Provider P} (decode : Hom M reference)
    (offer : Offer M) (sound : SoundOffer decode offer)
    {base : Base} {index : Index base} (state : M.State base index)
    (request : P.Shape base index) :
    decode.map (choose offer state request) = decode.map state := by
  cases offered : offer state request with
  | none => simp [choose, offered]
  | some next => simpa [choose, offered] using sound state next request offered

/-- A selected representation executes the request against the transferred
live state. There is one operation here, not a restarted client. -/
def switchingProvider (M : Provider P) (offer : Offer M) : Provider P where
  State := M.State
  step state request := M.step (choose offer state request) request

def switchingHom {M reference : Provider P} (decode : Hom M reference)
    (offer : Offer M) (sound : SoundOffer decode offer) :
    Hom (switchingProvider M offer) reference where
  map := decode.map
  step state request := by
    have law := decode.step (choose offer state request) request
    rw [choose_preserves decode offer sound state request] at law
    exact law

/-- Transfer and execution are separately charged. This does not assert that
an accepted offer is profitable. -/
def switchingCharge {M : Provider P} (offer : Offer M)
    (transferCost : Charge M) (operationCost : Charge M) :
    Charge (switchingProvider M offer) :=
  fun state request => transferCost state request +
    operationCost (choose offer state request) request

/-- Any number of representation changes preserves the actual bounded client
observation, with its live residual state mapped to the reference. -/
theorem switching_advance
    {Return : (base : Base) → Index base → Type u}
    (C : Client (P := P) (Return := Return))
    {M reference : Provider P} (decode : Hom M reference)
    (offer : Offer M) (sound : SoundOffer decode offer)
    (actualCost : Charge (switchingProvider M offer))
    (referenceCost : Charge reference) (fuel : Nat) {base : Base}
    (packet : Packet (switchingProvider M offer) C base) :
    (switchingHom decode offer sound).outcome C
        (advance (switchingProvider M offer) C actualCost fuel packet).2 =
      (advance reference C referenceCost fuel
        ((switchingHom decode offer sound).packet C packet)).2 :=
  Hom.advance C (switchingHom decode offer sound) actualCost referenceCost fuel packet

end Mettapedia.Machines.Cursor
