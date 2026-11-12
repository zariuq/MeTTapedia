import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Generic query clients and sampled providers

These are the canonical protocol, client and provider definitions used by the
adaptive-query cursor developments. Concrete authority, binding-store and
retained-force adapters belong downstream. Their presence must not become a
dependency of a generic provider interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReadOnlyQuery

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.Machines.ReadOnlyQuery (Program Reads Observation)

universe u
variable {Key Value Answer : Type u}

abbrev protocol (Key Value : Type u) :
    IndexedPolynomial PUnit.{u + 1} (fun _ => PUnit.{u + 1}) where
  Shape _ _ := Key
  Position _ := Value
  next _ _ := .unit

/-- Reads are retained in reverse chronological order so a new read is a
single list constructor. The immutable store view is supplied by the provider. -/
def provider (store : Key → Value) : Provider (protocol Key Value) where
  State _ _ := Reads Key Value
  step reads key := ⟨store key, (key, store key) :: reads⟩

def client : Client (P := protocol Key Value) (Return := fun _ _ => Answer) where
  V _ _ := Program Key Value Answer
  str := fun _ _ => ↾(fun program => match program with
    | .pure answer => ⟨.inl answer, fun impossible => nomatch impossible⟩
    | .read key next => ⟨.inr key, next⟩)

end Mettapedia.Machines.Cursor.ReadOnlyQuery

namespace Mettapedia.Machines.Cursor.ReadOnlyQuery.Sampled

open Mettapedia.Machines.ReadOnlyQuery (Program Reads Observation)

universe u
variable {Key Value Answer Context : Type u}

/-- A real sampling operation returns its actual reply and next context. -/
def provider (sample : Context → Key → Value × Context) :
    Cursor.Provider (protocol Key Value) where
  State _ _ := Context × Reads Key Value
  step saved key :=
    let observed := sample saved.1 key
    ⟨observed.1, observed.2, (key, observed.1) :: saved.2⟩

def charge (sample : Context → Key → Value × Context) (price : Key → Nat) :
    Cursor.Charge (provider sample) := fun _ key => price key

def fixedCharge (store : Key → Value) (price : Key → Nat) :
    Cursor.Charge (ReadOnlyQuery.provider store) := fun _ key => price key

/-- This is the existing cursor, with the existing adaptive query client. -/
def advance (sample : Context → Key → Value × Context) (price : Key → Nat)
    (fuel : Nat) (program : Program Key Value Answer) (context : Context)
    (reads : Reads Key Value) :=
  Cursor.advance (provider sample) client (charge sample price) (base := PUnit.unit) fuel
    ⟨PUnit.unit, program, context, reads⟩

def fixedAdvance (store : Key → Value) (price : Key → Nat) (fuel : Nat)
    (program : Program Key Value Answer) (reads : Reads Key Value) :=
  Cursor.advance (ReadOnlyQuery.provider store) client (fixedCharge store price) (base := PUnit.unit) fuel
    ⟨PUnit.unit, program, reads⟩

def savedState (sample : Context → Key → Value × Context) :
    Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit →
      Context × Reads Key Value
  | .paused ⟨_, _, saved⟩ => saved
  | .done ⟨_, _, saved⟩ => saved

def recorded (sample : Context → Key → Value × Context)
    (outcome : Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit) :
    Reads Key Value := (savedState sample outcome).2.reverse

def completed? (sample : Context → Key → Value × Context) :
    Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit →
      Option (Observation Key Value Answer)
  | .paused _ => none
  | .done ⟨_, answer, saved⟩ => some ⟨answer, saved.2.reverse⟩

def resume (sample : Context → Key → Value × Context) (price : Key → Nat) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit) :=
  Cursor.resume (provider sample) client (charge sample price) fuel previous

def fixedResume (store : Key → Value) (price : Key → Nat) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (ReadOnlyQuery.provider store) (client (Answer := Answer)) PUnit.unit) :=
  Cursor.resume (ReadOnlyQuery.provider store) client (fixedCharge store price) fuel previous

end Mettapedia.Machines.Cursor.ReadOnlyQuery.Sampled
