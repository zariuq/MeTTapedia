import Mettapedia.Logic.HOL.IndexedCarrier

/-! # Indexed preparation witnesses in raw HOL carriers

Witnesses retain their source state and firing. Empty witness fibres stay
empty; the extra raw inhabitant is invalid. Result and permission operations
read the retained witness, while the preparation relation checks its indices.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparationEncoding

open Mettapedia.Logic.HOL

universe uS uF uP

variable (State : Type uS) (Firing : State → Type uF)
  (Preparation : (s : State) → Firing s → Sort uP)

abbrev Firings := (s : State) × Firing s
abbrev Witnesses := (entry : Firings State Firing) × PLift (Preparation entry.1 entry.2)
abbrev States := Option State
abbrev RawFirings := Option (Firings State Firing)
abbrev RawWitnesses := Option (Witnesses State Firing Preparation)

def encodeFiring {s : State} (f : Firing s) : RawFirings State Firing := some ⟨s,f⟩
def encodeWitness {s : State} (f : Firing s) (p : Preparation s f) : RawWitnesses State Firing Preparation :=
  some ⟨⟨s,f⟩, PLift.up p⟩

def prepares (s : States State) (f : RawFirings State Firing) : RawWitnesses State Firing Preparation → Prop
  | none => False
  | some ⟨entry, _⟩ => s = some entry.1 ∧ f = some entry

def result (next : (s : State) → (f : Firing s) → Preparation s f → State) :
    RawWitnesses State Firing Preparation → States State
  | none => none
  | some ⟨entry, p⟩ => some (next entry.1 entry.2 p.down)

def permission (allow : (s : State) → (f : Firing s) → Preparation s f → Prop) :
    RawWitnesses State Firing Preparation → Prop
  | none => False
  | some ⟨entry, p⟩ => allow entry.1 entry.2 p.down

theorem prepares_encoded {s : State} (f : Firing s) (p : Preparation s f) :
    prepares State Firing Preparation (some s) (encodeFiring State Firing f)
      (encodeWitness State Firing Preparation f p) := ⟨rfl,rfl⟩

theorem prepares_iff {s : State} (f : Firing s) (raw : RawWitnesses State Firing Preparation) :
    prepares State Firing Preparation (some s) (encodeFiring State Firing f) raw ↔
      ∃ p : Preparation s f, raw = encodeWitness State Firing Preparation f p := by
  constructor
  · intro valid
    cases raw with
    | none => cases valid
    | some witness =>
        rcases witness with ⟨⟨source, firing⟩, prepared⟩
        have same : (⟨s,f⟩ : Firings State Firing) = ⟨source,firing⟩ := Option.some.inj valid.2
        cases same
        exact ⟨prepared.down, rfl⟩
  · rintro ⟨p,rfl⟩
    exact prepares_encoded State Firing Preparation f p

theorem witness_exists_iff {s : State} (f : Firing s) :
    (∃ raw, prepares State Firing Preparation (some s) (encodeFiring State Firing f) raw) ↔
      Nonempty (Preparation s f) := by
  simp only [prepares_iff]
  constructor
  · rintro ⟨raw,p,_⟩
    exact ⟨p⟩
  · rintro ⟨p⟩
    exact ⟨encodeWitness State Firing Preparation f p,p,rfl⟩

theorem encodeWitness_injective {s : State} (f : Firing s) :
    Function.Injective (encodeWitness State Firing Preparation f) := by
  intro p q same
  have lifted : (PLift.up p : PLift (Preparation s f)) = PLift.up q :=
    IndexedCarrier.encode_injective (fun entry : Firings State Firing => PLift (Preparation entry.1 entry.2)) ⟨s,f⟩ same
  exact congrArg PLift.down lifted

theorem result_encoded (next : (s : State) → (f : Firing s) → Preparation s f → State)
    {s : State} (f : Firing s) (p : Preparation s f) :
    result State Firing Preparation next (encodeWitness State Firing Preparation f p) = some (next s f p) := rfl

theorem permission_encoded (allow : (s : State) → (f : Firing s) → Preparation s f → Prop)
    {s : State} (f : Firing s) (p : Preparation s f) :
    permission State Firing Preparation allow (encodeWitness State Firing Preparation f p) ↔ allow s f p := Iff.rfl

theorem invalid_witness (s : States State) (f : RawFirings State Firing) :
    ¬prepares State Firing Preparation s f none := not_false

theorem wrong_source {s : State} (other : State) (different : other ≠ s)
    (f : Firing s) (p : Preparation s f) :
    ¬prepares State Firing Preparation (some other) (encodeFiring State Firing f)
      (encodeWitness State Firing Preparation f p) := by
  rintro ⟨same,_⟩
  exact different (Option.some.inj same)

#print axioms prepares_iff
#print axioms encodeWitness_injective
#print axioms wrong_source

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparationEncoding
