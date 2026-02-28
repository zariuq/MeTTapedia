import Mettapedia.Logic.PLNProbabilisticEventCalculus
import Mettapedia.Logic.GovernanceReasoning.Bridge

/-!
# Abstract Modal Query Encoder

Provides a single abstract structure `ModalQueryEncoder (Modality Referent Query)` that
unifies two concrete query-encoder patterns in the codebase:

- `EventQueryEncoder` (event calculus, three temporal modalities)
- `DeonticQueryEncoder.modalQuery` (governance, four deontic modalities)

Both have the shape `Modality → Referent → Query`, but were defined independently.
This module introduces the abstract form and shows each is an instance.

## Mathematical Note

A `ModalQueryEncoder M R Q` is simply a function `M → R → Q`, packaged as a structure
so that it carries the same interface conventions as the existing encoders.  The
correspondence with `EventQueryEncoder` is a bijection (roundtrip identity, both ways).
The `DeonticQueryEncoder` instance is a projection of an existing field.

## References

- Kowalski, R. & Sergot, M. (1986). "A logic-based calculus of events"
- Shanahan, M. (1999). "The event calculus explained"
- Hobbs, J. (1985). "Ontological Promiscuity"
-/

namespace Mettapedia.Logic.ModalQueryEncoder

open Mettapedia.Logic.PLNProbabilisticEventCalculus
open Mettapedia.Logic.GovernanceReasoning.Bridge
open Mettapedia.Logic.GovernanceReasoning.Core

/-! ## §1 Abstract Encoder Structure -/

/-- An abstract modal query encoder: maps a modality × referent pair to a query.

    This is the common abstract structure shared by event-calculus encoders
    (where `Modality` is a temporal modality and `Referent = Event × Time`)
    and deontic encoders (where `Modality` is `DeonticModality` and
    `Referent = Eventuality Entity Pred`). -/
structure ModalQueryEncoder (Modality Referent Query : Type*) where
  /-- Encode a modal query from a modality and a referent. -/
  encode : Modality → Referent → Query

/-! ## §2 Event-Calculus Modality -/

/-- The three temporal modalities of the event calculus.

    These correspond to the three fields of `EventQueryEncoder`:
    `holdsAt`, `initiatedAt`, `terminatedAt`.

    Note: `EventCalcSort` in `PLNProbabilisticEventCalculus` uses the same
    three constructors (`.holds`, `.initiated`, `.terminated`).  `EventModality`
    uses more descriptive names matching the `EventQueryEncoder` field names. -/
inductive EventModality where
  | holdsAt       -- Fluent holds at time t
  | initiatedAt   -- Fluent is initiated at time t
  | terminatedAt  -- Fluent is terminated at time t
  deriving DecidableEq, Repr

/-! ## §3 EventQueryEncoder ≃ ModalQueryEncoder EventModality -/

/-- Convert an `EventQueryEncoder` to an abstract `ModalQueryEncoder`.

    The referent type becomes the product `Event × Time`, unifying the two
    arguments of each encoder field into a single type. -/
def eventQueryEncoderToModal {Event Time Query : Type*}
    (enc : EventQueryEncoder Event Time Query) :
    ModalQueryEncoder EventModality (Event × Time) Query where
  encode
    | .holdsAt,      ⟨e, t⟩ => enc.holdsAt e t
    | .initiatedAt,  ⟨e, t⟩ => enc.initiatedAt e t
    | .terminatedAt, ⟨e, t⟩ => enc.terminatedAt e t

/-- Convert a `ModalQueryEncoder EventModality (Event × Time) Q` back to an
    `EventQueryEncoder`, splitting the product referent into two arguments. -/
def modalToEventQueryEncoder {Event Time Query : Type*}
    (m : ModalQueryEncoder EventModality (Event × Time) Query) :
    EventQueryEncoder Event Time Query where
  holdsAt     e t := m.encode .holdsAt ⟨e, t⟩
  initiatedAt e t := m.encode .initiatedAt ⟨e, t⟩
  terminatedAt e t := m.encode .terminatedAt ⟨e, t⟩

/-- Roundtrip (modal → event → modal): the composition is the identity. -/
@[simp]
theorem eventQueryEncoder_roundtrip_of_to {Event Time Query : Type*}
    (m : ModalQueryEncoder EventModality (Event × Time) Query) :
    eventQueryEncoderToModal (modalToEventQueryEncoder m) = m := by
  simp only [eventQueryEncoderToModal, modalToEventQueryEncoder]
  congr 1
  funext modality ⟨e, t⟩
  cases modality <;> rfl

/-- Roundtrip (event → modal → event): the composition is the identity. -/
@[simp]
theorem eventQueryEncoder_roundtrip_to_of {Event Time Query : Type*}
    (enc : EventQueryEncoder Event Time Query) :
    modalToEventQueryEncoder (eventQueryEncoderToModal enc) = enc := by
  simp [modalToEventQueryEncoder, eventQueryEncoderToModal]

/-! ## §4 DeonticQueryEncoder Instance -/

/-- Embed a `DeonticQueryEncoder` as a `ModalQueryEncoder`.

    The `modalQuery` field of `DeonticQueryEncoder` has exactly the
    abstract shape `DeonticModality → Eventuality Entity Pred → Query`,
    so the embedding is a direct projection. -/
def deonticQueryEncoderToModal {Entity Pred Query : Type*}
    (d : DeonticQueryEncoder Entity Pred Query) :
    ModalQueryEncoder DeonticModality (Eventuality Entity Pred) Query where
  encode := d.modalQuery

/-- The embedding recovers `modalQuery` on the nose. -/
@[simp]
theorem deonticQueryEncoder_encode_eq {Entity Pred Query : Type*}
    (d : DeonticQueryEncoder Entity Pred Query)
    (m : DeonticModality) (e : Eventuality Entity Pred) :
    (deonticQueryEncoderToModal d).encode m e = d.modalQuery m e := rfl

/-! ## §5 Summary -/

#check @ModalQueryEncoder
#check @EventModality
#check @eventQueryEncoderToModal
#check @modalToEventQueryEncoder
#check @eventQueryEncoder_roundtrip_of_to
#check @eventQueryEncoder_roundtrip_to_of
#check @deonticQueryEncoderToModal

end Mettapedia.Logic.ModalQueryEncoder
