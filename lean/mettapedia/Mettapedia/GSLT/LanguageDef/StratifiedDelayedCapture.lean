import Mettapedia.GSLT.Core.RankedDependency
import Mettapedia.GSLT.LanguageDef.SupportRestrictedSourceViewCompilation

/-!
# Capture-time stratification for delayed values

An owned delayed value may contain references to other owned delayed values.
Ownership alone does not make that graph safe: a self-reference or a cycle can
make semantic forcing diverge even when ordinary term-level occurs checking
sees no cycle.

This module states the missing admission contract independently of a physical
carrier.  Every capture has an immutable payload, a distinct capture clock,
and a finite set of retained capture identities.  A family is admitted only
when every retained identity was captured strictly earlier in an independent
well-founded order.  The resulting dependency graph is well founded and
acyclic, and it supplies the induction principle required by a forcing or GC
realization.

The capture clock is deliberately not `SourceView.generation`.  The latter is
part of variable identity and instantiation semantics; a runtime growth clock
is the chronological authority for ownership.  Conflating them would turn a
namespace into a lifetime proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.StratifiedDelayedCapture

open Mettapedia.GSLT.Core.RankedDependency
open Mettapedia.GSLT.LanguageDef.SupportRestrictedSourceViewCompilation

universe uCapture uClock uPayload uOwner uRevision uPayload₂

/-- An immutable family of owned captures together with the exact finite
dependency set of each payload.  The dependency relation is semantic
metadata for a prospective physical carrier; no runtime representation is
prescribed. -/
structure Family
    (Capture : Type uCapture) (Clock : Type uClock)
    (Payload : Type uPayload) [DecidableEq Capture] where
  payload : Capture → Payload
  capturedAt : Capture → Clock
  references : Capture → Finset Capture
  earlier : Clock → Clock → Prop
  earlierWellFounded : WellFounded earlier
  referenceEarlier :
    ∀ {capture dependency},
      dependency ∈ references capture →
        earlier (capturedAt dependency) (capturedAt capture)

namespace Family

variable {Capture : Type uCapture} {Clock : Type uClock}
  {Payload : Type uPayload} {Payload₂ : Type uPayload₂}
  [DecidableEq Capture]

/-- The direct dependency relation exposed by the finite reference sets. -/
def DependsOn (family : Family Capture Clock Payload)
    (capture dependency : Capture) : Prop :=
  dependency ∈ family.references capture

/-- Forget payloads and expose the generic well-founded dependency object. -/
def dependencyOrder (family : Family Capture Clock Payload) :
    Mettapedia.GSLT.Core.RankedDependency.Order Capture Clock where
  rank := family.capturedAt
  earlier := family.earlier
  earlierWellFounded := family.earlierWellFounded
  dependsOn := family.DependsOn
  decreases := family.referenceEarlier

theorem dependencyOrder_precedes_iff
    (family : Family Capture Clock Payload)
    (dependency capture : Capture) :
    family.dependencyOrder.Precedes dependency capture ↔
      dependency ∈ family.references capture :=
  Iff.rfl

/-- No admitted capture directly retains itself. -/
theorem no_self_reference (family : Family Capture Clock Payload)
    (capture : Capture) :
    capture ∉ family.references capture := by
  exact family.dependencyOrder.no_self_dependency capture

/-- No nonempty path through retained captures returns to its origin. -/
theorem no_reference_cycle (family : Family Capture Clock Payload)
    (capture : Capture) :
    ¬ Relation.TransGen family.dependencyOrder.Precedes capture capture :=
  family.dependencyOrder.no_dependency_cycle capture

/-- A forcing, tracing, or compaction property that is closed under already
processed dependencies holds for every capture. -/
theorem dependency_induction (family : Family Capture Clock Payload)
    (motive : Capture → Prop)
    (step :
      ∀ capture,
        (∀ dependency,
          dependency ∈ family.references capture → motive dependency) →
        motive capture) :
    ∀ capture, motive capture := by
  exact family.dependencyOrder.dependency_induction motive step

/-- Payload transformation leaves capture chronology and dependencies
unchanged.  This is the representation-independence law used when compiling
an abstract delayed value to a different owned payload. -/
def mapPayload (family : Family Capture Clock Payload)
    (transform : Payload → Payload₂) : Family Capture Clock Payload₂ where
  payload := transform ∘ family.payload
  capturedAt := family.capturedAt
  references := family.references
  earlier := family.earlier
  earlierWellFounded := family.earlierWellFounded
  referenceEarlier := family.referenceEarlier

@[simp]
theorem mapPayload_capturedAt
    (family : Family Capture Clock Payload)
    (transform : Payload → Payload₂) (capture : Capture) :
    (family.mapPayload transform).capturedAt capture =
      family.capturedAt capture :=
  rfl

@[simp]
theorem mapPayload_references
    (family : Family Capture Clock Payload)
    (transform : Payload → Payload₂) (capture : Capture) :
    (family.mapPayload transform).references capture =
      family.references capture :=
  rfl

theorem mapPayload_dependencyOrder
    (family : Family Capture Clock Payload)
    (transform : Payload → Payload₂) :
    (family.mapPayload transform).dependencyOrder =
      family.dependencyOrder :=
  rfl

/-! ## Runtime-growth-clock specialization -/

/-- Construct a stratified family from a natural-number growth clock.  This
is the shape required of a chronological append-only capture store. -/
def ofGrowthClock
    (payload : Capture → Payload)
    (capturedAt : Capture → Nat)
    (references : Capture → Finset Capture)
    (referenceEarlier :
      ∀ {capture dependency},
        dependency ∈ references capture →
          capturedAt dependency < capturedAt capture) :
    Family Capture Nat Payload where
  payload := payload
  capturedAt := capturedAt
  references := references
  earlier := (· < ·)
  earlierWellFounded := wellFounded_lt
  referenceEarlier := referenceEarlier

/-- A support-restricted source snapshot is one possible payload of a
stratified family.  Its own variable generation remains independent of the
capture clock. -/
abbrev SupportSnapshotFamily
    (Capture : Type uCapture) (Clock : Type uClock)
    (Owner : Type uOwner) (Revision : Type uRevision)
    [DecidableEq Capture] :=
  Family Capture Clock (SupportSnapshot Owner Revision)

end Family

/-! ## Positive and negative controls -/

namespace Canaries

inductive Capture
  | first
  | second
  | third
deriving DecidableEq

def payload : Capture → Nat
  | .first => 10
  | .second => 20
  | .third => 30

def capturedAt : Capture → Nat
  | .first => 0
  | .second => 1
  | .third => 2

def references : Capture → Finset Capture
  | .first => ∅
  | .second => {.first}
  | .third => {.first, .second}

theorem referenceEarlier {capture dependency : Capture}
    (member : dependency ∈ references capture) :
    capturedAt dependency < capturedAt capture := by
  cases capture <;> cases dependency <;>
    simp [references, capturedAt] at member ⊢

def family : Family Capture Nat Nat :=
  Family.ofGrowthClock payload capturedAt references referenceEarlier

/-- A later capture may retain several older values. -/
example :
    Capture.first ∈ family.references .third ∧
      Capture.second ∈ family.references .third := by
  decide

/-- The chronological family has no capture cycle. -/
example :
    ¬ Relation.TransGen family.dependencyOrder.Precedes
      Capture.third Capture.third :=
  family.no_reference_cycle .third

/-- The smallest dangerous proposal, a capture retaining itself, fails the
strict growth-clock admission condition. -/
example :
    ¬ capturedAt Capture.second < capturedAt Capture.second := by
  decide

/-- A backward edge from the oldest capture to the newest also fails
admission. -/
example :
    ¬ capturedAt Capture.third < capturedAt Capture.first := by
  decide

#print axioms Family.no_self_reference
#print axioms Family.no_reference_cycle
#print axioms Family.dependency_induction
#print axioms Family.mapPayload_dependencyOrder

end Canaries

end Mettapedia.GSLT.LanguageDef.StratifiedDelayedCapture
