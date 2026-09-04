import Mettapedia.Logic.AnytimeEvidence

/-!
# Proof-relevant evidence over a monotone certificate observer

`MonotoneCertificate` deliberately exposes only the proposition that some
sound evidence has appeared by a finite stage.  Algorithms and auditors often
need more: the evidence values themselves, their identity, and an explicit way
to retain an earlier value at every later stage.

`MonotoneEvidence` is that displayed, proof-relevant layer.  Forgetting the
evidence value gives a `MonotoneCertificate`; it does not identify values in
the evidence fibre.  Products and sums give the finite conjunction and
disjunction interfaces used by assumption-sensitive proof plans.

This separation is intentionally independent of any particular logic,
runtime, scheduler, or provenance algebra.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.DisplayedAnytimeEvidence

open Mettapedia.Logic.AnytimeEvidence

universe u

/-- Stage-indexed proof-relevant evidence for a proposition.  Persistence
retains an actual evidence value, not merely the fact that one exists. -/
structure MonotoneEvidence (claim : Prop) where
  EvidenceAt : Nat → Type u
  persist : ∀ {earlier later : Nat}, earlier ≤ later →
    EvidenceAt earlier → EvidenceAt later
  sound : ∀ {stage : Nat}, EvidenceAt stage → claim

namespace MonotoneEvidence

variable {claim : Prop}

/-- The thin observer forgets which evidence value was retained and reports
only whether the stage contains at least one. -/
def toCertificate (evidence : MonotoneEvidence.{u} claim) :
    MonotoneCertificate claim where
  acceptsAt stage := Nonempty (evidence.EvidenceAt stage)
  monotone := by
    intro earlier later bounded
    rintro ⟨witness⟩
    exact ⟨evidence.persist bounded witness⟩
  sound := by
    intro stage
    rintro ⟨witness⟩
    exact evidence.sound witness

@[simp] theorem toCertificate_acceptsAt
    (evidence : MonotoneEvidence.{u} claim) (stage : Nat) :
    evidence.toCertificate.acceptsAt stage ↔
      Nonempty (evidence.EvidenceAt stage) :=
  Iff.rfl

/-- Positive completeness of displayed evidence is exactly positive
completeness of its thin observer. -/
def EventuallyComplete (evidence : MonotoneEvidence.{u} claim) : Prop :=
  evidence.toCertificate.EventuallyComplete

/-- Reinterpret the claim by a sound implication without changing any
evidence value or its persistence map. -/
def map {target : Prop} (evidence : MonotoneEvidence.{u} claim)
    (implication : claim → target) : MonotoneEvidence.{u} target where
  EvidenceAt := evidence.EvidenceAt
  persist := evidence.persist
  sound witness := implication (evidence.sound witness)

@[simp] theorem map_EvidenceAt {target : Prop}
    (evidence : MonotoneEvidence.{u} claim) (implication : claim → target)
    (stage : Nat) :
    (evidence.map implication).EvidenceAt stage = evidence.EvidenceAt stage :=
  rfl

/-- Conjunctive evidence retains both component witnesses at one common
stage. -/
def prod {leftClaim rightClaim : Prop}
    (left : MonotoneEvidence.{u} leftClaim)
    (right : MonotoneEvidence.{u} rightClaim) :
    MonotoneEvidence.{u} (leftClaim ∧ rightClaim) where
  EvidenceAt stage := left.EvidenceAt stage × right.EvidenceAt stage
  persist bounded witness :=
    ⟨left.persist bounded witness.1, right.persist bounded witness.2⟩
  sound witness := ⟨left.sound witness.1, right.sound witness.2⟩

/-- Two positively complete evidence streams can be synchronized at the
maximum of their witness stages. -/
theorem prod_eventuallyComplete {leftClaim rightClaim : Prop}
    (left : MonotoneEvidence.{u} leftClaim)
    (right : MonotoneEvidence.{u} rightClaim)
    (leftComplete : left.EventuallyComplete)
    (rightComplete : right.EventuallyComplete) :
    (left.prod right).EventuallyComplete := by
  rintro ⟨leftHolds, rightHolds⟩
  obtain ⟨leftStage, ⟨leftEvidence⟩⟩ := leftComplete leftHolds
  obtain ⟨rightStage, ⟨rightEvidence⟩⟩ := rightComplete rightHolds
  refine ⟨max leftStage rightStage, ⟨?_, ?_⟩⟩
  · exact left.persist (Nat.le_max_left _ _) leftEvidence
  · exact right.persist (Nat.le_max_right _ _) rightEvidence

/-- Disjunctive evidence retains which branch supplied the witness. -/
def sum {leftClaim rightClaim : Prop}
    (left : MonotoneEvidence.{u} leftClaim)
    (right : MonotoneEvidence.{u} rightClaim) :
    MonotoneEvidence.{u} (leftClaim ∨ rightClaim) where
  EvidenceAt stage := Sum (left.EvidenceAt stage) (right.EvidenceAt stage)
  persist bounded witness :=
    match witness with
    | .inl leftWitness => .inl (left.persist bounded leftWitness)
    | .inr rightWitness => .inr (right.persist bounded rightWitness)
  sound witness :=
    match witness with
    | .inl leftWitness => Or.inl (left.sound leftWitness)
    | .inr rightWitness => Or.inr (right.sound rightWitness)

/-- Positive completeness is closed under disjunction while preserving the
identity of the successful branch. -/
theorem sum_eventuallyComplete {leftClaim rightClaim : Prop}
    (left : MonotoneEvidence.{u} leftClaim)
    (right : MonotoneEvidence.{u} rightClaim)
    (leftComplete : left.EventuallyComplete)
    (rightComplete : right.EventuallyComplete) :
    (left.sum right).EventuallyComplete := by
  intro holds
  rcases holds with leftHolds | rightHolds
  · obtain ⟨stage, ⟨witness⟩⟩ := leftComplete leftHolds
    exact ⟨stage, ⟨Sum.inl witness⟩⟩
  · obtain ⟨stage, ⟨witness⟩⟩ := rightComplete rightHolds
    exact ⟨stage, ⟨Sum.inr witness⟩⟩

end MonotoneEvidence

/-! ## A fibre-richness control -/

/-- Every stage contains two distinguishable Boolean evidence values for the
same true claim. -/
def boolFibre : MonotoneEvidence.{0} True where
  EvidenceAt := fun _ => Bool
  persist _ witness := witness
  sound _ := True.intro

/-- The evidence fibre is nontrivial even though its thin observer has only
the proposition that some evidence exists. -/
theorem boolFibre_two_values_over_one_observation :
    ∃ first second : boolFibre.EvidenceAt 0,
      first ≠ second ∧ boolFibre.toCertificate.acceptsAt 0 := by
  exact ⟨true, false, by simp, ⟨true⟩⟩

/-! ## Audited theorem crowns -/

#print axioms MonotoneEvidence.prod_eventuallyComplete
#print axioms MonotoneEvidence.sum_eventuallyComplete
#print axioms boolFibre_two_values_over_one_observation

end Mettapedia.Logic.DisplayedAnytimeEvidence
