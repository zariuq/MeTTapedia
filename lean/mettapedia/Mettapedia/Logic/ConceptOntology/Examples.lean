import Mettapedia.Logic.ConceptOntology.WMBridge

/-!
# Small Ontology Examples

These examples show the intended semantic separation:

- typed query extraction yields `memberEvidence`
- extensional inheritance is derived from object-level membership evidence
- typicality/default channels are separate and do not determine extensional
  inheritance on their own
-/

namespace Mettapedia.Logic.ConceptOntology.Examples

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.ConceptOntology

/-- Tiny object domain for ontology examples. -/
inductive Creature where
  | tweety
  | pingu
  | plane
  deriving DecidableEq, Repr, Fintype

/-- Tiny concept domain separating extensional inheritance from typicality. -/
inductive Concept where
  | bird
  | penguin
  | fly
  deriving DecidableEq, Repr, Fintype

/-- Separate query sorts for membership and typicality/default evidence. -/
inductive ToySort where
  | membership
  | typicality
  deriving DecidableEq, Repr, Fintype

/-- Typed toy query family. -/
inductive ToyQueryFamily : ToySort → Type where
  | member : Creature → Concept → ToyQueryFamily .membership
  | typical : Concept → Concept → ToyQueryFamily .typicality

abbrev ToyState := Sigma ToyQueryFamily → BinaryEvidence

noncomputable instance : EvidenceType ToyState := { (inferInstance : AddCommMonoid ToyState) with }

instance : WorldModelSigma ToyState ToySort ToyQueryFamily where
  evidence W q := W q
  evidence_add _W₁ _W₂ _q := rfl
  evidence_zero _q := rfl

@[simp] theorem toyState_evidence_eq
    (W : ToyState) (q : Sigma ToyQueryFamily) :
    WorldModelSigma.evidence W q = W q := rfl

@[simp] theorem toyState_evidenceAt_member_eq
    (W : ToyState) (x : Creature) (c : Concept) :
    WorldModelSigma.evidenceAt W (ToyQueryFamily.member x c) =
      W ⟨ToySort.membership, ToyQueryFamily.member x c⟩ := rfl

@[simp] theorem toyState_evidenceAt_typical_eq
    (W : ToyState) (c d : Concept) :
    WorldModelSigma.evidenceAt W (ToyQueryFamily.typical c d) =
      W ⟨ToySort.typicality, ToyQueryFamily.typical c d⟩ := rfl

def yes : BinaryEvidence := ⟨1, 0⟩

def strongYes : BinaryEvidence := ⟨2, 0⟩

@[simp] theorem binaryEvidence_pos_zero : BinaryEvidence.pos (0 : BinaryEvidence) = 0 := rfl

/-- A toy typed WM where penguins are birds, birds are typically flying, but
penguins are not guaranteed to fly. -/
def toyWM : ToyState
  | ⟨.membership, .member .tweety .bird⟩ => strongYes
  | ⟨.membership, .member .tweety .fly⟩ => strongYes
  | ⟨.membership, .member .pingu .bird⟩ => strongYes
  | ⟨.membership, .member .pingu .penguin⟩ => strongYes
  | ⟨.typicality, .typical .bird .fly⟩ => strongYes
  | _ => 0

def membershipBuilder : MembershipQueryBuilder Creature Concept ToySort ToyQueryFamily where
  memberSort := .membership
  member := ToyQueryFamily.member

def gate : EvidenceGate BinaryEvidence :=
  { accept := fun e => 0 < e.pos
    mono := by
      intro a b hab ha
      exact lt_of_lt_of_le ha hab.1 }

noncomputable def typicalityEvidence (W : ToyState) (c d : Concept) : BinaryEvidence :=
  WorldModelSigma.evidenceAt W (ToyQueryFamily.typical c d)

example :
    MembershipQueryBuilder.memberEvidence toyWM membershipBuilder Creature.pingu Concept.penguin =
      strongYes := rfl

example :
    (MembershipQueryBuilder.toEvidenceMembershipContext
      (State := ToyState) membershipBuilder).memberEvidence
        toyWM Creature.tweety Concept.bird = strongYes := rfl

theorem penguin_extensionally_inherits_bird :
    MembershipQueryBuilder.crispExtensionalInheritsAt
      (State := ToyState) gate toyWM membershipBuilder Concept.penguin Concept.bird := by
  rw [MembershipQueryBuilder.crispExtensionalInheritsAt_iff]
  intro x hx
  cases x with
  | tweety =>
      have hNot :
          ¬ gate.accept
            (MembershipQueryBuilder.memberEvidence
              toyWM membershipBuilder Creature.tweety Concept.penguin) := by
        simp [MembershipQueryBuilder.memberEvidence, membershipBuilder, toyWM,
          gate]
      exact False.elim (hNot hx)
  | pingu =>
      simp [MembershipQueryBuilder.memberEvidence, membershipBuilder, toyWM, gate, strongYes]
  | plane =>
      have hNot :
          ¬ gate.accept
            (MembershipQueryBuilder.memberEvidence
              toyWM membershipBuilder Creature.plane Concept.penguin) := by
        simp [MembershipQueryBuilder.memberEvidence, membershipBuilder, toyWM,
          gate]
      exact False.elim (hNot hx)

theorem bird_typically_flies :
    gate.accept (typicalityEvidence toyWM Concept.bird Concept.fly) := by
  simp [typicalityEvidence, toyWM, gate, strongYes]

theorem bird_not_extensionally_inherits_fly :
    ¬ MembershipQueryBuilder.crispExtensionalInheritsAt
      (State := ToyState) gate toyWM membershipBuilder Concept.bird Concept.fly := by
  rw [MembershipQueryBuilder.crispExtensionalInheritsAt_iff]
  push_neg
  refine ⟨Creature.pingu, ?_, ?_⟩
  · simp [MembershipQueryBuilder.memberEvidence, membershipBuilder, toyWM, gate, strongYes]
  · simp [MembershipQueryBuilder.memberEvidence, membershipBuilder, toyWM, gate]

theorem penguin_not_typically_flying :
    ¬ gate.accept (typicalityEvidence toyWM Concept.penguin Concept.fly) := by
  simp [typicalityEvidence, toyWM, gate]

end Mettapedia.Logic.ConceptOntology.Examples
