import Mettapedia.Logic.ConceptOntology.WMBridge

/-!
# AtomQuery Ontology Canary

This module instantiates the ontology bridge on the live `AtomQuery` surface:

- membership is encoded by `AtomQuery.prop`
- extensional inheritance links are encoded by `AtomQuery.link`
- the current pairwise extensional hook is exhibited as a summary of extents
-/

namespace Mettapedia.Logic.ConceptOntology.AtomQueryCanary

open Classical
open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNIntensionalWorldModel
open Mettapedia.Logic.ConceptOntology
open scoped ENNReal

noncomputable section

/-- Tiny object domain. -/
inductive Creature where
  | tweety
  | pingu
  | plane
  deriving DecidableEq, Repr

/-- Tiny concept domain. -/
inductive Concept where
  | bird
  | penguin
  | fly
  deriving DecidableEq, Repr

/-- Single atom type using the repo's standard `AtomQuery` constructors. -/
inductive OntologyAtom where
  | member : Creature → Concept → OntologyAtom
  | extensional : Concept → OntologyAtom
  | assoc : Concept → OntologyAtom
  | pat : Concept → OntologyAtom
  deriving DecidableEq, Repr

/-- Canonical object extents for the canary concepts. -/
def conceptExtent : Concept → Set Creature
  | .bird => {x | x = .tweety ∨ x = .pingu}
  | .penguin => {x | x = .pingu}
  | .fly => {x | x = .tweety}

abbrev ToyState := ℕ

instance : EvidenceType ToyState := { (inferInstance : AddCommMonoid ToyState) with }

def supportToken (W : ToyState) : BinaryEvidence :=
  ⟨(W : ℝ≥0∞), 0⟩

@[simp] theorem binaryEvidence_zero_pos : (0 : BinaryEvidence).pos = 0 := by
  change BinaryEvidence.zero.pos = 0
  rfl

@[simp] theorem binaryEvidence_zero_neg : (0 : BinaryEvidence).neg = 0 := by
  change BinaryEvidence.zero.neg = 0
  rfl

@[simp] theorem supportToken_zero :
    supportToken 0 = 0 := by
  ext <;> simp [supportToken]

@[simp] theorem supportToken_add (W₁ W₂ : ToyState) :
    supportToken (W₁ + W₂) = supportToken W₁ + supportToken W₂ := by
  ext <;> simp [supportToken, BinaryEvidence.hplus_def]

theorem supportToken_pos_of_ne_zero {W : ToyState} (hW : W ≠ 0) :
    0 < (supportToken W).pos := by
  simpa [supportToken] using
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hW) : (0 : ℝ≥0∞) < (W : ℝ≥0∞))

theorem ite_supportToken_add (p : Prop) [Decidable p] (W₁ W₂ : ToyState) :
    (if p then supportToken (W₁ + W₂) else 0) =
      (if p then supportToken W₁ else 0) + (if p then supportToken W₂ else 0) := by
  by_cases hp : p <;> simp [hp, supportToken_add, BinaryEvidence.hplus_def]

theorem ite_supportToken_zero (p : Prop) [Decidable p] :
    (if p then supportToken 0 else 0) = (0 : BinaryEvidence) := by
  by_cases hp : p <;> simp [hp, supportToken_zero]

def strongYes : BinaryEvidence :=
  supportToken 2

def subsetSummary (W : ToyState) (A B : Set Creature) : BinaryEvidence :=
  if A ⊆ B then supportToken W else 0

def liveState : ToyState := 2

instance : BinaryWorldModel ToyState (AtomQuery OntologyAtom) where
  evidence W
    | .prop (.member x c) =>
        if x ∈ conceptExtent c then supportToken W else 0
    | .link (.extensional a) (.extensional b) =>
        subsetSummary W (conceptExtent a) (conceptExtent b)
    | .link (.assoc a) (.assoc b) =>
        if (a = .penguin ∧ b = .bird) ∨ (a = .bird ∧ b = .fly) then supportToken W else 0
    | .link (.pat a) (.pat b) =>
        if a = .penguin ∧ b = .bird then supportToken W else 0
    | _ => 0
  evidence_add W₁ W₂ q := by
    cases q with
    | prop a =>
        cases a with
        | member x c =>
            simpa [BinaryEvidence.hplus_def] using
              ite_supportToken_add (p := x ∈ conceptExtent c) W₁ W₂
        | extensional c => simp
        | assoc c => simp
        | pat c => simp
    | link a b =>
        cases a with
        | member x c =>
            cases b <;> simp
        | extensional a =>
            cases b with
            | extensional b =>
                simpa [subsetSummary, BinaryEvidence.hplus_def] using
                  ite_supportToken_add (p := conceptExtent a ⊆ conceptExtent b) W₁ W₂
            | member x c => simp
            | assoc c => simp
            | pat c => simp
        | assoc a =>
            cases b with
            | assoc b =>
                simpa [BinaryEvidence.hplus_def] using
                  ite_supportToken_add
                    (p := (a = .penguin ∧ b = .bird) ∨ (a = .bird ∧ b = .fly)) W₁ W₂
            | member x c => simp
            | extensional c => simp
            | pat c => simp
        | pat a =>
            cases b with
            | pat b =>
                simpa [BinaryEvidence.hplus_def] using
                  ite_supportToken_add (p := a = .penguin ∧ b = .bird) W₁ W₂
            | member x c => simp
            | extensional c => simp
            | assoc c => simp
    | linkCond xs a =>
        simp
  evidence_zero q := by
    cases q with
    | prop a =>
        cases a with
        | member x c =>
            simp
        | extensional c => rfl
        | assoc c => rfl
        | pat c => rfl
    | link a b =>
        cases a with
        | member x c =>
            cases b <;> rfl
        | extensional a =>
            cases b with
            | extensional b =>
                simp [subsetSummary]
            | member x c => rfl
            | assoc c => rfl
            | pat c => rfl
        | assoc a =>
            cases b with
            | assoc b =>
                simp
            | member x c => rfl
            | extensional c => rfl
            | pat c => rfl
        | pat a =>
            cases b with
            | pat b =>
                simp
            | member x c => rfl
            | extensional c => rfl
            | assoc c => rfl
    | linkCond xs a =>
        simp

local instance : WorldModelSigma ToyState PUnit (fun _ : PUnit => AtomQuery OntologyAtom) :=
  WorldModelSigma.ofWorldModelUnit
    (State := ToyState) (Query := AtomQuery OntologyAtom)

def memberEncoder :
    MembershipAtomEncoder Creature Concept OntologyAtom where
  atomOf := OntologyAtom.member

def memberBuilder :
    MembershipQueryBuilder Creature Concept PUnit (fun _ : PUnit => AtomQuery OntologyAtom) :=
  memberEncoder.toMembershipQueryBuilder

def pairEnc : InheritanceQueryBuilder Concept (AtomQuery OntologyAtom) where
  extensional := fun a b => .link (.extensional a) (.extensional b)
  intensionalAssoc := fun a b => .link (.assoc a) (.assoc b)
  intensionalPAT := fun a b => .link (.pat a) (.pat b)
  mixed := fun a b => .link (.extensional a) (.extensional b)

def gate : EvidenceGate BinaryEvidence :=
  EvidenceGate.positiveSupport

theorem subsetSummary_mono
    (W : ToyState)
    {A B C D : Set Creature}
    (hCA : C ⊆ A) (hBD : B ⊆ D) :
    subsetSummary W A B ≤ subsetSummary W C D := by
  by_cases hAB : A ⊆ B
  · have hCD : C ⊆ D := by
      intro x hxC
      exact hBD (hAB (hCA hxC))
    simp [subsetSummary, hAB, hCD, supportToken]
  · by_cases hCD : C ⊆ D
    · dsimp [subsetSummary]
      rw [if_neg hAB, if_pos hCD]
      constructor
      · exact bot_le
      · rfl
    · simp [subsetSummary, hAB, hCD]

def activeExtent (W : ToyState) (c : Concept) : Set Creature :=
  if W = 0 then ∅ else conceptExtent c

@[simp] theorem memberEvidence_eq_support (W : ToyState) (x : Creature) (c : Concept) :
    MembershipQueryBuilder.memberEvidence
        (State := ToyState) W memberBuilder x c =
      if x ∈ conceptExtent c then supportToken W else 0 := by
  rfl

@[simp] theorem extensionalEvidence_eq_subsetSummary
    (W : ToyState) (a b : Concept) :
    InheritanceQueryBuilder.extensionalEvidence
        (State := ToyState) (Atom := Concept) (Query := AtomQuery OntologyAtom)
        W pairEnc a b =
      subsetSummary W (conceptExtent a) (conceptExtent b) := by
  rfl

theorem crispExtentAt_eq_activeExtent (W : ToyState) (c : Concept) :
    MembershipQueryBuilder.crispExtentAt
      (State := ToyState) gate W memberBuilder c = activeExtent W c := by
  ext x
  rw [MembershipQueryBuilder.mem_crispExtentAt_iff, activeExtent]
  by_cases hW : W = 0
  · by_cases hx : x ∈ conceptExtent c
    · rw [if_pos hW, memberEvidence_eq_support, if_pos hx]
      constructor
      · intro h
        have hf : False := by
          simp [gate, hW, supportToken_zero] at h
        exact False.elim hf
      · intro h
        cases h
    · rw [if_pos hW, memberEvidence_eq_support, if_neg hx]
      constructor
      · intro h
        have hf : False := by
          simp [gate] at h
        exact False.elim hf
      · intro h
        cases h
  · by_cases hx : x ∈ conceptExtent c
    · rw [if_neg hW, memberEvidence_eq_support, if_pos hx]
      constructor
      · intro _
        exact hx
      · intro _
        simpa [gate] using supportToken_pos_of_ne_zero hW
    · rw [if_neg hW, memberEvidence_eq_support, if_neg hx]
      constructor
      · intro h
        have hf : False := by
          simp [gate] at h
        exact False.elim hf
      · intro h
        exact False.elim (hx h)

def factorization :
    ExtensionalHookFactorization
      ToyState Creature Concept PUnit (AtomQuery OntologyAtom)
      (fun _ : PUnit => AtomQuery OntologyAtom) gate memberBuilder pairEnc where
  summarize := subsetSummary
  summarize_mono := by
    intro W A B C D hCA hBD
    exact subsetSummary_mono W hCA hBD
  factor := by
    intro W a b
    rw [extensionalEvidence_eq_subsetSummary, crispExtentAt_eq_activeExtent,
      crispExtentAt_eq_activeExtent]
    by_cases hW : W = 0
    · simp [activeExtent, subsetSummary, hW, supportToken_zero]
    · simp [activeExtent, subsetSummary, hW]

theorem canary_memberEvidence_uses_AtomQuery_prop :
    MembershipQueryBuilder.memberEvidence
        (State := ToyState) liveState memberBuilder Creature.pingu Concept.penguin =
      strongYes := by
  simp [liveState, strongYes, conceptExtent, supportToken]

theorem canary_penguin_extensionally_inherits_bird :
    MembershipQueryBuilder.crispExtensionalInheritsAt
      (State := ToyState) gate liveState memberBuilder Concept.penguin Concept.bird := by
  change MembershipQueryBuilder.crispExtentAt gate liveState memberBuilder Concept.penguin ⊆
      MembershipQueryBuilder.crispExtentAt gate liveState memberBuilder Concept.bird
  rw [crispExtentAt_eq_activeExtent, crispExtentAt_eq_activeExtent]
  intro x hx
  simp [activeExtent, liveState, conceptExtent] at hx ⊢
  exact Or.inr hx

theorem canary_bird_not_extensionally_inherit_fly :
    ¬ MembershipQueryBuilder.crispExtensionalInheritsAt
      (State := ToyState) gate liveState memberBuilder Concept.bird Concept.fly := by
  change ¬ (MembershipQueryBuilder.crispExtentAt gate liveState memberBuilder Concept.bird ⊆
      MembershipQueryBuilder.crispExtentAt gate liveState memberBuilder Concept.fly)
  rw [crispExtentAt_eq_activeExtent, crispExtentAt_eq_activeExtent]
  intro h
  have hxBird : Creature.pingu ∈ activeExtent liveState Concept.bird := by
    simp [activeExtent, liveState, conceptExtent]
  have hxFly : Creature.pingu ∈ activeExtent liveState Concept.fly := h hxBird
  simp [activeExtent, liveState, conceptExtent] at hxFly

theorem canary_extensional_hook_factors_through_extents :
    InheritanceQueryBuilder.extensionalEvidence
        (State := ToyState) (Atom := Concept) (Query := AtomQuery OntologyAtom)
        liveState pairEnc Concept.penguin Concept.penguin ≤
      InheritanceQueryBuilder.extensionalEvidence
        (State := ToyState) (Atom := Concept) (Query := AtomQuery OntologyAtom)
        liveState pairEnc Concept.penguin Concept.bird := by
  exact extensionalEvidenceSubsetRel_of_crispExtensionalInherits
    (State := ToyState) (Obj := Creature) (Con := Concept)
    (MemberSrt := PUnit) (PairQuery := AtomQuery OntologyAtom)
    (MemberQuery := fun _ : PUnit => AtomQuery OntologyAtom)
    factorization
    canary_penguin_extensionally_inherits_bird

end

end Mettapedia.Logic.ConceptOntology.AtomQueryCanary
