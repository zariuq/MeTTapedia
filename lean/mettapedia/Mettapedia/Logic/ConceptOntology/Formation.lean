import Mathlib.Data.SetLike.Fintype
import Mettapedia.Logic.AbstractInheritance

/-!
# Finite Concept-Family Formation

This module adds the first public finite concept-family surface on top of the
existing ontology foundations:

- all closed dual concepts for a crisp relation
- the gated finite concept family induced by evidence-valued membership
- thin wrappers for world-state contexts and aggregated observations
-/

namespace Mettapedia.Logic.AbstractInheritance

open Mettapedia.Logic.ConceptOntology

universe u v w x

namespace DualConcept

variable {Obj : Type u} {Attr : Type v}

/-- A dual concept is exactly a pair of extent and intent sets. -/
def equivSetProd : DualConcept Obj Attr ≃ Set Obj × Set Attr where
  toFun A := (A.extent, A.intent)
  invFun p := { extent := p.1, intent := p.2 }
  left_inv A := by
    cases A
    rfl
  right_inv p := by
    cases p
    rfl

/-- Finite object and attribute carriers induce a finite dual-concept carrier. -/
noncomputable instance [Fintype Obj] [Fintype Attr] : Fintype (DualConcept Obj Attr) :=
  Fintype.ofEquiv (Set Obj × Set Attr) equivSetProd.symm

end DualConcept

section FiniteFamilies

variable {Obj : Type u} {Attr : Type v} {Q : Type w}
variable [Fintype Obj] [Fintype Attr]

/-- The finite family of all closed dual concepts for a crisp relation. -/
noncomputable def finiteClosedConceptFamily
    (r : Obj → Attr → Prop) : Finset (DualConcept Obj Attr) := by
  classical
  exact Finset.univ.filter (fun A => DualConcept.IsClosed r A)

@[simp] theorem mem_finiteClosedConceptFamily_iff
    (r : Obj → Attr → Prop) (A : DualConcept Obj Attr) :
    A ∈ finiteClosedConceptFamily r ↔ DualConcept.IsClosed r A := by
  classical
  simp [finiteClosedConceptFamily]

section Crisp

variable [Preorder Q]

/-- The finite family of closed concepts induced by a gated evidence-valued
membership relation. -/
noncomputable def finiteConceptFamily
    (G : EvidenceGate Q) (M : Obj → Attr → Q) : Finset (DualConcept Obj Attr) :=
  finiteClosedConceptFamily (crispRelation G M)

@[simp] theorem mem_finiteConceptFamily_iff
    (G : EvidenceGate Q) (M : Obj → Attr → Q) (A : DualConcept Obj Attr) :
    A ∈ finiteConceptFamily G M ↔
      DualConcept.IsClosed (crispRelation G M) A := by
  simp [finiteConceptFamily, finiteClosedConceptFamily]

@[simp] theorem not_mem_finiteConceptFamily_iff
    (G : EvidenceGate Q) (M : Obj → Attr → Q) (A : DualConcept Obj Attr) :
    A ∉ finiteConceptFamily G M ↔
      ¬ DualConcept.IsClosed (crispRelation G M) A := by
  simp [mem_finiteConceptFamily_iff]

/-- The carrier of formed concepts for a gated evidence-valued relation. -/
abbrev FormedConcept
    (G : EvidenceGate Q) (M : Obj → Attr → Q) :=
  { A : DualConcept Obj Attr // A ∈ finiteConceptFamily G M }

/-- Every gated base concept is a member of the finite formed concept family,
because it is already closed by construction. -/
theorem ofCrispBaseConcept_mem_finiteConceptFamily
    (G : EvidenceGate Q) (M : Obj → Attr → Q) (c : Attr) :
    ofCrispBaseConcept G M c ∈ finiteConceptFamily G M := by
  rw [mem_finiteConceptFamily_iff]
  exact DualConcept.isClosed_ofConcept (crispBaseConcept G M c)

/-- Formed concepts inherit a canonical abstract interpretation by forgetting
their membership proof. -/
noncomputable def formedConceptInterpretation
    (G : EvidenceGate Q) (M : Obj → Attr → Q) :
    Interpretation (FormedConcept G M) Obj Attr where
  meaning := fun A => A.1

@[simp] theorem formedConceptInterpretation_meaning
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A : FormedConcept G M) :
    (formedConceptInterpretation G M).meaning A = A.1 := rfl

@[simp] theorem formedConcept_isClosed
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A : FormedConcept G M) :
    DualConcept.IsClosed (crispRelation G M) A.1 :=
  (mem_finiteConceptFamily_iff G M A.1).mp A.2

end Crisp
end FiniteFamilies
end Mettapedia.Logic.AbstractInheritance

namespace Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext

open Mettapedia.Logic.AbstractInheritance

universe u v w x

variable {State : Type u} {Obj : Type v} {Con : Type w} {Q : Type x}
variable [Mettapedia.Logic.EvidenceClass.EvidenceType State] [AddCommMonoid Q] [Preorder Q]
variable [Fintype Obj] [Fintype Con]

/-- The carrier of formed concepts at a fixed state and gate. -/
abbrev FormedConceptAt
    (M : EvidenceMembershipContext State Obj Con Q)
    (G : EvidenceGate Q) (W : State) :=
  AbstractInheritance.FormedConcept G (M.memberEvidence W)

/-- Finite concept family formed from the membership evidence carried by a
fixed world/model state. -/
noncomputable def finiteConceptFamilyAt
    (M : EvidenceMembershipContext State Obj Con Q)
    (G : EvidenceGate Q) (W : State) :
    Finset (AbstractInheritance.DualConcept Obj Con) :=
  AbstractInheritance.finiteConceptFamily G (M.memberEvidence W)

@[simp] theorem mem_finiteConceptFamilyAt_iff
    (M : EvidenceMembershipContext State Obj Con Q)
    (G : EvidenceGate Q) (W : State)
    (A : AbstractInheritance.DualConcept Obj Con) :
    A ∈ finiteConceptFamilyAt M G W ↔
      AbstractInheritance.DualConcept.IsClosed
        (crispRelation G (M.memberEvidence W)) A := by
  rw [finiteConceptFamilyAt]
  exact AbstractInheritance.mem_finiteConceptFamily_iff
    (Obj := Obj) (Attr := Con) (Q := Q) G (M.memberEvidence W) A

@[simp] theorem not_mem_finiteConceptFamilyAt_iff
    (M : EvidenceMembershipContext State Obj Con Q)
    (G : EvidenceGate Q) (W : State)
    (A : AbstractInheritance.DualConcept Obj Con) :
    A ∉ finiteConceptFamilyAt M G W ↔
      ¬ AbstractInheritance.DualConcept.IsClosed
        (crispRelation G (M.memberEvidence W)) A := by
  simp [mem_finiteConceptFamilyAt_iff]

/-- Canonical interpretation of formed concepts at a fixed state. -/
noncomputable def formedConceptInterpretationAt
    (M : EvidenceMembershipContext State Obj Con Q)
    (G : EvidenceGate Q) (W : State) :
    AbstractInheritance.Interpretation (FormedConceptAt M G W) Obj Con :=
  AbstractInheritance.formedConceptInterpretation G (M.memberEvidence W)

@[simp] theorem formedConceptInterpretationAt_meaning
    (M : EvidenceMembershipContext State Obj Con Q)
    (G : EvidenceGate Q) (W : State)
    (A : FormedConceptAt M G W) :
    (formedConceptInterpretationAt M G W).meaning A = A.1 := rfl

end Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext

namespace Mettapedia.Logic.ConceptOntology.ObservationSurface

open Mettapedia.Logic.AbstractInheritance

universe u v w x

variable {Obs : Type u} {Obj : Type v} {Con : Type w} {Q : Type x}
variable [AddCommMonoid Q] [Preorder Q] [Fintype Obj] [Fintype Con]

/-- The carrier of formed concepts induced by aggregated observation evidence. -/
abbrev FormedConcept
    (S : ObservationSurface Obs Obj Con Q)
    (G : EvidenceGate Q) (σ : Multiset Obs) :=
  AbstractInheritance.FormedConcept G (aggregate S σ)

/-- Finite concept family formed from aggregated observation evidence under a
gate. -/
noncomputable def finiteConceptFamily
    (S : ObservationSurface Obs Obj Con Q)
    (G : EvidenceGate Q) (σ : Multiset Obs) :
    Finset (AbstractInheritance.DualConcept Obj Con) :=
  AbstractInheritance.finiteConceptFamily G (aggregate S σ)

@[simp] theorem mem_finiteConceptFamily_iff
    (S : ObservationSurface Obs Obj Con Q)
    (G : EvidenceGate Q) (σ : Multiset Obs)
    (A : AbstractInheritance.DualConcept Obj Con) :
    A ∈ finiteConceptFamily S G σ ↔
      AbstractInheritance.DualConcept.IsClosed
        (crispRelation G (aggregate S σ)) A := by
  rw [finiteConceptFamily]
  exact AbstractInheritance.mem_finiteConceptFamily_iff
    (Obj := Obj) (Attr := Con) (Q := Q) G (aggregate S σ) A

@[simp] theorem not_mem_finiteConceptFamily_iff
    (S : ObservationSurface Obs Obj Con Q)
    (G : EvidenceGate Q) (σ : Multiset Obs)
    (A : AbstractInheritance.DualConcept Obj Con) :
    A ∉ finiteConceptFamily S G σ ↔
      ¬ AbstractInheritance.DualConcept.IsClosed
        (crispRelation G (aggregate S σ)) A := by
  simp [mem_finiteConceptFamily_iff]

/-- Canonical interpretation of formed concepts induced by aggregated
observations. -/
noncomputable def formedConceptInterpretation
    (S : ObservationSurface Obs Obj Con Q)
    (G : EvidenceGate Q) (σ : Multiset Obs) :
    AbstractInheritance.Interpretation (FormedConcept S G σ) Obj Con :=
  AbstractInheritance.formedConceptInterpretation G (aggregate S σ)

@[simp] theorem formedConceptInterpretation_meaning
    (S : ObservationSurface Obs Obj Con Q)
    (G : EvidenceGate Q) (σ : Multiset Obs)
    (A : FormedConcept S G σ) :
    (formedConceptInterpretation S G σ).meaning A = A.1 := rfl

end Mettapedia.Logic.ConceptOntology.ObservationSurface
