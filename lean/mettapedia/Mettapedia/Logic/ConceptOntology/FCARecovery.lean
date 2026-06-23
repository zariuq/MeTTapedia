import Mettapedia.Logic.ConceptOntology.Formation

/-!
# FCA Recovery for Exact Concept Formation

This module makes explicit that the exact finite concept-formation surface is
not a parallel notion beside classical FCA: it is equivalent to mathlib's
formal-concept carrier for the same gated incidence relation.

That equivalence is the main conceptual reason the classical FCA algorithms and
order-theoretic results remain the right exact baseline for our theory.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic.AbstractInheritance

universe u v w

section ExactRecovery

variable {Obj : Type u} {Attr : Type v} {Q : Type w}
variable [Fintype Obj] [Fintype Attr] [Preorder Q]

/-- Exact formed concepts are equivalent to the classical formal concepts of
the same gated incidence relation. -/
noncomputable def formedConceptEquivCrispConcept
    (G : EvidenceGate Q) (M : Obj → Attr → Q) :
    AbstractInheritance.FormedConcept G M ≃ CrispConcept G M where
  toFun A :=
    DualConcept.toConcept A.1 (AbstractInheritance.formedConcept_isClosed G M A)
  invFun c :=
    ⟨DualConcept.ofConcept c,
      (AbstractInheritance.mem_finiteConceptFamily_iff G M _).2
        (DualConcept.isClosed_ofConcept c)⟩
  left_inv A := by
    apply Subtype.ext
    exact DualConcept.ofConcept_toConcept A.1
      (AbstractInheritance.formedConcept_isClosed G M A)
  right_inv c := by
    exact DualConcept.toConcept_ofConcept c

/-- The exact formed-concept order is the standard FCA concept-lattice order. -/
noncomputable def formedConceptOrderIsoCrispConcept
    (G : EvidenceGate Q) (M : Obj → Attr → Q) :
    AbstractInheritance.FormedConcept G M ≃o CrispConcept G M where
  toEquiv := formedConceptEquivCrispConcept G M
  map_rel_iff' := by
    intro A B
    exact
      (DualConcept.toConcept_le_iff A.1 B.1
        (AbstractInheritance.formedConcept_isClosed G M A)
        (AbstractInheritance.formedConcept_isClosed G M B))

@[simp] theorem formedConceptOrderIsoCrispConcept_apply
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.FormedConcept G M) :
    formedConceptOrderIsoCrispConcept G M A =
      DualConcept.toConcept A.1 (AbstractInheritance.formedConcept_isClosed G M A) :=
  rfl

/-- Exact formation does not merely resemble FCA: it preserves the full concept
order exactly. -/
theorem formedConcept_inherits_iff_crispConcept_le
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A B : AbstractInheritance.FormedConcept G M) :
    A ≤ B ↔
      formedConceptOrderIsoCrispConcept G M A ≤
        formedConceptOrderIsoCrispConcept G M B := by
  simpa using (formedConceptOrderIsoCrispConcept G M).map_rel_iff.symm

end ExactRecovery

end Mettapedia.Logic.ConceptOntology
