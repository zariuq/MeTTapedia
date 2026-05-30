import Mettapedia.Logic.ConceptOntology.FCA

/-!
# Distinction-Preserving Representation Layer

This module records the basic invariance facts needed for a
Goertzel-style weak representation story: once ontology is derived from the
membership relation, observationally indistinguishable objects/concepts remain
indistinguishable for the derived crisp ontology.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Algebra.QuantaleWeakness

universe u v w

section Distinction

variable {Obj : Type u} {Con : Type v} {Q : Type w}

/-- Objects are indistinguishable when they have the same membership-evidence
profile across all concepts. -/
def ObjectIndistinguishable (M : Obj → Con → Q) (x y : Obj) : Prop :=
  ∀ c, M x c = M y c

/-- Concepts are indistinguishable when they present the same membership
evidence across all objects. -/
def ConceptIndistinguishable (M : Obj → Con → Q) (c d : Con) : Prop :=
  ∀ x, M x c = M x d

def objectSetoid (M : Obj → Con → Q) : Setoid Obj where
  r := ObjectIndistinguishable M
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x c
      rfl
    · intro x y hxy c
      exact (hxy c).symm
    · intro x y z hxy hyz c
      exact (hxy c).trans (hyz c)

def conceptSetoid (M : Obj → Con → Q) : Setoid Con where
  r := ConceptIndistinguishable M
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro c x
      rfl
    · intro c d hcd x
      exact (hcd x).symm
    · intro c d e hcd hde x
      exact (hcd x).trans (hde x)

end Distinction

section QuotientFactorization

variable {Obj : Type u} {Con : Type v} {Q : Type w}

/-- Membership evidence factors through the quotient by object and concept
indistinguishability. -/
noncomputable def factoredMemberEvidence
    (M : Obj → Con → Q) :
    Quotient (objectSetoid M) → Quotient (conceptSetoid M) → Q :=
  Quotient.lift₂ M <| by
    intro x c y d hxy hcd
    calc
      M x c = M y c := hxy c
      _ = M y d := hcd y

@[simp] theorem factoredMemberEvidence_mk
    (M : Obj → Con → Q) (x : Obj) (c : Con) :
    factoredMemberEvidence M ⟦x⟧ ⟦c⟧ = M x c := rfl

end QuotientFactorization

section PredicateFactorization

variable {Obj : Type u} {Con : Type v} {Q : Type w}

/-- An object-indexed predicate respects the indistinguishability classes induced
by the membership relation. -/
def ObjectPredicateInvariant (M : Obj → Con → Q) (E : Obj → Q) : Prop :=
  ∀ ⦃x y : Obj⦄, ObjectIndistinguishable M x y → E x = E y

/-- A concept-indexed predicate respects the indistinguishability classes induced
by the membership relation. -/
def ConceptPredicateInvariant (M : Obj → Con → Q) (I : Con → Q) : Prop :=
  ∀ ⦃c d : Con⦄, ConceptIndistinguishable M c d → I c = I d

/-- Invariant object-predicates factor through the object quotient. -/
noncomputable def factoredObjectPredicate
    (M : Obj → Con → Q) (E : Obj → Q) (hE : ObjectPredicateInvariant M E) :
    Quotient (objectSetoid M) → Q :=
  Quotient.lift E <| by
    intro x y hxy
    exact hE hxy

/-- Invariant concept-predicates factor through the concept quotient. -/
noncomputable def factoredConceptPredicate
    (M : Obj → Con → Q) (I : Con → Q) (hI : ConceptPredicateInvariant M I) :
    Quotient (conceptSetoid M) → Q :=
  Quotient.lift I <| by
    intro c d hcd
    exact hI hcd

@[simp] theorem factoredObjectPredicate_mk
    (M : Obj → Con → Q) (E : Obj → Q) (hE : ObjectPredicateInvariant M E) (x : Obj) :
    factoredObjectPredicate M E hE ⟦x⟧ = E x := rfl

@[simp] theorem factoredConceptPredicate_mk
    (M : Obj → Con → Q) (I : Con → Q) (hI : ConceptPredicateInvariant M I) (c : Con) :
    factoredConceptPredicate M I hI ⟦c⟧ = I c := rfl

end PredicateFactorization

section QuantaleFactorization

variable {Obj : Type u} {Con : Type v} {Q : Type w}
variable [CommSemigroup Q] [CompleteLattice Q] [IsQuantale Q]

omit [IsQuantale Q] in
theorem upperAdjoint_factored_mk
    (M : Obj → Con → Q)
    (extent : Obj → Q) (hExtent : ObjectPredicateInvariant M extent)
    (c : Con) :
    upperAdjoint (factoredMemberEvidence M)
        (factoredObjectPredicate M extent hExtent) ⟦c⟧ =
      upperAdjoint M extent c := by
  apply le_antisymm
  · apply le_iInf
    intro x
    simpa [upperAdjoint, factoredMemberEvidence, factoredObjectPredicate] using
      (iInf_le
        (fun qx =>
          quantaleImplies
            (factoredObjectPredicate M extent hExtent qx)
            (factoredMemberEvidence M qx ⟦c⟧))
        ⟦x⟧)
  · apply le_iInf
    intro qx
    refine Quotient.inductionOn qx ?_
    intro x
    simpa [upperAdjoint, factoredMemberEvidence, factoredObjectPredicate] using
      (iInf_le (fun y => quantaleImplies (extent y) (M y c)) x)

omit [IsQuantale Q] in
theorem lowerAdjoint_factored_mk
    (M : Obj → Con → Q)
    (intent : Con → Q) (hIntent : ConceptPredicateInvariant M intent)
    (x : Obj) :
    lowerAdjoint (factoredMemberEvidence M)
        (factoredConceptPredicate M intent hIntent) ⟦x⟧ =
      lowerAdjoint M intent x := by
  apply le_antisymm
  · apply le_iInf
    intro c
    simpa [lowerAdjoint, factoredMemberEvidence, factoredConceptPredicate] using
      (iInf_le
        (fun qc =>
          quantaleImplies
            (factoredConceptPredicate M intent hIntent qc)
            (factoredMemberEvidence M ⟦x⟧ qc))
        ⟦c⟧)
  · apply le_iInf
    intro qx
    refine Quotient.inductionOn qx ?_
    intro c
    simpa [lowerAdjoint, factoredMemberEvidence, factoredConceptPredicate] using
      (iInf_le (fun d => quantaleImplies (intent d) (M x d)) c)

noncomputable def EvidenceConcept.factor
    (M : Obj → Con → Q)
    (A : EvidenceConcept M)
    (hExtent : ObjectPredicateInvariant M A.extent)
    (hIntent : ConceptPredicateInvariant M A.intent) :
    EvidenceConcept (factoredMemberEvidence M) where
  extent := factoredObjectPredicate M A.extent hExtent
  intent := factoredConceptPredicate M A.intent hIntent
  upper_extent := by
    ext qc
    refine Quotient.inductionOn qc ?_
    intro c
    simpa [upperAdjoint_factored_mk, hExtent] using congrFun A.upper_extent c
  lower_intent := by
    ext qx
    refine Quotient.inductionOn qx ?_
    intro x
    simpa [lowerAdjoint_factored_mk, hIntent] using congrFun A.lower_intent x

omit [IsQuantale Q] in
@[simp] theorem EvidenceConcept_factor_extent_mk
    (M : Obj → Con → Q)
    (A : EvidenceConcept M)
    (hExtent : ObjectPredicateInvariant M A.extent)
    (hIntent : ConceptPredicateInvariant M A.intent)
    (x : Obj) :
    (A.factor M hExtent hIntent).extent ⟦x⟧ = A.extent x := by
  rfl

omit [IsQuantale Q] in
@[simp] theorem EvidenceConcept_factor_intent_mk
    (M : Obj → Con → Q)
    (A : EvidenceConcept M)
    (hExtent : ObjectPredicateInvariant M A.extent)
    (hIntent : ConceptPredicateInvariant M A.intent)
    (c : Con) :
    (A.factor M hExtent hIntent).intent ⟦c⟧ = A.intent c := by
  rfl

end QuantaleFactorization

section CrispInvariance

variable {Obj : Type u} {Con : Type v} {Q : Type w} [Preorder Q]
variable (G : EvidenceGate Q) (M : Obj → Con → Q)

theorem crispRelation_congr_left
    {x y : Obj} (hxy : ObjectIndistinguishable M x y) (c : Con) :
    crispRelation G M x c ↔ crispRelation G M y c := by
  simp [crispRelation, hxy c]

theorem crispRelation_congr_right
    {c d : Con} (hcd : ConceptIndistinguishable M c d) (x : Obj) :
    crispRelation G M x c ↔ crispRelation G M x d := by
  simp [crispRelation, hcd x]

theorem crispExtent_eq_of_conceptIndistinguishable
    {c d : Con} (hcd : ConceptIndistinguishable M c d) :
    crispExtent G M c = crispExtent G M d := by
  ext x
  simp [mem_crispExtent_iff, hcd x]

theorem crispIntent_eq_of_objectIndistinguishable
    {x y : Obj} (hxy : ObjectIndistinguishable M x y) :
    crispIntent G M x = crispIntent G M y := by
  ext c
  simp [mem_crispIntent_iff, hxy c]

theorem crispExtensionalInherits_congr_left
    {c c' d : Con} (hcc' : ConceptIndistinguishable M c c') :
    crispExtensionalInherits G M c d ↔ crispExtensionalInherits G M c' d := by
  simp [crispExtensionalInherits, crispExtent_eq_of_conceptIndistinguishable (G := G) (M := M) hcc']

theorem crispExtensionalInherits_congr_right
    {c d d' : Con} (hdd' : ConceptIndistinguishable M d d') :
    crispExtensionalInherits G M c d ↔ crispExtensionalInherits G M c d' := by
  simp [crispExtensionalInherits, crispExtent_eq_of_conceptIndistinguishable (G := G) (M := M) hdd']

theorem crispExtensionalInherits_congr
    {c c' d d' : Con}
    (hcc' : ConceptIndistinguishable M c c')
    (hdd' : ConceptIndistinguishable M d d') :
    crispExtensionalInherits G M c d ↔ crispExtensionalInherits G M c' d' := by
  rw [crispExtensionalInherits_congr_left (G := G) (M := M) hcc']
  rw [crispExtensionalInherits_congr_right (G := G) (M := M) hdd']

theorem factoredCrispRelation_mk
    (x : Obj) (c : Con) :
    crispRelation G (factoredMemberEvidence M) ⟦x⟧ ⟦c⟧ ↔ crispRelation G M x c := by
  simp [crispRelation, factoredMemberEvidence]

theorem factoredCrispExtensionalInherits_mk_iff
    (c d : Con) :
    crispExtensionalInherits G (factoredMemberEvidence M) ⟦c⟧ ⟦d⟧
      ↔ crispExtensionalInherits G M c d := by
  rw [crispExtensionalInherits_iff, crispExtensionalInherits_iff]
  constructor
  · intro h x hx
    have hx' : crispRelation G (factoredMemberEvidence M) ⟦x⟧ ⟦c⟧ := by
      simpa [crispRelation, factoredMemberEvidence] using hx
    have hd' : crispRelation G (factoredMemberEvidence M) ⟦x⟧ ⟦d⟧ := h ⟦x⟧ hx'
    simpa [crispRelation, factoredMemberEvidence] using hd'
  · intro h qx
    refine Quotient.inductionOn qx ?_
    intro x hx
    have hx' : crispRelation G M x c := by
      simpa [crispRelation, factoredMemberEvidence] using hx
    have hd' : crispRelation G M x d := h x hx'
    simpa [crispRelation, factoredMemberEvidence] using hd'

end CrispInvariance

end Mettapedia.Logic.ConceptOntology
