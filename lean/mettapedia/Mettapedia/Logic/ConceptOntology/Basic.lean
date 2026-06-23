import Mathlib.Order.GaloisConnection.Basic
import Mettapedia.Logic.SufficientStatisticSurface
import Mettapedia.Algebra.QuantaleWeakness

/-!
# Evidence-Valued Concept Ontology Core

This module isolates the core extensional-ontology data for WM-PLN:

- evidence-valued membership of objects in concepts
- additive extension from raw observations to membership evidence
- evidence-valued extent/intent adjunction in a commutative quantale

The observation layer is intentionally built as a thin specialization of the
existing `SufficientStatisticSurface` machinery, with query type `Obj × Con`.
-/

namespace Mettapedia.Logic.ConceptOntology

open Function OrderDual
open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelAdditive
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Algebra.QuantaleWeakness

universe u v w x

/-- A revisable state carries evidence-valued membership for object/concept
pairs, and that membership is additive under revision. -/
structure EvidenceMembershipContext
    (State : Type u) (Obj : Type v) (Con : Type w) (Ev : Type x)
    [EvidenceType State] [AddCommMonoid Ev] where
  memberEvidence : State → Obj → Con → Ev
  memberEvidence_add :
    ∀ W₁ W₂ x c,
      memberEvidence (W₁ + W₂) x c = memberEvidence W₁ x c + memberEvidence W₂ x c

namespace EvidenceMembershipContext

variable {State : Type u} {Obj : Type v} {Con : Type w} {Ev : Type x}
variable [EvidenceType State] [AddCommMonoid Ev]

theorem memberEvidence_add'
    (M : EvidenceMembershipContext State Obj Con Ev)
    (W₁ W₂ : State) (x : Obj) (c : Con) :
    M.memberEvidence (W₁ + W₂) x c = M.memberEvidence W₁ x c + M.memberEvidence W₂ x c :=
  M.memberEvidence_add W₁ W₂ x c

/-- Every evidence-valued membership context induces a generic additive world
model on the query type `Obj × Con`. -/
def toAdditiveWorldModel
    (M : EvidenceMembershipContext State Obj Con Ev) :
    AdditiveWorldModel State (Obj × Con) Ev where
  extract W q := M.memberEvidence W q.1 q.2
  extract_add W₁ W₂ q := M.memberEvidence_add W₁ W₂ q.1 q.2

end EvidenceMembershipContext

/-- Observation surfaces for ontology formation are just sufficient-statistic
surfaces whose queries are object/concept pairs. -/
abbrev ObservationSurface (Obs : Type u) (Obj : Type v) (Con : Type w) (Ev : Type x) :=
  SufficientStatisticSurface Obs (Obj × Con) Ev

namespace ObservationSurface

variable {Obs : Type u} {Obj : Type v} {Con : Type w} {Ev : Type x}

/-- Read the pair-indexed observation surface as object/concept membership
evidence. -/
def observeAt (S : ObservationSurface Obs Obj Con Ev) (o : Obs) (x : Obj) (c : Con) : Ev :=
  S.observe o (x, c)

section Additive

variable [AddCommMonoid Ev]

/-- Aggregate observation evidence into object/concept membership evidence. -/
noncomputable def aggregate
    (S : ObservationSurface Obs Obj Con Ev)
    (σ : Multiset Obs) (x : Obj) (c : Con) : Ev :=
  SufficientStatisticSurface.aggregate S σ (x, c)

@[simp] theorem aggregate_zero
    (S : ObservationSurface Obs Obj Con Ev) (x : Obj) (c : Con) :
    aggregate S 0 x c = 0 := by
  simp [aggregate]

@[simp] theorem aggregate_singleton
    (S : ObservationSurface Obs Obj Con Ev) (o : Obs) (x : Obj) (c : Con) :
    aggregate S ({o} : Multiset Obs) x c = observeAt S o x c := by
  simp [aggregate, observeAt]

theorem aggregate_add
    (S : ObservationSurface Obs Obj Con Ev)
    (σ₁ σ₂ : Multiset Obs) (x : Obj) (c : Con) :
    aggregate S (σ₁ + σ₂) x c = aggregate S σ₁ x c + aggregate S σ₂ x c := by
  simpa [aggregate] using SufficientStatisticSurface.aggregate_add S σ₁ σ₂ (x, c)

/-- The curried additive-extension property for ontology membership evidence. -/
def IsMembershipAdditiveExtension
    (observe : Obs → Obj → Con → Ev)
    (E : Multiset Obs → Obj → Con → Ev) : Prop :=
  GenIsAdditiveExtension
    (fun o : Obs => fun q : Obj × Con => observe o q.1 q.2)
    (fun σ q => E σ q.1 q.2)

theorem aggregate_isMembershipAdditiveExtension
    (S : ObservationSurface Obs Obj Con Ev) :
    IsMembershipAdditiveExtension (observeAt S) (aggregate S) := by
  exact S.aggregate_isAdditiveExtension

theorem aggregate_eq_of_isMembershipAdditiveExtension
    (S : ObservationSurface Obs Obj Con Ev)
    {E : Multiset Obs → Obj → Con → Ev}
    (hE : IsMembershipAdditiveExtension (observeAt S) E) :
    E = aggregate S := by
  have hEq :
      (fun (σ : Multiset Obs) (q : Obj × Con) => E σ q.1 q.2) =
        fun (σ : Multiset Obs) (q : Obj × Con) =>
          SufficientStatisticSurface.aggregate S σ q := by
    exact SufficientStatisticSurface.aggregate_eq_of_isAdditiveExtension S hE
  funext σ x c
  exact congrFun (congrFun hEq σ) (x, c)

/-- The canonical multiset-based evidence membership context induced by an
observation surface. -/
noncomputable def inducedContext
    (S : ObservationSurface Obs Obj Con Ev) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    EvidenceMembershipContext (Multiset Obs) Obj Con Ev := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  exact
    { memberEvidence := aggregate S
      memberEvidence_add := aggregate_add S }

@[simp] theorem inducedContext_memberEvidence_eq_aggregate
    (S : ObservationSurface Obs Obj Con Ev)
    (σ : Multiset Obs) (x : Obj) (c : Con) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    (S.inducedContext).memberEvidence σ x c = aggregate S σ x c := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  rfl

end Additive

end ObservationSurface

/-- Evidence-valued predicates used for extents and intents. -/
abbrev Predicate (α : Type*) (Q : Type*) := α → Q

section Quantale

variable {Obj : Type u} {Con : Type v} {Q : Type w}
variable [CommSemigroup Q] [CompleteLattice Q] [IsQuantale Q]

/-- The evidence-valued upper operator induced by an object/concept membership
relation. -/
noncomputable def upperAdjoint
    (M : Obj → Con → Q) (extent : Predicate Obj Q) : Predicate Con Q :=
  fun c => ⨅ x, quantaleImplies (extent x) (M x c)

/-- The evidence-valued lower operator induced by an object/concept membership
relation. -/
noncomputable def lowerAdjoint
    (M : Obj → Con → Q) (intent : Predicate Con Q) : Predicate Obj Q :=
  fun x => ⨅ c, quantaleImplies (intent c) (M x c)

theorem le_upperAdjoint_iff_le_lowerAdjoint
    (M : Obj → Con → Q) (extent : Predicate Obj Q) (intent : Predicate Con Q) :
    intent ≤ upperAdjoint M extent ↔ extent ≤ lowerAdjoint M intent := by
  constructor
  · intro h x
    apply le_iInf
    intro c
    have hUpper : intent c ≤ upperAdjoint M extent c := h c
    have h₁ : intent c ≤ quantaleImplies (extent x) (M x c) := by
      exact le_trans hUpper (by
        simpa [upperAdjoint] using
          (iInf_le (fun y => quantaleImplies (extent y) (M y c)) x))
    have h₂ : intent c * extent x ≤ M x c :=
      (quantaleImplies_adjunction (x := extent x) (y := M x c) (z := intent c)).2 h₁
    have h₃ : extent x * intent c ≤ M x c := by
      simpa [mul_comm] using h₂
    exact (quantaleImplies_adjunction (x := intent c) (y := M x c) (z := extent x)).1 h₃
  · intro h c
    apply le_iInf
    intro x
    have hLower : extent x ≤ lowerAdjoint M intent x := h x
    have h₁ : extent x ≤ quantaleImplies (intent c) (M x c) := by
      exact le_trans hLower (by
        simpa [lowerAdjoint] using
          (iInf_le (fun d => quantaleImplies (intent d) (M x d)) c))
    have h₂ : extent x * intent c ≤ M x c :=
      (quantaleImplies_adjunction (x := intent c) (y := M x c) (z := extent x)).2 h₁
    have h₃ : intent c * extent x ≤ M x c := by
      simpa [mul_comm] using h₂
    exact (quantaleImplies_adjunction (x := extent x) (y := M x c) (z := intent c)).1 h₃

theorem gc_upperAdjoint_lowerAdjoint
    (M : Obj → Con → Q) :
    GaloisConnection (toDual ∘ upperAdjoint M) (lowerAdjoint M ∘ ofDual) := by
  intro extent intent
  exact le_upperAdjoint_iff_le_lowerAdjoint M extent intent

/-- Evidence-valued concepts are fixed points of the extent/intent adjunction. -/
structure EvidenceConcept (M : Obj → Con → Q) where
  extent : Predicate Obj Q
  intent : Predicate Con Q
  upper_extent : upperAdjoint M extent = intent
  lower_intent : lowerAdjoint M intent = extent

namespace EvidenceConcept

variable {M : Obj → Con → Q}

/-- Extensional inheritance between evidence concepts is pointwise extent
inclusion. -/
def ExtensionalInherits (A B : EvidenceConcept M) : Prop :=
  A.extent ≤ B.extent

omit [IsQuantale Q] in
theorem extensionalInherits_refl (A : EvidenceConcept M) :
    ExtensionalInherits A A :=
  fun _ => le_rfl

omit [IsQuantale Q] in
theorem extensionalInherits_trans {A B C : EvidenceConcept M}
    (hAB : ExtensionalInherits A B) (hBC : ExtensionalInherits B C) :
    ExtensionalInherits A C :=
  fun x => le_trans (hAB x) (hBC x)

end EvidenceConcept

end Quantale

end Mettapedia.Logic.ConceptOntology
