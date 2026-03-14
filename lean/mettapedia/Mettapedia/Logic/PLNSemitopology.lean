import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import Mettapedia.Logic.PLNWorldModelOverlap
import Mettapedia.Logic.PLNWorldModelSupportForgetting

/-!
# WM Semitopology

Minimal semitopology / coalition layer for non-additive WM reasoning.

- actionable sets model workable coalitions/quorums;
- arbitrary unions are preserved, but finite intersections need not be;
- local consensus is constancy on an actionable coalition around a point;
- conflict is witnessed by any actionable coalition around a point containing
  incompatible values.

This module is intentionally lightweight and extends the existing overlap and
support-tracked forgetting perimeter rather than replacing the additive core.
-/

namespace Mettapedia.Logic

open scoped ENNReal

/-! ## Semitopology Core -/

/-- A semitopology keeps the topology-style empty/universe/union laws but does
not assume finite-intersection closure. Actionable sets are read as coalitions
or quorums that can jointly accomplish some task. -/
structure Semitopology (α : Type*) where
  actionable : Set α → Prop
  actionable_empty : actionable ∅
  actionable_univ : actionable Set.univ
  actionable_union :
    ∀ U V : Set α, actionable U → actionable V → actionable (U ∪ V)

/-- Special case of semitopology where actionable sets are also closed under
finite intersections. This is the topology-like coalition regime. -/
structure CoalitionTopology (α : Type*) extends Semitopology α where
  actionable_inter :
    ∀ U V : Set α, actionable U → actionable V → actionable (U ∩ V)

namespace Semitopology

variable {α β State Scope Query Ev Ov Supp : Type*}

/-- `U` is an actionable neighborhood of `p`. -/
def Neighborhood (T : Semitopology α) (p : α) (U : Set α) : Prop :=
  p ∈ U ∧ T.actionable U

/-- `f` is locally consensus-preserving at `p` when some actionable coalition
around `p` forces a unique value. -/
def LocallyConsensusAt (T : Semitopology α) (f : α → β) (p : α) : Prop :=
  ∃ U : Set α, p ∈ U ∧ T.actionable U ∧ ∀ x ∈ U, f x = f p

/-- `f` is constant on coalition `U`. -/
def ConstantOn (U : Set α) (f : α → β) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ U → y ∈ U → f x = f y

theorem local_consensus_of_constant_on_actionable
    (T : Semitopology α)
    {f : α → β} {p : α} {U : Set α}
    (hp : p ∈ U) (hU : T.actionable U)
    (hconst : ConstantOn U f) :
    T.LocallyConsensusAt f p := by
  refine ⟨U, hp, hU, ?_⟩
  intro x hx
  exact hconst hx hp

theorem global_consensus_of_constant
    (T : Semitopology α)
    {f : α → β}
    (hconst : ∀ x y : α, f x = f y) :
    ∀ p : α, T.LocallyConsensusAt f p := by
  intro p
  refine ⟨Set.univ, by simp, T.actionable_univ, ?_⟩
  intro x _
  exact hconst x p

theorem discontinuity_of_conflicting_actionable_values
    (T : Semitopology α)
    {f : α → β} {p : α}
    (hconflict :
      ∀ U : Set α, p ∈ U → T.actionable U →
        ∃ x ∈ U, ∃ y ∈ U, f x ≠ f y) :
    ¬ T.LocallyConsensusAt f p := by
  intro hloc
  rcases hloc with ⟨U, hp, hU, hlocU⟩
  rcases hconflict U hp hU with ⟨x, hx, y, hy, hxy⟩
  have hx' : f x = f p := hlocU x hx
  have hy' : f y = f p := hlocU y hy
  exact hxy (hx'.trans hy'.symm)

/-- Turn a semitopology into the topology-like special case once finite
intersection closure is supplied. -/
def coalitionTopologyOfIntersectionClosed
    (T : Semitopology α)
    (hinter :
      ∀ U V : Set α, T.actionable U → T.actionable V → T.actionable (U ∩ V)) :
    CoalitionTopology α where
  actionable := T.actionable
  actionable_empty := T.actionable_empty
  actionable_univ := T.actionable_univ
  actionable_union := T.actionable_union
  actionable_inter := hinter

theorem topological_of_intersection_closed
    (T : Semitopology α)
    (hinter :
      ∀ U V : Set α, T.actionable U → T.actionable V → T.actionable (U ∩ V)) :
    (coalitionTopologyOfIntersectionClosed T hinter).toSemitopology = T := by
  cases T
  rfl

/-! ## Positive / Negative Examples -/

/-- Topology-like indiscrete semitopology: only `∅` and `univ` are actionable. -/
def indiscreteSemitopology (α : Type*) : Semitopology α where
  actionable U := U = ∅ ∨ U = Set.univ
  actionable_empty := Or.inl rfl
  actionable_univ := Or.inr rfl
  actionable_union := by
    intro U V hU hV
    rcases hU with rfl | rfl <;> rcases hV with rfl | rfl <;> simp

theorem indiscrete_intersection_closed (α : Type*) :
    ∀ U V : Set α,
      (indiscreteSemitopology α).actionable U →
      (indiscreteSemitopology α).actionable V →
      (indiscreteSemitopology α).actionable (U ∩ V) := by
  intro U V hU hV
  rcases hU with rfl | rfl <;> rcases hV with rfl | rfl <;> simp [indiscreteSemitopology]

/-- A quorum-style semitopology with two workable coalitions whose overlap is
not itself actionable. -/
def coalition01 : Set (Fin 3) := {i | i = 0 ∨ i = 1}

/-- Second actionable coalition in the quorum example. -/
def coalition02 : Set (Fin 3) := {i | i = 0 ∨ i = 2}

/-- Quorum semitopology: any set containing `coalition01` or `coalition02` is
actionable. The overlap `{0}` is not actionable. -/
def quorumSemitopology : Semitopology (Fin 3) where
  actionable U := U = ∅ ∨ coalition01 ⊆ U ∨ coalition02 ⊆ U
  actionable_empty := Or.inl rfl
  actionable_univ := Or.inr <| Or.inl <| by intro x hx; simp
  actionable_union := by
    intro U V hU hV
    rcases hU with rfl | hU | hU
    · simpa using hV
    · exact Or.inr <| Or.inl <| by
        intro x hx
        exact Or.inl (hU hx)
    · exact Or.inr <| Or.inr <| by
        intro x hx
        exact Or.inl (hU hx)

theorem quorumSemitopology_actionable_coalition01 :
    quorumSemitopology.actionable coalition01 := by
  exact Or.inr <| Or.inl <| Set.Subset.rfl

theorem quorumSemitopology_actionable_coalition02 :
    quorumSemitopology.actionable coalition02 := by
  exact Or.inr <| Or.inr <| Set.Subset.rfl

theorem quorumSemitopology_not_actionable_singleton_zero :
    ¬ quorumSemitopology.actionable ({0} : Set (Fin 3)) := by
  intro h
  rcases h with h | h | h
  · have : (0 : Fin 3) ∈ ({0} : Set (Fin 3)) := by simp
    simp [h] at this
  · have h1 : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := h (by simp [coalition01])
    simp at h1
  · have h2 : (2 : Fin 3) ∈ ({0} : Set (Fin 3)) := h (by simp [coalition02])
    simp at h2

theorem quorumSemitopology_intersection_not_actionable :
    ¬ quorumSemitopology.actionable (coalition01 ∩ coalition02) := by
  have hEq : coalition01 ∩ coalition02 = ({0} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> simp [coalition01, coalition02]
  rw [hEq]
  exact quorumSemitopology_not_actionable_singleton_zero

/-! ## Bridge to Overlap Layer -/

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric

variable [EvidenceType State] [AddCommMonoid Ev] [GenericWorldModel State Query Ev]

/-- Semitopology-driven independence: both supports are actionable and
pairwise disjoint at the query in question. -/
def SemitopologyIndependent
    (T : Semitopology α)
    (support : State → Query → Set α)
    (W₁ W₂ : State) (q : Query) : Prop :=
  T.actionable (support W₁ q) ∧
  T.actionable (support W₂ q) ∧
  Disjoint (support W₁ q) (support W₂ q)

theorem additive_of_semitopologyIndependent
    (T : Semitopology α)
    (L : OverlapLayer State Query Ev Ov)
    (support : State → Query → Set α)
    (hind :
      ∀ {W₁ W₂ : State} {q : Query},
        SemitopologyIndependent T support W₁ W₂ q →
        L.independent W₁ W₂ q)
    {W₁ W₂ : State} {q : Query}
    (hsemi : SemitopologyIndependent T support W₁ W₂ q) :
    GenericWorldModel.evidence
      (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q =
    GenericWorldModel.evidence
      (State := State) (Query := Query) (Ev := Ev) W₁ q +
    GenericWorldModel.evidence
      (State := State) (Query := Query) (Ev := Ev) W₂ q :=
  L.additive_of_independent' W₁ W₂ q (hind hsemi)

/-! ## Bridge to Support-Tracked Forgetting -/

/-- The revision `Δ` is fully supported inside the actionable coalition/footprint
associated to scope `S`. -/
def SupportedInActionableScope
    (T : Semitopology Supp)
    (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    (S : Scope) (Δ : State) : Prop :=
  T.actionable (↑(F.scopeFootprint S) : Set Supp) ∧
  ∀ q, F.support Δ q ⊆ F.scopeFootprint S

theorem exactInverse_of_supportedInActionableScope
    (T : Semitopology Supp)
    (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    {S : Scope} {Δ : State}
    (hsupp : SupportedInActionableScope T F S Δ) :
    ∀ W : State, F.forget S (W + Δ) = W := by
  exact F.exactInverse_revision_of_support_subset hsupp.2

end Semitopology
end Mettapedia.Logic
