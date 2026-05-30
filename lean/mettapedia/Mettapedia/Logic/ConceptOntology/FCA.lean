import Mathlib.Order.Concept
import Mettapedia.Logic.ConceptOntology.Basic

/-!
# Crisp FCA View of Evidence-Valued Ontology

This module derives a late crisp view from evidence-valued membership by
gating evidence into a `Prop` relation and then reusing mathlib's `Concept`
infrastructure.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic.EvidenceQuantale

universe u v w

/-- A monotone gate for turning evidence into crisp membership judgments. -/
structure EvidenceGate (Q : Type u) [Preorder Q] where
  accept : Q → Prop
  mono : Monotone accept

namespace EvidenceGate

variable {Q : Type u} [Preorder Q]

/-- The canonical upper-set gate at threshold `τ`. -/
def threshold (τ : Q) : EvidenceGate Q where
  accept q := τ ≤ q
  mono := by
    intro a b hab hτ
    exact le_trans hτ hab

theorem accept_mono (G : EvidenceGate Q) {a b : Q} (hab : a ≤ b) :
    G.accept a → G.accept b :=
  G.mono hab

section BinaryEvidence

open scoped ENNReal

/-- Canonical membership gate: an object counts as a member once it has any
positive support. This is monotone in the BinaryEvidence information order. -/
def positiveSupport : EvidenceGate BinaryEvidence where
  accept e := 0 < e.pos
  mono := by
    intro a b hab ha
    exact lt_of_lt_of_le ha hab.1

/-- Canonical thresholded membership gate on the positive-evidence coordinate. -/
def positiveThreshold (τ : ℝ≥0∞) : EvidenceGate BinaryEvidence where
  accept e := τ ≤ e.pos
  mono := by
    intro a b hab hτ
    exact le_trans hτ hab.1

@[simp] theorem positiveSupport_accept_iff (e : BinaryEvidence) :
    positiveSupport.accept e ↔ 0 < e.pos := Iff.rfl

@[simp] theorem positiveThreshold_accept_iff (τ : ℝ≥0∞) (e : BinaryEvidence) :
    (positiveThreshold τ).accept e ↔ τ ≤ e.pos := Iff.rfl

theorem positiveThreshold_iff_threshold
    (τ : ℝ≥0∞) (e : BinaryEvidence) :
    (positiveThreshold τ).accept e ↔
      (threshold (Q := BinaryEvidence) ⟨τ, 0⟩).accept e := by
  simp [positiveThreshold, threshold, BinaryEvidence.le_def]

end BinaryEvidence

end EvidenceGate

section Crisp

variable {Obj : Type u} {Con : Type v} {Q : Type w} [Preorder Q]

/-- The crisp incidence relation induced by an evidence gate. -/
def crispRelation (G : EvidenceGate Q) (M : Obj → Con → Q) : Obj → Con → Prop :=
  fun x c => G.accept (M x c)

/-- The crisp extent of a base concept, derived from the gated membership
relation. -/
def crispExtent (G : EvidenceGate Q) (M : Obj → Con → Q) (c : Con) : Set Obj :=
  _root_.lowerPolar (crispRelation G M) ({c} : Set Con)

/-- The crisp intent of an object, derived from the gated membership relation. -/
def crispIntent (G : EvidenceGate Q) (M : Obj → Con → Q) (x : Obj) : Set Con :=
  _root_.upperPolar (crispRelation G M) ({x} : Set Obj)

@[simp] theorem mem_crispExtent_iff
    (G : EvidenceGate Q) (M : Obj → Con → Q) (x : Obj) (c : Con) :
    x ∈ crispExtent G M c ↔ G.accept (M x c) := by
  constructor
  · intro hx
    exact hx (by simp)
  · intro hx d hd
    rcases Set.mem_singleton_iff.mp hd with rfl
    exact hx

@[simp] theorem mem_crispIntent_iff
    (G : EvidenceGate Q) (M : Obj → Con → Q) (x : Obj) (c : Con) :
    c ∈ crispIntent G M x ↔ G.accept (M x c) := by
  constructor
  · intro hx
    exact hx (by simp)
  · intro hx y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hx

/-- Mathlib's formal concepts over the gated evidence relation. -/
abbrev CrispConcept (G : EvidenceGate Q) (M : Obj → Con → Q) :=
  _root_.Concept Obj Con (crispRelation G M)

theorem gc_crispUpper_lower
    (G : EvidenceGate Q) (M : Obj → Con → Q) :
    GaloisConnection
      (OrderDual.toDual ∘ _root_.upperPolar (crispRelation G M))
      (_root_.lowerPolar (crispRelation G M) ∘ OrderDual.ofDual) :=
  _root_.gc_upperPolar_lowerPolar (crispRelation G M)

/-- Extensional inheritance between base concepts is inclusion of their gated
extents. -/
def crispExtensionalInherits
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c d : Con) : Prop :=
  crispExtent G M c ⊆ crispExtent G M d

theorem crispExtensionalInherits_iff
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c d : Con) :
    crispExtensionalInherits G M c d ↔ ∀ x, G.accept (M x c) → G.accept (M x d) := by
  constructor
  · intro h x hx
    have hx' : x ∈ crispExtent G M c := by
      simpa using hx
    have hx'' : x ∈ crispExtent G M d := h hx'
    simpa using hx''
  · intro h x hx
    have hx' : G.accept (M x c) := by
      simpa using hx
    have hx'' : G.accept (M x d) := h x hx'
    simpa using hx''

end Crisp

end Mettapedia.Logic.ConceptOntology
