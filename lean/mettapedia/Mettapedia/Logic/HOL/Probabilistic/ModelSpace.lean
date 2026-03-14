import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mettapedia.Logic.HOL.WorldModel

/-!
# Indexed Model Spaces for Probabilistic HOL

This module defines the canonical abstract model-space interface for
probabilistic semantics of closed HOL formulas.

The design is intentionally **indexed** rather than placing a measurable space
directly on raw `HenkinModel`. This keeps the semantic layer honest while
avoiding premature commitments about measurable structures on model objects.

The resulting `ProbHOL` path is compatible with the dynamic belief/process
layer inspired by Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), while remaining strictly
separate from that layer.
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WorldModel

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A measurable index space carrying a family of pointed Henkin models such that
every closed HOL sentence has a measurable satisfaction event. -/
structure ModelSpace (Base : Type u) (Const : Ty Base → Type v) where
  Idx : Type x
  instMeasurableSpace : MeasurableSpace Idx
  model : Idx → HenkinModel.{u, v, w} Base Const
  measurable_sentence_event :
    ∀ φ : ClosedFormula Const,
      MeasurableSet {i | holSatisfies (model i) φ}

attribute [instance] ModelSpace.instMeasurableSpace

namespace ModelSpace

/-- Satisfaction event of a closed HOL sentence in an indexed model space. -/
def sentenceEvent (S : ModelSpace Base Const) (φ : ClosedFormula Const) : Set S.Idx :=
  {i | holSatisfies (S.model i) φ}

@[simp] theorem mem_sentenceEvent (S : ModelSpace Base Const) (φ : ClosedFormula Const) (i : S.Idx) :
    i ∈ sentenceEvent S φ ↔ holSatisfies (S.model i) φ := Iff.rfl

theorem measurable_sentenceEvent (S : ModelSpace Base Const) (φ : ClosedFormula Const) :
    MeasurableSet (sentenceEvent S φ) :=
  S.measurable_sentence_event φ

/-- Pointwise semantic implication across the indexed family. -/
def PointwiseImplies (S : ModelSpace Base Const)
    (φ ψ : ClosedFormula Const) : Prop :=
  ∀ i : S.Idx, holSatisfies (S.model i) φ → holSatisfies (S.model i) ψ

/-- Pointwise semantic equivalence across the indexed family. -/
def PointwiseIff (S : ModelSpace Base Const)
    (φ ψ : ClosedFormula Const) : Prop :=
  ∀ i : S.Idx, holSatisfies (S.model i) φ ↔ holSatisfies (S.model i) ψ

theorem sentenceEvent_subset_of_pointwiseImplies
    (S : ModelSpace Base Const) {φ ψ : ClosedFormula Const}
    (himp : PointwiseImplies S φ ψ) :
    sentenceEvent S φ ⊆ sentenceEvent S ψ := by
  intro i hi
  exact himp i hi

theorem sentenceEvent_eq_of_pointwiseIff
    (S : ModelSpace Base Const) {φ ψ : ClosedFormula Const}
    (hiff : PointwiseIff S φ ψ) :
    sentenceEvent S φ = sentenceEvent S ψ := by
  ext i
  exact hiff i

theorem sentenceEvent_eq_of_pointwiseEq
    (S : ModelSpace Base Const) {φ ψ : ClosedFormula Const}
    (heq : ∀ i : S.Idx, holSatisfies (S.model i) φ = holSatisfies (S.model i) ψ) :
    sentenceEvent S φ = sentenceEvent S ψ := by
  apply sentenceEvent_eq_of_pointwiseIff (S := S)
  intro i
  exact heq i ▸ Iff.rfl

end ModelSpace

end Mettapedia.Logic.HOL.Probabilistic
