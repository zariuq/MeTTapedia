import Foundation.FirstOrder.SetTheory.Universe
import Mettapedia.Logic.HOL.Embedding.FirstOrder

/-!
# Set-Based HOL Semantics

This module supplies the direct low-level `SetSemantics -> HOL` arrow by
specializing the generic first-order-to-HOL standard-model construction to
Foundation's set-theory language `ℒₛₑₜ`.

The current file is intentionally semantic rather than world-model facing:
it turns set-theoretic membership structures into genuine Henkin HOL models,
and it proves truth preservation for embedded set-theory sentences.
-/

namespace Mettapedia.Logic.HOL.Semantics.SetBased

open LO
open LO.FirstOrder
open LO.FirstOrder.SetTheory
open Mettapedia.Logic.HOL

universe w

/-- Base-type family used by the direct set-theory-to-HOL grounding. -/
abbrev SetBaseTy := Embedding.FirstOrder.BaseTy

/-- HOL constants induced by the set-theory language `ℒₛₑₜ`. -/
abbrev SetConst := Embedding.FirstOrder.Const ℒₛₑₜ

/-- Closed HOL queries over the direct set-theory grounding. -/
abbrev SetHOLQuery := ClosedFormula SetConst

/-- Pointed HOL models induced from set-theoretic membership structures. -/
abbrev SetHOLModel := HenkinModel SetBaseTy SetConst

/-- Direct semantic grounding from a set-theoretic membership structure to a
standard Henkin HOL model. -/
def ofSetStructure (M : Type w) [SetStructure M] [Nonempty M] : SetHOLModel :=
  Embedding.FirstOrder.standardModel (L := ℒₛₑₜ) (s := standardStructure M)

/-- The same grounding, but starting from a pointed Foundation structure. -/
def ofPointed (S : SmallStruc ℒₛₑₜ) : SetHOLModel :=
  Embedding.FirstOrder.standardModel (L := ℒₛₑₜ) S.struc

/-- Embedded set-theory sentences preserve truth in the directly induced HOL
model of a membership structure. This is stated in raw denotation form to make
the semantic grounding arrow completely explicit. -/
theorem denote_embedSentence_iff
    (M : Type w) [SetStructure M] [Nonempty M] (φ : LO.FirstOrder.Sentence ℒₛₑₜ) :
    ((ofSetStructure M).denote
      (Embedding.FirstOrder.embedSentence φ)
      (fun v => nomatch v)).down ↔
      M ⊧ₘ φ := by
  simpa [LO.FirstOrder.models_iff, ofSetStructure] using
    (Embedding.FirstOrder.denote_embedSentence_iff
      (L := ℒₛₑₜ) (s := standardStructure M) (φ := φ))

/-- Pointed set-theory structures and their directly induced HOL models agree on
embedded set-theory sentences. This raw denotation form keeps the low-level
semantic arrow explicit. -/
theorem pointed_denote_embedSentence_iff
    (S : SmallStruc ℒₛₑₜ) (φ : LO.FirstOrder.Sentence ℒₛₑₜ) :
    ((ofPointed S).denote
      (Embedding.FirstOrder.embedSentence φ)
      (fun v => nomatch v)).down ↔
      S ⊧ φ := by
  simpa [ofPointed] using
    (Embedding.FirstOrder.denote_embedSentence_iff
      (L := ℒₛₑₜ) (s := S.struc) (φ := φ))

/-- The canonical Foundation universe yields a direct HOL model that validates
embedded `ZF` theorems. -/
theorem universe_models_embedSentence_of_mem_zf
    (φ : LO.FirstOrder.Sentence ℒₛₑₜ) (hφ : φ ∈ (𝗭𝗙 : Theory ℒₛₑₜ)) :
    ((ofSetStructure Universe).denote
      (Embedding.FirstOrder.embedSentence φ)
      (fun v => nomatch v)).down := by
  have hmodels : Universe ⊧ₘ φ :=
    LO.FirstOrder.Theory.models (M := Universe) (T := (𝗭𝗙 : Theory ℒₛₑₜ)) hφ
  exact (denote_embedSentence_iff (M := Universe) φ).2 hmodels

/-- Negative canary: the directly induced HOL universe model does not satisfy
the embedded set-theory false sentence. -/
theorem universe_not_models_embedSentence_falsum :
    ¬ ((ofSetStructure Universe).denote
      (Embedding.FirstOrder.embedSentence (⊥ : LO.FirstOrder.Sentence ℒₛₑₜ))
      (fun v => nomatch v)).down := by
  intro h
  have hmodels : Universe ⊧ₘ (⊥ : LO.FirstOrder.Sentence ℒₛₑₜ) :=
    (denote_embedSentence_iff
      (M := Universe) (φ := (⊥ : LO.FirstOrder.Sentence ℒₛₑₜ))).1 h
  simp at hmodels

end Mettapedia.Logic.HOL.Semantics.SetBased
