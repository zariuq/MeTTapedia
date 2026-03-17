import Mettapedia.Logic.PLNTemporal
import Mettapedia.Logic.OSLFEvidenceSemantics
import Mettapedia.Logic.PLNProbabilisticEventCalculus
import Mettapedia.OSLF.Framework.VertexTemporalRewriteRules
import Mettapedia.OSLF.Framework.HypercubeTemporalGSLTFunctor
import Mettapedia.OSLF.Framework.QuantaleCoherence

/-!
# PLN Chapter 14 Layer: Temporal and Causal Inference

This module formalizes a compact core of Chapter 14 from the PLN book:

- Temporal link families used in temporal reasoning (`SimAND`, `SimOR`,
  eventual/disjoint sequential links, predictive chains).
- A lightweight causal discriminator matching the chapter's
  extensional-vs-intensional discussion.

It is intentionally compositional over `PLNTemporal.lean`, reusing:

- `TemporalPredicate`
- `SequentialAnd`, `SequentialOr`
- `PredictiveImplication`
- `Lead`
-/

universe u v

namespace Mettapedia.Logic.PLNTemporalCausalInference

open TemporalPredicate

def TemporalPred (Domain : Type u) (Time : Type v) := TemporalPredicate Domain Time

section TemporalLinks

variable {Domain : Type u} {Time : Type v}
variable [AddCommGroup Time]

/-- Simultaneous conjunction (Chapter 14.3): both predicates hold now. -/
def SimAND (P Q : TemporalPred Domain Time) : TemporalPred Domain Time :=
  fun x t => P x t ∧ Q x t

/-- Simultaneous disjunction (Chapter 14.3): at least one predicate holds now. -/
def SimOR (P Q : TemporalPred Domain Time) : TemporalPred Domain Time :=
  fun x t => P x t ∨ Q x t

/-- Eventual sequential conjunction (Chapter 14.3.1):
`P` holds now and `Q` holds at some future (or otherwise selected) offset. -/
def EventualSeqAND (P Q : TemporalPred Domain Time) : TemporalPred Domain Time :=
  fun x t => P x t ∧ ∃ Δ : Time, Q x (t + Δ)

/-- Disjoint sequential conjunction parameterized by an admissible-delay predicate.
Typical use is `future Δ := 0 < Δ`. -/
def DisjointSeqAND (future : Time → Prop)
    (P Q : TemporalPred Domain Time) : TemporalPred Domain Time :=
  fun x t => P x t ∧ ∃ Δ : Time, future Δ ∧ Q x (t + Δ)

/-- Eventual predictive implication (Chapter 14.3.3):
if `P` holds now, `Q` holds at some (not pre-fixed) offset. -/
def EventualPredictiveImplication
    (P Q : TemporalPred Domain Time) : TemporalPred Domain Time :=
  fun x t => P x t → ∃ Δ : Time, Q x (t + Δ)

/-- Three-node predictive chain specialization (Chapter 14.3.4):
`PredictiveImplication T₂ (SeqAND T₁ A B) C`. -/
def PredictiveChain3 (T₁ T₂ : Time)
    (A B C : TemporalPred Domain Time) : TemporalPred Domain Time :=
  PredictiveImplication T₂ (SequentialAnd T₁ A B) C

theorem simAND_eq_sequentialAnd_zero
    (P Q : TemporalPred Domain Time) :
    SimAND P Q = SequentialAnd (0 : Time) P Q := by
  funext x t
  apply propext
  simp [SimAND, SequentialAnd, Lead]

theorem simOR_eq_sequentialOr_zero
    (P Q : TemporalPred Domain Time) :
    SimOR P Q = SequentialOr (0 : Time) P Q := by
  funext x t
  apply propext
  simp [SimOR, SequentialOr, Lead]

theorem sequentialAnd_implies_eventualSeqAND
    (T : Time) (P Q : TemporalPred Domain Time) {x : Domain} {t : Time}
    (h : SequentialAnd T P Q x t) :
    EventualSeqAND P Q x t := by
  rcases h with ⟨hP, hQ⟩
  refine ⟨hP, T, ?_⟩
  simpa [Lead] using hQ

theorem disjointSeqAND_intro
    (future : Time → Prop) (P Q : TemporalPred Domain Time)
    {x : Domain} {t Δ : Time}
    (hP : P x t) (hΔ : future Δ) (hQ : Q x (t + Δ)) :
    DisjointSeqAND future P Q x t := by
  exact ⟨hP, Δ, hΔ, hQ⟩

theorem predictiveImplication_implies_eventual
    (T : Time) (P Q : TemporalPred Domain Time) {x : Domain} {t : Time}
    (h : PredictiveImplication T P Q x t) :
    EventualPredictiveImplication P Q x t := by
  intro hP
  refine ⟨T, ?_⟩
  have h' : P x t → Q x (t + T) := by
    simpa [PredictiveImplication, Lead] using h
  exact h' hP

theorem eventualPredictive_modus_ponens
    (P Q : TemporalPred Domain Time) {x : Domain} {t : Time}
    (hP : P x t) (hImp : EventualPredictiveImplication P Q x t) :
    ∃ Δ : Time, Q x (t + Δ) :=
  hImp hP

theorem predictiveChain3_eq
    (T₁ T₂ : Time) (A B C : TemporalPred Domain Time) :
    PredictiveChain3 T₁ T₂ A B C =
      fun x t => (A x t ∧ B x (t + T₁)) → C x (t + T₂) := by
  funext x t
  apply propext
  simp [PredictiveChain3, PredictiveImplication, SequentialAnd, Lead]

theorem predictiveChain3_intro
    (T₁ T₂ : Time) (A B C : TemporalPred Domain Time)
    {x : Domain} {t : Time}
    (h : (A x t ∧ B x (t + T₁)) → C x (t + T₂)) :
    PredictiveChain3 T₁ T₂ A B C x t := by
  intro hSeq
  rcases hSeq with ⟨hA, hBlead⟩
  have hB : B x (t + T₁) := by
    simpa [Lead] using hBlead
  show Lead C T₂ x t
  simpa [Lead] using h ⟨hA, hB⟩

theorem predictiveChain3_mp
    (T₁ T₂ : Time) (A B C : TemporalPred Domain Time)
    {x : Domain} {t : Time}
    (hA : A x t) (hB : B x (t + T₁))
    (hChain : PredictiveChain3 T₁ T₂ A B C x t) :
    C x (t + T₂) := by
  have hSeq : SequentialAnd T₁ A B x t := by
    refine ⟨hA, ?_⟩
    simpa [Lead] using hB
  have hLeadC : Lead C T₂ x t := hChain hSeq
  simpa [Lead] using hLeadC

end TemporalLinks

section WMGrounding

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula

variable {State : Type*}
variable [EvidenceType State] [BinaryWorldModel State Pattern]

/-- Chapter-14 sequential conjunction at the evidence layer, grounded in
the WM temporal atom semantics. -/
noncomputable def chapter14SequentialAndSemE
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) :=
  sequentialAndSemE R W baseAtomQuery baseTime T φ ψ p

/-- Chapter-14 predictive implication at the evidence layer, grounded in
the WM temporal atom semantics. -/
noncomputable def chapter14PredictiveImplicationSemE
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) :=
  predictiveImplicationSemE R W baseAtomQuery baseTime T φ ψ p

theorem chapter14SequentialAnd_le_left
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) :
    chapter14SequentialAndSemE R W baseAtomQuery baseTime T φ ψ p ≤
      semE R (temporalEvidenceAtomSem W baseAtomQuery baseTime) φ p := by
  simpa [chapter14SequentialAndSemE] using
    (sequentialAnd_le_left R W baseAtomQuery baseTime T φ ψ p)

theorem chapter14PredictiveImplication_mp
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R (temporalEvidenceAtomSem W baseAtomQuery baseTime) φ p ⊓
      chapter14PredictiveImplicationSemE R W baseAtomQuery baseTime T φ ψ p ≤
      semE R (temporalEvidenceAtomSem W baseAtomQuery (baseTime + T)) ψ p := by
  simpa [chapter14PredictiveImplicationSemE] using
    (predictiveImplication_mp R W baseAtomQuery baseTime T φ ψ p)

end WMGrounding

section CausalHeuristics

variable {Domain : Type u} {Time : Type v}

/-- Chapter 14.5 causal profile:
extensional predictive support vs intensional predictive support. -/
structure PredictiveCausalProfile where
  extensional : TemporalPred Domain Time
  intensional : TemporalPred Domain Time

/-- A candidate spurious causal edge (high extensional support, weak intensional support)
captured at the proposition level as extensional truth plus intensional failure. -/
def SpuriousCausalCandidate
    (profile : PredictiveCausalProfile (Domain := Domain) (Time := Time)) :
    TemporalPred Domain Time :=
  fun x t => profile.extensional x t ∧ ¬ profile.intensional x t

theorem spurious_has_extensional
    (profile : PredictiveCausalProfile (Domain := Domain) (Time := Time))
    {x : Domain} {t : Time}
    (h : SpuriousCausalCandidate profile x t) :
    profile.extensional x t := h.1

theorem spurious_lacks_intensional
    (profile : PredictiveCausalProfile (Domain := Domain) (Time := Time))
    {x : Domain} {t : Time}
    (h : SpuriousCausalCandidate profile x t) :
    ¬ profile.intensional x t := h.2

theorem not_spurious_of_intensional
    (profile : PredictiveCausalProfile (Domain := Domain) (Time := Time))
    {x : Domain} {t : Time}
    (hInt : profile.intensional x t) :
    ¬ SpuriousCausalCandidate profile x t := by
  intro hSpur
  exact hSpur.2 hInt

end CausalHeuristics

section HypercubeEventFlow

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.ProbabilityTheory.Hypercube
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.OSLF.Framework.VertexTemporalRewriteRules
open Mettapedia.OSLF.Framework.HypercubeTemporalGSLTFunctor
open Mettapedia.OSLF.Framework.QuantaleCoherence
open Mettapedia.Logic.PLNProbabilisticEventCalculus

/-- Chapter-14 event query example: atom-to-query encoding for `holdsAt`. -/
def chapter14EventHoldsQuery (a : String) (t : Pattern) : Sigma PatternEventQueryFamily :=
  patternEventQueryOfAtom_holds a t

theorem chapter14EventHoldsQuery_pattern
    (a : String) (t : Pattern) :
    sigmaEventQueryPattern (chapter14EventHoldsQuery a t) = pHoldsAt (.fvar a) t := rfl

/-- Concrete Chapter-14 flow step:
temporal/event reductions transport from `quantum` to `kolmogorov`. -/
theorem chapter14_event_forward_transport_quantum_to_kolmogorov
    {p q : Pattern}
    (hred : Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar
      (vertexTemporalLanguageDef quantum) p q) :
    Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar
      (vertexTemporalLanguageDef kolmogorov) p q :=
  gslt_temporal_forward_transport (by decide : kolmogorov ≤ quantum) hred

/-- Chapter-14 flow bundle:
`vertexTemporalLanguageDef` reachability transport and quantale coherence. -/
theorem chapter14_event_quantale_coherence_temporal
    {v w : ProbabilityVertex}
    (hvw : v ≤ w)
    (f : QuantaleHom
      (QuantaleSemantics.semanticsOfVertex w).Q
      (QuantaleSemantics.semanticsOfVertex v).Q)
    (srcVal : Pattern → (QuantaleSemantics.semanticsOfVertex w).Q)
    (dstVal : Pattern → (QuantaleSemantics.semanticsOfVertex v).Q)
    (hVal : ∀ p, dstVal p = f (srcVal p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar
      (vertexTemporalLanguageDef w) p₀ (pick u))
    (H : Finset (U × U)) :
    (∀ u, Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar
      (vertexTemporalLanguageDef v) p₀ (pick u)) ∧
      f (weakness (sourceWeight srcVal pick) H) =
        weakness (targetWeight dstVal id pick) H := by
  exact hypercube_forward_quantale_coherence_bundle_temporal
    (v := v) (w := w) hvw f srcVal dstVal hVal pick (p₀ := p₀) hReach H

end HypercubeEventFlow

end Mettapedia.Logic.PLNTemporalCausalInference
