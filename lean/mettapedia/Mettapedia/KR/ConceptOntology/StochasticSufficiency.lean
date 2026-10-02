import Mettapedia.KR.ConceptOntology.Formation
import Mettapedia.ProbabilityTheory.BayesianInference.SufficientFiltering
import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptiveSemantics

/-!
# Formed concept observations and sufficient stochastic representations

A concept family supplies overlapping extent observations. Agreement of all
membership observations induces the state classes; the extents themselves are
not assumed to partition the state space. Only realizable signatures are used
as abstract states. The compressed dynamics is the existing aggregated kernel,
with its prediction and filtering laws conditional on strong lumpability.
-/

namespace Mettapedia.KR.ConceptOntology.StochasticSufficiency

open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.FiniteLumpability
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.Cybernetics.ApproximateAdequacy

variable {Obj Attr K A : Type*} [Fintype Obj] [Fintype K]

/-- Membership in each retained concept extent, including overlapping concepts. -/
noncomputable def signature (meaning : K → DualConcept Obj Attr) (state : Obj) : K → Bool := by
  classical
  exact fun k => decide (state ∈ (meaning k).extent)

omit [Fintype Obj] [Fintype K] in
theorem signature_eq_iff (meaning : K → DualConcept Obj Attr) (first second : Obj) :
    signature meaning first = signature meaning second ↔
      ∀ k, (first ∈ (meaning k).extent ↔ second ∈ (meaning k).extent) := by
  classical
  simp only [signature, funext_iff, decide_eq_decide]

/-- The carrier excludes unrealizable combinations of concept memberships. -/
abbrev ConceptState (meaning : K → DualConcept Obj Attr) := Set.range (signature meaning)

noncomputable instance conceptStateFintype (meaning : K → DualConcept Obj Attr) :
    Fintype (ConceptState meaning) := by
  classical
  exact Fintype.ofFinite _

noncomputable def observe (meaning : K → DualConcept Obj Attr) (state : Obj) :
    ConceptState meaning := ⟨signature meaning state, ⟨state, rfl⟩⟩

noncomputable def representative (meaning : K → DualConcept Obj Attr)
    (state : ConceptState meaning) : Obj := Classical.choose state.2

omit [Fintype Obj] [Fintype K] in
theorem representative_section (meaning : K → DualConcept Obj Attr) :
    Function.RightInverse (representative meaning) (observe meaning) := by
  intro state
  apply Subtype.ext
  exact Classical.choose_spec state.2

/-- Construct the finite compressed kernel by aggregating actual source transitions. -/
noncomputable def compressedKernel (meaning : K → DualConcept Obj Attr)
    (kernel : A → Obj → Prob Obj) : A → ConceptState meaning → Prob (ConceptState meaning) := by
  classical
  exact lumpedKernel (observe meaning) kernel (representative meaning)

theorem prediction_commutes (meaning : K → DualConcept Obj Attr)
    (kernel : A → Obj → Prob Obj)
    (sufficient : StrongLumpability (observe meaning) kernel) (prior : Prob Obj) (action : A) :
    Prob.coarsen (Prob.bind prior (kernel action)) (observe meaning) =
      Prob.bind (Prob.coarsen prior (observe meaning)) (compressedKernel meaning kernel action) := by
  classical
  exact coarsen_predict (observe meaning) kernel (representative meaning)
    (representative_section meaning) sufficient prior action

theorem filtering_commutes (meaning : K → DualConcept Obj Attr)
    (kernel : A → Obj → Prob Obj)
    (sufficient : StrongLumpability (observe meaning) kernel) (prior : Prob Obj) (action : A)
    (likelihood : ConceptState meaning → ℝ) (nonneg : ∀ c, 0 ≤ likelihood c)
    (possible : 0 < evidence (Prob.bind prior (kernel action)) (likelihood ∘ observe meaning)) :
    Prob.coarsen (posterior (Prob.bind prior (kernel action)) (likelihood ∘ observe meaning)
      (fun s => nonneg (observe meaning s)) possible) (observe meaning) =
    posterior (Prob.bind (Prob.coarsen prior (observe meaning)) (compressedKernel meaning kernel action))
      likelihood nonneg (by
        rw [← prediction_commutes meaning kernel sufficient, evidence_coarsen]
        exact possible) := by
  classical
  exact coarsen_filter_step (observe meaning) kernel (representative meaning)
    (representative_section meaning) sufficient prior action likelihood nonneg possible

/-- The observation-producing kernel of the compressed model is constructed
from its aggregated transition and the retained emission, rather than assumed. -/
theorem observed_kernel_commutes {O : Type*} [Fintype O] [DecidableEq O]
    (meaning : K → DualConcept Obj Attr) (kernel : A → Obj → Prob Obj)
    (sufficient : StrongLumpability (observe meaning) kernel)
    (emission : A → ConceptState meaning → Prob O) (action : A) (state : Obj) :
    Prob.coarsen (joint (kernel action state) (emission action ∘ observe meaning))
      (fun next => (observe meaning next.1, next.2)) =
      joint (compressedKernel meaning kernel action (observe meaning state))
        (emission action) := by
  classical
  rw [coarsen_joint]
  congr 1
  exact (lumpedKernel_correct (observe meaning) kernel (representative meaning)
    (representative_section meaning) sufficient action state).symm

/-- Every contingent policy carries over to the constructed compressed model,
provided both its emissions and terminal goal use the retained concepts. -/
theorem policy_value_commutes {O : Type*} [Fintype O] [DecidableEq O]
    (meaning : K → DualConcept Obj Attr) (kernel : A → Obj → Prob Obj)
    (sufficient : StrongLumpability (observe meaning) kernel)
    (emission : A → ConceptState meaning → Prob O)
    (reward : ConceptState meaning → ℝ) {n : ℕ} (policy : ObservationPolicy O A n)
    (state : Obj) :
    adaptiveValue (fun a s => joint (kernel a s) (emission a ∘ observe meaning))
      (reward ∘ observe meaning) policy state =
    adaptiveValue (fun a c => joint (compressedKernel meaning kernel a c) (emission a))
      reward policy (observe meaning state) := by
  classical
  exact adaptiveValue_coarsen (observe meaning) _ _
    (observed_kernel_commutes meaning kernel sufficient emission) reward policy state

/-- Concepts selected from the existing evidence-gated formation interface
supply the sufficient observation family for prediction. -/
theorem formed_prediction_commutes {Q : Type*} [Preorder Q] [Fintype Attr]
    (gate : EvidenceGate Q) (membership : Obj → Attr → Q)
    (selected : K → FormedConcept gate membership) (kernel : A → Obj → Prob Obj)
    (sufficient : StrongLumpability
      (observe (fun k => (formedConceptInterpretation gate membership).meaning (selected k))) kernel)
    (prior : Prob Obj) (action : A) :
    let meaning := fun k => (formedConceptInterpretation gate membership).meaning (selected k)
    Prob.coarsen (Prob.bind prior (kernel action)) (observe meaning) =
      Prob.bind (Prob.coarsen prior (observe meaning)) (compressedKernel meaning kernel action) :=
  prediction_commutes _ kernel sufficient prior action

omit [Fintype Obj] [Fintype K] in
/-- A new concept family retaining every old extent retains all old observations. -/
theorem signature_refinement {New : Type*} (old : K → DualConcept Obj Attr)
    (new : New → DualConcept Obj Attr) (embedding : K → New)
    (retains : ∀ k, (new (embedding k)).extent = (old k).extent) (state : Obj) :
    signature old state = signature new state ∘ embedding := by
  classical
  funext k
  simp [signature, retains]

namespace OverlapControl

def meaning : Bool → DualConcept (Fin 3) Unit
  | false => ⟨{x | x = 0 ∨ x = 1}, Set.univ⟩
  | true => ⟨{x | x = 1 ∨ x = 2}, Set.univ⟩

omit [Fintype Obj] [Fintype K] in
theorem extents_overlap : (1 : Fin 3) ∈ (meaning false).extent ∩ (meaning true).extent := by
  simp [meaning]

omit [Fintype Obj] [Fintype K] in
theorem membership_distinguishes : signature meaning (0 : Fin 3) ≠ signature meaning 1 := by
  intro same
  have at_true := congrArg (fun f : Bool → Bool => f true) same
  norm_num [signature, meaning] at at_true
  exact (by decide : (0 : Fin 3) ≠ 2) at_true

end OverlapControl

end Mettapedia.KR.ConceptOntology.StochasticSufficiency
