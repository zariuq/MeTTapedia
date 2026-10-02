import Mettapedia.KR.ConceptOntology.StochasticSufficiency

/-!
# A nontrivial sufficient concept compression

Four states carry a task-relevant bit and an irrelevant implementation bit.
The retained concept identifies states with the same task bit. Controlled
transitions change that bit and reset the implementation bit. This genuine
compression preserves all retained-emission policies, while a consumer of
the hidden implementation bit provably cannot descend.
-/

namespace Mettapedia.KR.ConceptOntology.StochasticSufficiency.CompressionControl

open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.FiniteLumpability
open Mettapedia.Cybernetics.ApproximateAdequacy

abbrev State := Bool × Bool

def meaning (_ : Unit) : DualConcept State Unit :=
  ⟨{s | s.1 = true}, Set.univ⟩

/-- This retained extent is an actual closed formal concept of the crisp
membership relation, not an arbitrary label attached to a state class. -/
theorem meaning_is_formed :
    meaning () ∈ finiteClosedConceptFamily (fun state (_ : Unit) => state.1 = true) := by
  rw [mem_finiteClosedConceptFamily_iff]
  constructor
  · ext question
    constructor
    · intro _
      trivial
    · intro _ state retained
      exact retained
  · ext state
    constructor
    · intro retained
      exact retained (Set.mem_univ ())
    · intro retained question _
      exact retained

theorem observe_eq_iff (s t : State) : observe meaning s = observe meaning t ↔ s.1 = t.1 := by
  rw [Subtype.ext_iff]
  change signature meaning s = signature meaning t ↔ s.1 = t.1
  rw [signature_eq_iff]
  simp only [meaning, Set.mem_ofPred_eq, forall_const]
  cases hs : s.1 <;> cases ht : t.1 <;> simp

noncomputable def kernel (action : Bool) (s : State) : Prob State :=
  Prob.dirac (if action then (!s.1, false) else (s.1, true))

theorem lumpable : StrongLumpability (observe meaning) kernel := by
  intro a s t same
  have equal := (observe_eq_iff s t).mp same
  simp only [kernel, equal]

theorem genuine_compression :
    (false, false) ≠ (false, true) ∧
      observe meaning (false, false) = observe meaning (false, true) := by
  exact ⟨by decide, (observe_eq_iff _ _).mpr rfl⟩

theorem hidden_consumer_does_not_descend :
    ¬ ∃ consumer : ConceptState meaning → Bool,
      ∀ state : State, consumer (observe meaning state) = state.2 := by
  rintro ⟨consumer, correct⟩
  have first := correct (false, false)
  have second := correct (false, true)
  rw [← genuine_compression.2, first] at second
  contradiction

/-- All finite adaptive values are preserved in the constructed two-class
kernel, without identifying the four source states themselves. -/
theorem all_policy_values_preserved {O : Type*} [Fintype O] [DecidableEq O]
    (emission : Bool → ConceptState meaning → Prob O)
    (reward : ConceptState meaning → ℝ) {n : ℕ} (policy : ObservationPolicy O Bool n)
    (state : State) :
    adaptiveValue
      (fun a s => Mettapedia.ProbabilityTheory.BayesianInference.joint
        (kernel a s) (emission a ∘ observe meaning))
      (reward ∘ observe meaning) policy state =
    adaptiveValue
      (fun a c => Mettapedia.ProbabilityTheory.BayesianInference.joint
        (compressedKernel meaning kernel a c) (emission a))
      reward policy (observe meaning state) :=
  policy_value_commutes meaning kernel lumpable emission reward policy state

end Mettapedia.KR.ConceptOntology.StochasticSufficiency.CompressionControl
