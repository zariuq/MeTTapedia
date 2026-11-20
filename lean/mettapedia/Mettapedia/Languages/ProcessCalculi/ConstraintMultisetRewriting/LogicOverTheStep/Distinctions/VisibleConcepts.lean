import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.ObserverConcepts
import Mettapedia.Hyperseed.Regression

/-!
# Observers restricted to a visible region

Restricting the observer family to a visible region of queries: each visible query reads whether
it belongs to a set of queries (`visible`). Two sets are indistinguishable to it exactly when they
agree on the region (`indist_visible_iff`).

**The visible consequences are determined by the visible part of the seed exactly when the region
is backward closed under the active rules** (`respects_closure_iff`): consequence closure respects
the visible observers on seeds and on consequences, equivalently it pulls every type of the
restricted family back to a type (`pullback_closure_iff`), exactly when no active rule enters the
region from a hidden premise. This is the observer form of
`Hyperseed.backwardClosedAt_iff_closure_observation`.

Controls on the agent fixture of `Hyperseed.Regression`: the local region is backward closed, and
its visible consequences are determined by its visible seed (`local_respects`); the terminal region
is not once a pulse is observed, and two seeds that agree on it have different visible
consequences (`terminal_not_respects`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.VisibleConcepts

open Set
open Mettapedia.Hyperseed
open Mettapedia.PLN.Evidence.EvidenceClass Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open ObserverConcepts

section General

variable {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]

/-- **The observers of a visible region**: whether each visible query belongs to a set. -/
def visible (V : Set Query) : V → Set Query → Prop := fun q S => q.1 ∈ S

/-- Two sets are indistinguishable to the region's observers exactly when they agree on it. -/
theorem indist_visible_iff (V S T : Set Query) : Indist (visible V) S T ↔ S ∩ V = T ∩ V := by
  constructor
  · intro same
    ext q
    exact ⟨fun ⟨inS, inV⟩ => ⟨(Iff.of_eq (same ⟨q, inV⟩)).mp inS, inV⟩,
      fun ⟨inT, inV⟩ => ⟨(Iff.of_eq (same ⟨q, inV⟩)).mpr inT, inV⟩⟩
  · intro equal q
    apply propext
    constructor
    · intro inS
      exact ((Set.ext_iff.mp equal q.1).mp ⟨inS, q.2⟩).1
    · intro inT
      exact ((Set.ext_iff.mp equal q.1).mpr ⟨inT, q.2⟩).1

/-- **The visible consequences are determined by the visible seed exactly when the region is
backward closed under the active rules.** -/
theorem respects_closure_iff (R : RuleSet State Query) (W : State) (V : Set Query) :
    Respects (visible V) (visible V) (leastRuleClosure R W) ↔ BackwardClosedAt R W V := by
  constructor
  · intro respects r member active visibleConclusion
    by_contra hidden
    have same : Indist (visible V) {r.premise} ∅ := by
      refine (indist_visible_iff V _ _).mpr ?_
      ext q
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.empty_inter, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro rfl
      exact hidden
    have equal := (indist_visible_iff V _ _).mp (respects _ _ same)
    have reached : r.conclusion ∈ leastRuleClosure R W {r.premise} ∩ V :=
      ⟨leastRuleClosure_rule_closed R W _ member active
        (seed_subset_leastRuleClosure _ _ _ (Set.mem_singleton _)), visibleConclusion⟩
    rw [equal, leastRuleClosure_empty] at reached
    exact reached.1
  · intro closed S T same
    refine (indist_visible_iff V _ _).mpr ?_
    rw [leastRuleClosure_inter_visible R W V closed S, leastRuleClosure_inter_visible R W V closed T,
      (indist_visible_iff V S T).mp same]

/-- **The same, as pullbacks of types**: consequence closure pulls every type of the restricted
family back to a type exactly when the region is backward closed. -/
theorem pullback_closure_iff (R : RuleSet State Query) (W : State) (V : Set Query) :
    (∀ X, IsConcept (Apart (visible V)) X →
        IsConcept (Apart (visible V)) (leastRuleClosure R W ⁻¹' X)) ↔ BackwardClosedAt R W V :=
  (pullback_isConcept_iff _ _ _).trans (respects_closure_iff R W V)

end General

/-! ## Controls on the agent fixture -/

section Controls

open Regression Regression.VisibleInference

/-- **The local region**: its visible consequences are determined by its visible seed. -/
theorem local_respects (σ : Multiset AgentObservation) :
    Respects (visible localRegion) (visible localRegion) (leastRuleClosure agentRules σ) :=
  (respects_closure_iff agentRules σ localRegion).mpr (local_backward_closed σ)

/-- **The terminal region, once a pulse is observed**: two seeds that agree on it have different
visible consequences. -/
theorem terminal_not_respects {σ : Multiset AgentObservation} (active : σ ≠ 0) :
    ¬ Respects (visible terminalRegion) (visible terminalRegion) (leastRuleClosure agentRules σ) :=
  fun respects => terminal_not_backward_closed active
    ((respects_closure_iff agentRules σ terminalRegion).mp respects)

/-- A pulse is an observation. -/
theorem pulse_active : ({AgentObservation.pulse} : Multiset AgentObservation) ≠ 0 := by
  simp

end Controls

#print axioms indist_visible_iff
#print axioms respects_closure_iff
#print axioms pullback_closure_iff
#print axioms local_respects
#print axioms terminal_not_respects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.VisibleConcepts
