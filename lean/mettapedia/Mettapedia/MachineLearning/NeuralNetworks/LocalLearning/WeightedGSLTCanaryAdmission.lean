import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTFiniteAdmission

/-!
# Exact finite admission of the rewarded-choice canary

The four-event rewarded-choice protocol is reified as a finite event-driven
support graph.  Both learners traverse the same activity phases.  Their weight
marginals are the exact integrated learners from
`WeightedGSLTBehavioralAdequacy`:

* shipped saturating addition ends at weights `(3, 3)` and fails the `3/4`
  behavioral gate;
* local reward-sensitive potentiation ends at `(3, 1)` and passes it.

The unique bottom class of the finite support graph is its terminal phase, so
the generic recurrent-class admission gate rejects the shipped learner and
admits the reward-sensitive control.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTCanaryAdmission

open WeightedGSLTBehavioralAdequacy
open WeightedGSLTFiniteAdmission

inductive CanaryPhase where
  | start
  | afterTargetOne
  | afterDistractorOne
  | afterTargetTwo
  | done
deriving DecidableEq, Fintype

def phaseNext : CanaryPhase → CanaryPhase
  | .start => .afterTargetOne
  | .afterTargetOne => .afterDistractorOne
  | .afterDistractorOne => .afterTargetTwo
  | .afterTargetTwo => .done
  | .done => .done

def PhaseStep (source target : CanaryPhase) : Prop := phaseNext source = target

/-- The event history available at each phase, stored newest first as required
by the integrated trace semantics. -/
def phaseEpisode : CanaryPhase → List (LocalEvent ChoiceSynapse)
  | .start => []
  | .afterTargetOne =>
      [ { key := .target, rewarded := true } ]
  | .afterDistractorOne =>
      [ { key := .distractor, rewarded := false }
      , { key := .target, rewarded := true } ]
  | .afterTargetTwo =>
      [ { key := .target, rewarded := true }
      , { key := .distractor, rewarded := false }
      , { key := .target, rewarded := true } ]
  | .done => rewardedChoiceEpisode

noncomputable def shippedPhaseWeights (phase : CanaryPhase) : WeightMap ChoiceSynapse :=
  shippedChoiceLearner (phaseEpisode phase)

noncomputable def rewardSensitivePhaseWeights
    (phase : CanaryPhase) : WeightMap ChoiceSynapse :=
  rewardSensitiveChoiceLearner (phaseEpisode phase)

def ShippedGood (phase : CanaryPhase) : Prop :=
  rewardedChoiceTask.Solves (shippedPhaseWeights phase)

def RewardSensitiveGood (phase : CanaryPhase) : Prop :=
  rewardedChoiceTask.Solves (rewardSensitivePhaseWeights phase)

def doneClass : Set CanaryPhase := {CanaryPhase.done}

theorem phaseNext_done : phaseNext .done = .done := rfl

theorem reachable_from_done_eq_done {target : CanaryPhase}
    (hreach : Relation.ReflTransGen PhaseStep .done target) : target = .done := by
  induction hreach with
  | refl => rfl
  | tail _ hstep ih =>
      rw [ih] at hstep
      change phaseNext CanaryPhase.done = _ at hstep
      simpa [phaseNext] using hstep.symm

theorem doneClass_bottom : BottomClass PhaseStep doneClass := by
  refine ⟨⟨.done, rfl⟩, ?_, ?_⟩
  · intro source hsource target htarget
    simp only [doneClass, Set.mem_singleton_iff] at hsource htarget
    subst source
    subst target
    exact Relation.ReflTransGen.refl
  · intro source hsource target hstep
    simp only [doneClass, Set.mem_singleton_iff] at hsource ⊢
    subst source
    change phaseNext CanaryPhase.done = target at hstep
    simpa [phaseNext] using hstep.symm

theorem doneClass_reachable : ReachableClass PhaseStep .start doneClass := by
  refine ⟨.done, rfl, ?_⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single (show PhaseStep .start .afterTargetOne from rfl))
        (show PhaseStep .afterTargetOne .afterDistractorOne from rfl))
      (show PhaseStep .afterDistractorOne .afterTargetTwo from rfl))
    (show PhaseStep .afterTargetTwo .done from rfl)

theorem done_mem_of_bottomClass {carrier : Set CanaryPhase}
    (hbottom : BottomClass PhaseStep carrier) : CanaryPhase.done ∈ carrier := by
  rcases hbottom.nonempty with ⟨phase, hphase⟩
  cases phase with
  | start =>
      have h1 := hbottom.closed hphase
        (show PhaseStep .start .afterTargetOne from rfl)
      have h2 := hbottom.closed h1
        (show PhaseStep .afterTargetOne .afterDistractorOne from rfl)
      have h3 := hbottom.closed h2
        (show PhaseStep .afterDistractorOne .afterTargetTwo from rfl)
      exact hbottom.closed h3 (show PhaseStep .afterTargetTwo .done from rfl)
  | afterTargetOne =>
      have h2 := hbottom.closed hphase
        (show PhaseStep .afterTargetOne .afterDistractorOne from rfl)
      have h3 := hbottom.closed h2
        (show PhaseStep .afterDistractorOne .afterTargetTwo from rfl)
      exact hbottom.closed h3 (show PhaseStep .afterTargetTwo .done from rfl)
  | afterDistractorOne =>
      have h3 := hbottom.closed hphase
        (show PhaseStep .afterDistractorOne .afterTargetTwo from rfl)
      exact hbottom.closed h3 (show PhaseStep .afterTargetTwo .done from rfl)
  | afterTargetTwo =>
      exact hbottom.closed hphase (show PhaseStep .afterTargetTwo .done from rfl)
  | done => exact hphase

theorem bottomClass_eq_doneClass {carrier : Set CanaryPhase}
    (hbottom : BottomClass PhaseStep carrier) : carrier = doneClass := by
  have hdone := done_mem_of_bottomClass hbottom
  ext phase
  constructor
  · intro hphase
    have hreach := hbottom.stronglyConnected hdone hphase
    have heq := reachable_from_done_eq_done hreach
    change phase = CanaryPhase.done
    exact heq
  · intro hphase
    change phase = CanaryPhase.done at hphase
    subst phase
    exact hdone

theorem shipped_done_fails : ¬ ShippedGood .done := by
  exact shippedChoiceLearner_fails_of_protocol rewardedChoiceEpisode
    rewardedChoiceEpisode_satisfies_protocol

theorem rewardSensitive_done_succeeds : RewardSensitiveGood .done := by
  exact rewardSensitiveChoiceLearner_succeeds_of_protocol rewardedChoiceEpisode
    rewardedChoiceEpisode_satisfies_protocol

/-- Exact finite negative verdict for the shipped rule. -/
theorem shipped_canary_not_bottomAdmissible :
    ¬ BottomAdmissible PhaseStep .start ShippedGood := by
  intro hadmit
  have hgood := hadmit doneClass doneClass_bottom doneClass_reachable
    (state := CanaryPhase.done) rfl
  exact shipped_done_fails hgood

/-- Exact finite positive verdict for the reward-sensitive local control. -/
theorem rewardSensitive_canary_bottomAdmissible :
    BottomAdmissible PhaseStep .start RewardSensitiveGood := by
  intro carrier hbottom _ state hstate
  have hcarrier := bottomClass_eq_doneClass hbottom
  rw [hcarrier] at hstate
  have hdone : state = CanaryPhase.done := by simpa [doneClass] using hstate
  subst state
  exact rewardSensitive_done_succeeds

/-- The make-or-break pair on one finite support graph. -/
theorem canary_admission_separates_rules :
    (¬ BottomAdmissible PhaseStep .start ShippedGood) ∧
      BottomAdmissible PhaseStep .start RewardSensitiveGood :=
  ⟨shipped_canary_not_bottomAdmissible, rewardSensitive_canary_bottomAdmissible⟩

#print axioms bottomClass_eq_doneClass
#print axioms shipped_canary_not_bottomAdmissible
#print axioms rewardSensitive_canary_bottomAdmissible
#print axioms canary_admission_separates_rules

end WeightedGSLTCanaryAdmission
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
