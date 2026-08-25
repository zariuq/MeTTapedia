import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.TopDownTraceLegality

/-!
# Verifier-certified hindsight replay

Replay evidence is an atomic provenance fact.  Root-normalized weighting,
target-first sampling, and importance correction are proved separately so that
none of their support assumptions are hidden in an aggregate count.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe uQ uP uT uR uC uS uA

/-- One checker-certified state-to-action fact with its complete provenance. -/
structure VerifiedReplayFact
    (Query : Type uQ) (Program : Type uP) (Target : Type uT)
    (Receipt : Type uR) (CausalRoot : Type uC)
    (State : Type uS) (Action : Type uA) where
  query : Query
  program : Program
  solvedTarget : Target
  checkerReceipt : Receipt
  causalRoot : CausalRoot
  state : State
  nextAction : Action
  deriving DecidableEq, Repr

section RootWeighting

variable {Fact Root Action : Type*} [DecidableEq Root]

/-- Number of records attributed to one causal root. -/
def causalRootCount
    (rootOf : Fact → Root) (records : List Fact) (root : Root) : ℕ :=
  (records.filter fun record ↦ rootOf record = root).length

/-- Runtime-compatible per-record weight: reciprocal record count of the
record's causal root. -/
noncomputable def reciprocalRootWeight
    (rootOf : Fact → Root) (records : List Fact) (record : Fact) : ℚ :=
  if causalRootCount rootOf records (rootOf record) = 0 then 0
  else (causalRootCount rootOf records (rootOf record) : ℚ)⁻¹

/-- Total uniform weight assigned to a root. -/
noncomputable def causalRootMass
    (rootOf : Fact → Root) (records : List Fact) (root : Root) : ℚ :=
  (causalRootCount rootOf records root : ℚ) *
    (if causalRootCount rootOf records root = 0 then 0
      else (causalRootCount rootOf records root : ℚ)⁻¹)

/-- Every represented causal root contributes exactly one unit. -/
theorem causalRootMass_eq_one
    (rootOf : Fact → Root) (records : List Fact) (root : Root)
    (represented : 0 < causalRootCount rootOf records root) :
    causalRootMass rootOf records root = 1 := by
  have countNonzero : causalRootCount rootOf records root ≠ 0 :=
    Nat.ne_of_gt represented
  have castNonzero : (causalRootCount rootOf records root : ℚ) ≠ 0 := by
    exact_mod_cast countNonzero
  simp [causalRootMass, countNonzero, castNonzero]

/-- Cloning one record cannot inflate its root's *total* mass, provided that
root was already represented. -/
theorem causalRootMass_duplicate_record_invariant
    (rootOf : Fact → Root) (records : List Fact) (record : Fact)
    (represented : 0 < causalRootCount rootOf records (rootOf record)) :
    causalRootMass rootOf (record :: records) (rootOf record) =
      causalRootMass rootOf records (rootOf record) := by
  rw [causalRootMass_eq_one rootOf records (rootOf record) represented]
  apply causalRootMass_eq_one
  simp [causalRootCount]

/-- Within-root action mass exposes the finer distribution that total root
normalization does not identify. -/
noncomputable def causalRootActionMass
    [DecidableEq Action]
    (rootOf : Fact → Root) (actionOf : Fact → Action)
    (records : List Fact) (root : Root) (action : Action) : ℚ :=
  let rootCount := causalRootCount rootOf records root
  let actionCount :=
    (records.filter fun record ↦
      rootOf record = root ∧ actionOf record = action).length
  if rootCount = 0 then 0 else (actionCount : ℚ) / rootCount

structure RootActionFixture where
  root : Bool
  action : Bool
  deriving DecidableEq, Repr

def balancedRootRecords : List RootActionFixture :=
  [⟨false, false⟩, ⟨false, true⟩]

def partiallyClonedRootRecords : List RootActionFixture :=
  ⟨false, false⟩ :: balancedRootRecords

/-- Root-mass clone invariance does not imply invariance of the within-root
action histogram under duplicating only one action record. -/
theorem partial_record_clone_changes_action_distribution :
    causalRootActionMass RootActionFixture.root RootActionFixture.action
        balancedRootRecords false false = 1 / 2 ∧
      causalRootActionMass RootActionFixture.root RootActionFixture.action
        partiallyClonedRootRecords false false = 2 / 3 := by
  norm_num [causalRootActionMass, causalRootCount, balancedRootRecords,
    partiallyClonedRootRecords]

end RootWeighting

/-! ## Target-first hierarchical sampling -/

section TargetFirst

variable {Target Root Fact : Type*}

/-- A finite target-first sampling space with every conditional support
explicitly nonempty. -/
structure TargetFirstSamplingPlan where
  targets : Finset Target
  roots : Target → Finset Root
  facts : Target → Root → Finset Fact
  targets_nonempty : targets.Nonempty
  roots_nonempty : ∀ target ∈ targets, (roots target).Nonempty
  facts_nonempty : ∀ target ∈ targets, ∀ root ∈ roots target,
    (facts target root).Nonempty

namespace TargetFirstSamplingPlan

/-- Probability of one `(target, root, fact)` atom under uniform sampling at
each hierarchy level. -/
noncomputable def atomProbability
    (plan : TargetFirstSamplingPlan (Target := Target) (Root := Root)
      (Fact := Fact))
  (target : Target) (root : Root) : ℚ :=
  (plan.targets.card : ℚ)⁻¹ *
    ((plan.roots target).card : ℚ)⁻¹ *
    ((plan.facts target root).card : ℚ)⁻¹

theorem target_card_pos
    (plan : TargetFirstSamplingPlan (Target := Target) (Root := Root)
      (Fact := Fact)) :
    0 < plan.targets.card :=
  Finset.card_pos.mpr plan.targets_nonempty

theorem root_card_pos
    (plan : TargetFirstSamplingPlan (Target := Target) (Root := Root)
      (Fact := Fact))
    {target : Target} (targetMember : target ∈ plan.targets) :
    0 < (plan.roots target).card :=
  Finset.card_pos.mpr (plan.roots_nonempty target targetMember)

theorem fact_card_pos
    (plan : TargetFirstSamplingPlan (Target := Target) (Root := Root)
      (Fact := Fact))
    {target : Target} (targetMember : target ∈ plan.targets)
    {root : Root} (rootMember : root ∈ plan.roots target) :
    0 < (plan.facts target root).card :=
  Finset.card_pos.mpr
    (plan.facts_nonempty target targetMember root rootMember)

/-- Target choices retain membership evidence, so conditional supports are
available without inventing defaults outside the target support. -/
def TargetChoice
    (plan : TargetFirstSamplingPlan (Target := Target) (Root := Root)
      (Fact := Fact)) :=
  { target // target ∈ plan.targets }

def RootChoice
    (plan : TargetFirstSamplingPlan (Target := Target) (Root := Root)
      (Fact := Fact))
    (target : plan.TargetChoice) :=
  { root // root ∈ plan.roots target.1 }

def FactChoice
    (plan : TargetFirstSamplingPlan (Target := Target) (Root := Root)
      (Fact := Fact))
    (target : plan.TargetChoice) (root : plan.RootChoice target) :=
  { fact // fact ∈ plan.facts target.1 root.1 }

def SampleSpace
    (plan : TargetFirstSamplingPlan (Target := Target) (Root := Root)
      (Fact := Fact)) :=
  Σ target : plan.TargetChoice,
    Σ root : plan.RootChoice target, plan.FactChoice target root

/-- Target-first hierarchical sampling is a genuine PMF.  The dependent
support types make every conditional uniform distribution nonempty. -/
noncomputable def sampler
    (plan : TargetFirstSamplingPlan (Target := Target) (Root := Root)
      (Fact := Fact)) :
    PMF plan.SampleSpace := by
  classical
  let targetWitness := plan.targets_nonempty
  letI : Fintype plan.TargetChoice :=
    Fintype.ofFinset plan.targets.attach (fun target ↦ by simp)
  letI : Nonempty plan.TargetChoice :=
    ⟨⟨targetWitness.choose, targetWitness.choose_spec⟩⟩
  exact (PMF.uniformOfFintype plan.TargetChoice).bind fun target => by
    let rootWitness := plan.roots_nonempty target.1 target.2
    letI : Fintype (plan.RootChoice target) :=
      Fintype.ofFinset (plan.roots target.1).attach
        (fun root ↦ by simp)
    letI : Nonempty (plan.RootChoice target) :=
      ⟨⟨rootWitness.choose, rootWitness.choose_spec⟩⟩
    exact (PMF.uniformOfFintype (plan.RootChoice target)).bind fun root => by
      let factWitness := plan.facts_nonempty target.1 target.2 root.1 root.2
      letI : Fintype (plan.FactChoice target root) :=
        Fintype.ofFinset (plan.facts target.1 root.1).attach
          (fun fact ↦ by simp)
      letI : Nonempty (plan.FactChoice target root) :=
        ⟨⟨factWitness.choose, factWitness.choose_spec⟩⟩
      exact (PMF.uniformOfFintype (plan.FactChoice target root)).map fun fact =>
        ⟨target, root, fact⟩

/-- The hierarchy's assumptions construct an inhabited joint sample space. -/
theorem sampleSpace_nonempty
    (plan : TargetFirstSamplingPlan (Target := Target) (Root := Root)
      (Fact := Fact)) :
    Nonempty plan.SampleSpace := by
  let targetWitness := plan.targets_nonempty
  let target : plan.TargetChoice :=
    ⟨targetWitness.choose, targetWitness.choose_spec⟩
  let rootWitness := plan.roots_nonempty target.1 target.2
  let root : plan.RootChoice target :=
    ⟨rootWitness.choose, rootWitness.choose_spec⟩
  let factWitness := plan.facts_nonempty target.1 target.2 root.1 root.2
  exact ⟨⟨target, root, ⟨factWitness.choose, factWitness.choose_spec⟩⟩⟩

end TargetFirstSamplingPlan

end TargetFirst

/-! ## Importance correction and its support boundary -/

section Importance

variable {Atom : Type*} [Fintype Atom]

/-- Positive proposal support licenses the usual exact importance correction. -/
theorem importanceCorrection_exact
    (target proposal value : Atom → ℚ)
    (positiveSupport : ∀ atom, proposal atom ≠ 0) :
    ∑ atom, proposal atom * ((target atom / proposal atom) * value atom) =
      ∑ atom, target atom * value atom := by
  apply Finset.sum_congr rfl
  intro atom _
  field_simp [positiveSupport atom]

def missingSupportTarget : Bool → ℚ
  | false => 1
  | true => 0

def missingSupportProposal : Bool → ℚ
  | false => 0
  | true => 1

/-- If the proposal assigns zero mass to a target-positive atom, no finite
importance weight can reconstruct that atom's target contribution. -/
theorem importanceCorrection_impossible_without_support :
    ¬ ∃ weight : Bool → ℚ,
      missingSupportProposal false * weight false =
        missingSupportTarget false := by
  norm_num [missingSupportProposal, missingSupportTarget]

end Importance

/-! ## Checker validity is not training utility -/

structure ReplayUsefulnessFixture where
  checkerAccepted : Bool
  trainingUtility : ℤ
  deriving DecidableEq, Repr

def validButHarmfulReplay : ReplayUsefulnessFixture :=
  ⟨true, -1⟩

/-- A checker receipt proves semantic validity of the program/target edge; it
does not prove that replaying the associated action improves the learner. -/
theorem checker_valid_does_not_imply_useful_fixture :
    validButHarmfulReplay.checkerAccepted = true ∧
      validButHarmfulReplay.trainingUtility < 0 := by
  decide

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
