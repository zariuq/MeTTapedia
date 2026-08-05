import Mettapedia.MachineLearning.SearchGuidance.BudgetedCoverageCrown

/-!
# Witness-preserving program-discovery kernel

Checker-backed synthesis produces occurrences, not merely a set of solved
targets.  The raw ledger is therefore a multiset.  Target coverage, distinct
programs, and distinct program-target edges are non-destructive projections of
that ledger.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe uP uT uM uA uW uL

/-- The semantic solve relation supplied by a checker. -/
def Solves {Program : Type uP} {Target : Type uT}
    (checker : Program → Target → Prop) (program : Program) (target : Target) : Prop :=
  checker program target

/-- One authenticated occurrence in a bounded program-discovery run. -/
structure CheckedObservation
    (Program : Type uP) (Target : Type uT)
    (Model : Type uM) (Arm : Type uA) (World : Type uW)
    (Lineage : Type uL) (checker : Program → Target → Prop) where
  program : Program
  target : Target
  model : Model
  arm : Arm
  world : World
  generation : ℕ
  lineage : Lineage
  searchBudget : ℕ
  measuredRuntime : Option ℕ
  programSize : ℕ
  checked : Solves checker program target

/-- The raw discovery ledger.  Multiplicity is intentional: exact repeated
occurrences must remain distinguishable from distinct witnesses. -/
abbrev DiscoveryLedger
    (Program : Type uP) (Target : Type uT)
    (Model : Type uM) (Arm : Type uA) (World : Type uW)
    (Lineage : Type uL) (checker : Program → Target → Prop) :=
  Multiset (CheckedObservation Program Target Model Arm World Lineage checker)

namespace CheckedObservation

variable {Program : Type uP} {Target : Type uT}
variable {Model : Type uM} {Arm : Type uA} {World : Type uW}
variable {Lineage : Type uL} {checker : Program → Target → Prop}

def edge
    (observation : CheckedObservation Program Target Model Arm World Lineage checker) :
    Program × Target :=
  (observation.program, observation.target)

end CheckedObservation

section Projections

variable {Program : Type uP} {Target : Type uT}
variable {Model : Type uM} {Arm : Type uA} {World : Type uW}
variable {Lineage : Type uL} {checker : Program → Target → Prop}

local notation "LedgerT" =>
  DiscoveryLedger Program Target Model Arm World Lineage checker
local notation "ObservationT" =>
  CheckedObservation Program Target Model Arm World Lineage checker

/-- Targets covered by at least one authenticated occurrence. -/
noncomputable def coveredTargets (ledger : LedgerT) : Finset Target := by
  classical
  exact (ledger.map (fun observation ↦ observation.target)).toFinset

/-- Distinct programs occurring anywhere in the ledger. -/
noncomputable def distinctPrograms (ledger : LedgerT) : Finset Program := by
  classical
  exact (ledger.map (fun observation ↦ observation.program)).toFinset

/-- Distinct programs witnessing one declared target. -/
noncomputable def witnessPrograms (ledger : LedgerT) (target : Target) : Finset Program := by
  classical
  exact ((ledger.filter (fun observation ↦ observation.target = target)).map
    (fun observation ↦ observation.program)).toFinset

/-- Distinct authenticated program-target edges. -/
noncomputable def distinctEdges (ledger : LedgerT) : Finset (Program × Target) := by
  classical
  exact (ledger.map CheckedObservation.edge).toFinset

/-- Raw occurrences of one exact program-target edge. -/
noncomputable def occurrenceCount
    (ledger : LedgerT) (program : Program) (target : Target) : ℕ := by
  classical
  exact ledger.countP (fun observation ↦
    observation.program = program ∧ observation.target = target)

/-- A first observation is meaningful only relative to an explicit source
lineage.  It is the earliest generation of the same program-target claim in
that lineage. -/
def FirstInLineage (ledger : LedgerT) (observation : ObservationT) : Prop :=
  observation ∈ ledger ∧
    ∀ earlier ∈ ledger,
      earlier.lineage = observation.lineage →
      earlier.program = observation.program →
      earlier.target = observation.target →
      observation.generation ≤ earlier.generation

theorem checked_observation_solves (observation : ObservationT) :
    Solves checker observation.program observation.target :=
  observation.checked

theorem mem_coveredTargets_iff (ledger : LedgerT) (target : Target) :
    target ∈ coveredTargets ledger ↔ ∃ observation ∈ ledger, observation.target = target := by
  classical
  simp [coveredTargets]

theorem mem_witnessPrograms_iff (ledger : LedgerT) (program : Program) (target : Target) :
    program ∈ witnessPrograms ledger target ↔
      ∃ observation ∈ ledger,
        observation.target = target ∧ observation.program = program := by
  classical
  simp [witnessPrograms, and_left_comm, and_assoc]

theorem mem_distinctEdges_iff (ledger : LedgerT) (program : Program) (target : Target) :
    (program, target) ∈ distinctEdges ledger ↔
      ∃ observation ∈ ledger,
        observation.program = program ∧ observation.target = target := by
  classical
  simp [distinctEdges, CheckedObservation.edge, Prod.ext_iff]

/-- Projecting to targets preserves exactly the question "was this target
covered?" -/
theorem target_projection_preserves_coverage (ledger : LedgerT) (target : Target) :
    target ∈ coveredTargets ledger ↔ ∃ program, (program, target) ∈ distinctEdges ledger := by
  classical
  rw [mem_coveredTargets_iff]
  constructor
  · rintro ⟨observation, hmem, rfl⟩
    exact ⟨observation.program, (mem_distinctEdges_iff ledger _ _).2
      ⟨observation, hmem, rfl, rfl⟩⟩
  · rintro ⟨program, hedge⟩
    rcases (mem_distinctEdges_iff ledger program target).1 hedge with
      ⟨observation, hmem, _hprogram, htarget⟩
    exact ⟨observation, hmem, htarget⟩

/-- Extending a raw ledger can only extend target coverage. -/
theorem coveredTargets_mono {earlier later : LedgerT} (h : earlier ≤ later) :
    coveredTargets earlier ⊆ coveredTargets later := by
  classical
  intro target htarget
  rcases (mem_coveredTargets_iff earlier target).1 htarget with ⟨observation, hmem, rfl⟩
  exact (mem_coveredTargets_iff later observation.target).2
    ⟨observation, Multiset.mem_of_le h hmem, rfl⟩

end Projections

/-! ## Finite positive and negative fixtures -/

namespace Fixtures

inductive Program where
  | alpha
  | beta
  deriving DecidableEq, Repr

inductive Target where
  | first
  | second
  deriving DecidableEq, Repr

/-- `alpha` covers both targets; `beta` is a distinct witness for `first`. -/
def checker : Program → Target → Prop
  | .alpha, _ => True
  | .beta, .first => True
  | .beta, .second => False

abbrev Observation := CheckedObservation Program Target Bool Bool Bool ℕ checker
abbrev Ledger := DiscoveryLedger Program Target Bool Bool Bool ℕ checker

def alphaFirst : Observation where
  program := .alpha
  target := .first
  model := false
  arm := false
  world := false
  generation := 1
  lineage := 10
  searchBudget := 100
  measuredRuntime := some 8
  programSize := 2
  checked := trivial

def betaFirst : Observation where
  program := .beta
  target := .first
  model := true
  arm := true
  world := false
  generation := 1
  lineage := 11
  searchBudget := 100
  measuredRuntime := some 5
  programSize := 3
  checked := trivial

def alphaSecond : Observation where
  program := .alpha
  target := .second
  model := false
  arm := false
  world := false
  generation := 2
  lineage := 10
  searchBudget := 100
  measuredRuntime := some 7
  programSize := 2
  checked := trivial

def twoProgramsOneTarget : Ledger :=
  alphaFirst ::ₘ betaFirst ::ₘ 0

def repeatedExactProgram : Ledger :=
  alphaFirst ::ₘ alphaFirst ::ₘ 0

def oneProgramManyTargets : Ledger :=
  alphaFirst ::ₘ alphaSecond ::ₘ 0

/-- Positive fixture: two syntactically different accepted programs remain two
distinct witnesses for one target. -/
theorem two_programs_one_target :
    witnessPrograms twoProgramsOneTarget .first = {.alpha, .beta} ∧
      (coveredTargets twoProgramsOneTarget).card = 1 ∧
      (distinctEdges twoProgramsOneTarget).card = 2 := by
  classical
  constructor
  · ext program
    cases program <;>
      simp [mem_witnessPrograms_iff, twoProgramsOneTarget, alphaFirst, betaFirst]
  · simp [coveredTargets, distinctEdges, twoProgramsOneTarget,
      CheckedObservation.edge, alphaFirst, betaFirst]

/-- Negative fixture: repeating one exact witness changes raw multiplicity but
not distinct-program diversity. -/
theorem exact_repeat_changes_occurrences_not_diversity :
    occurrenceCount repeatedExactProgram .alpha .first = 2 ∧
      (distinctPrograms repeatedExactProgram).card = 1 ∧
      (distinctEdges repeatedExactProgram).card = 1 := by
  classical
  constructor
  · unfold occurrenceCount
    rw [repeatedExactProgram]
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    simp [alphaFirst]
  · simp [distinctPrograms, distinctEdges, repeatedExactProgram,
      CheckedObservation.edge, alphaFirst]

/-- One authenticated program may cover more than one target; target evidence
must therefore not be assumed independent merely because the target IDs differ. -/
theorem one_program_many_targets :
    (coveredTargets oneProgramManyTargets).card = 2 ∧
      (distinctPrograms oneProgramManyTargets).card = 1 ∧
      (distinctEdges oneProgramManyTargets).card = 2 := by
  classical
  simp [coveredTargets, distinctPrograms, distinctEdges, oneProgramManyTargets,
    CheckedObservation.edge, alphaFirst, alphaSecond]

/-- The target projection can strictly lose witness diversity. -/
theorem target_projection_strictly_loses_witness_diversity :
    (coveredTargets twoProgramsOneTarget).card <
      (distinctEdges twoProgramsOneTarget).card := by
  classical
  simp [coveredTargets, distinctEdges, twoProgramsOneTarget,
    CheckedObservation.edge, alphaFirst, betaFirst]

theorem firstInLineage_of_minimal_index :
    FirstInLineage twoProgramsOneTarget alphaFirst := by
  simp [FirstInLineage, twoProgramsOneTarget, alphaFirst, betaFirst]

end Fixtures

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
