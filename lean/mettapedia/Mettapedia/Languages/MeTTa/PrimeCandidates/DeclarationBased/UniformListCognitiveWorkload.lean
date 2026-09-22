import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListChartNIKService
import Mettapedia.Logic.HOL.UniformListInductionRevisionViews

/-!
# Bounded learning, proof import and revision reuse of one uniform HOL claim

A finite count-expression grammar generates higher-order list hypotheses.
Actual function/list samples filter those hypotheses but provide no proof
authority. The retained input-length hypothesis is the original map-length
sentence. Submitted chart certificates reconstruct that sentence under its
explicit induction theory; current reuse additionally checks the same proof's
conservative premise dependencies.

The grammar is deliberately bounded, not general higher-order ILP. The junk
model refutes the equations-only claim and fails the full induction theory.
Recognition misses, malformed certificates and stale dependencies are not
countermodels. Intrinsic HOL proofs remain distinct from native dependent
proof inhabitants and from unchecked external proof bytes.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace UniformListCognitiveWorkload

open Mettapedia.Logic HOL HOL.UniformListInduction
open HOL.UniformListInductionChart HOL.GroundUnaryEquationalChart
open HOL.UniformListInductionRevisionViews
open Mettapedia.Machines Mettapedia.GSLT.Dynamics

local instance : DecidableEq BaseSort
  | .element, .element | .sequence, .sequence | .count, .count => .isTrue rfl
  | .element, .sequence | .element, .count | .sequence, .element
  | .sequence, .count | .count, .element | .count, .sequence =>
      .isFalse (by intro equal; cases equal)

local instance (τ : HOL.Ty BaseSort) : DecidableEq (Symbol τ) := by
  intro left right
  cases left <;> cases right <;> exact .isTrue rfl

/-! ## Generic enumeration and sample-consumer laws -/

section Filtering

variable {Hypothesis Observation : Type}

def sampleFilter (test : Hypothesis → Observation → Bool)
    (samples : List Observation) (candidates : List Hypothesis) : List Hypothesis :=
  candidates.filter fun candidate => samples.all (test candidate)

theorem mem_sampleFilter (test : Hypothesis → Observation → Bool)
    (samples : List Observation) (candidates : List Hypothesis) (candidate : Hypothesis) :
    candidate ∈ sampleFilter test samples candidates ↔
      candidate ∈ candidates ∧ ∀ sample ∈ samples, test candidate sample = true := by
  simp only [sampleFilter, List.mem_filter, List.all_eq_true]

/-- Additional observations only remove candidates; they never manufacture
an unenumerated candidate or turn a sample test into a proof checker. -/
theorem sampleFilter_append (test : Hypothesis → Observation → Bool)
    (first later : List Observation) (candidates : List Hypothesis) :
    sampleFilter test (first ++ later) candidates =
      sampleFilter test later (sampleFilter test first candidates) := by
  simp only [sampleFilter, List.all_append, List.filter_filter]
  congr 1
  funext candidate
  exact Bool.and_comm _ _

end Filtering

/-! ## Actual count-expression generation and HOL interpretation -/

inductive CountExpression where
  | zero
  | inputLength
  | successor (body : CountExpression)
  deriving DecidableEq, Repr

namespace CountExpression

def depth : CountExpression → Nat
  | .zero | .inputLength => 0
  | .successor body => body.depth + 1

def enumerate : Nat → List CountExpression
  | 0 => []
  | fuel + 1 => [.zero, .inputLength] ++ (enumerate fuel).map .successor

theorem mem_enumerate (fuel : Nat) (expression : CountExpression) :
    expression ∈ enumerate fuel ↔ expression.depth < fuel := by
  induction fuel generalizing expression with
  | zero => simp [enumerate]
  | succ fuel ih =>
      cases expression <;> simp [enumerate, depth, ih]

/-- Compile into the existing count sort and list-length symbol. -/
def compile {Γ : HOL.Ctx BaseSort} (xs : Expr Γ sequence) : CountExpression → Expr Γ count
  | .zero => .const .zero
  | .inputLength => length xs
  | .successor body => succ (compile xs body)

end CountExpression

structure Sample where
  function : Bool → Bool
  values : List Bool

def evaluate : CountExpression → Sample → Nat
  | .zero, _ => 0
  | .inputLength, sample => sample.values.length
  | .successor body, sample => Nat.succ (evaluate body sample)

def fits (expression : CountExpression) (sample : Sample) : Bool :=
  decide ((sample.values.map sample.function).length = evaluate expression sample)

def sampleFormula (expression : CountExpression) : Sentence [sequence, mapping] :=
  .eq (length (map (.var (.vs .vz)) (.var .vz)))
    (expression.compile (.var .vz))

/-- Functions remain universally quantified in the retained source sentence. -/
def hypothesis (expression : CountExpression) : Sentence [] :=
  .all (.all (sampleFormula expression))

theorem inputLength_is_mapLength : hypothesis .inputLength = mapLength := rfl

def sampleValuation (sample : Sample) : StandardListModel.model.Valuation [sequence, mapping] :=
  fun {_} index => match index with
    | .vz => ⟨sample.values⟩
    | .vs .vz => fun value => ⟨sample.function value.down⟩
    | .vs (.vs impossible) => nomatch impossible

/-- The executable sample evaluator agrees with the actual HOL interpretation,
not an independently assigned score for each hypothesis constructor. -/
theorem evaluate_denote (expression : CountExpression) (sample : Sample) :
    StandardListModel.model.denote (expression.compile (.var .vz)) (sampleValuation sample) =
      (ULift.up (evaluate expression sample) : StandardListModel.LiftedCount) := by
  induction expression with
  | zero => rfl
  | inputLength => rfl
  | successor body ih => exact congrArg (fun value => ULift.up (Nat.succ value.down)) ih

theorem fits_iff_denote (expression : CountExpression) (sample : Sample) :
    fits expression sample = true ↔
      (StandardListModel.model.denote (sampleFormula expression) (sampleValuation sample)).down := by
  rw [fits, decide_eq_true_eq]
  change (sample.values.map sample.function).length = evaluate expression sample ↔
    (ULift.up (sample.values.map sample.function).length : StandardListModel.LiftedCount) =
      StandardListModel.model.denote (expression.compile (.var .vz)) (sampleValuation sample)
  rw [evaluate_denote]
  simp only [ULift.up.injEq]

def survivors (fuel : Nat) (samples : List Sample) : List CountExpression :=
  sampleFilter fits samples (CountExpression.enumerate fuel)

theorem mem_survivors (fuel : Nat) (samples : List Sample) (expression : CountExpression) :
    expression ∈ survivors fuel samples ↔
      expression.depth < fuel ∧ ∀ sample ∈ samples, fits expression sample = true := by
  rw [survivors, mem_sampleFilter, CountExpression.mem_enumerate]

theorem inputLength_fits (sample : Sample) : fits .inputLength sample = true := by
  simp [fits, evaluate]

theorem inputLength_survives (fuel : Nat) (positive : 0 < fuel) (samples : List Sample) :
    .inputLength ∈ survivors fuel samples :=
  (mem_survivors _ _ _).mpr ⟨positive, fun sample _ => inputLength_fits sample⟩

def emptySample : Sample := ⟨id, []⟩
def nonemptySample : Sample := ⟨Bool.not, [false]⟩

theorem empty_sample_underdetermines : survivors 1 [emptySample] = [.zero, .inputLength] := rfl

theorem nonempty_sample_eliminates_zero :
    survivors 1 [emptySample, nonemptySample] = [.inputLength] := rfl

theorem zero_overfits : fits .zero emptySample = true ∧ fits .zero nonemptySample = false :=
  ⟨rfl, rfl⟩

/-! ## Assumption-indexed model discrimination -/

def Refutes (model : HenkinModel BaseSort Symbol)
    (claim : UniformListChartNIKService.SourceClaim []) : Prop :=
  (∀ formula ∈ claim.1, model.models formula) ∧ ¬ model.models claim.2

/-- The ordinary full-theory model refutes the overfitted zero hypothesis,
not the distinct uniform input-length hypothesis. -/
theorem standard_refutes_zero : Refutes StandardListModel.model (theory, hypothesis .zero) := by
  refine ⟨StandardListModel.theory_valid, ?_⟩
  intro valid
  have impossible := valid (fun value => value) trivial ⟨[false]⟩ trivial
  change (ULift.up 1 : StandardListModel.LiftedCount) = ULift.up 0 at impossible
  exact Nat.one_ne_zero (congrArg ULift.down impossible)

theorem junk_refutes_equations_claim : Refutes JunkModel.model (equations, hypothesis .inputLength) :=
  ⟨JunkModel.equations_valid, JunkModel.mapLength_invalid⟩

theorem junk_not_full_theory_countermodel :
    ¬ Refutes JunkModel.model (theory, hypothesis .inputLength) := by
  intro refutes
  exact JunkModel.induction_invalid (refutes.1 _ (by simp [theory]))

theorem standard_full_theory_and_claim :
    (∀ formula ∈ theory (Γ := []), StandardListModel.model.models formula) ∧
      StandardListModel.model.models (hypothesis .inputLength) :=
  ⟨StandardListModel.theory_valid, StandardListModel.mapLength_valid⟩

/-- Every finite standard sample set can retain the exact hypothesis while
the weaker equations-only source claim has no object-HOL proof. -/
theorem samples_do_not_supply_induction (fuel : Nat) (positive : 0 < fuel) (samples : List Sample) :
    .inputLength ∈ survivors fuel samples ∧
      ¬ ExtDerivation Symbol equations (hypothesis .inputLength) :=
  ⟨inputLength_survives fuel positive samples, equations_do_not_derive_mapLength⟩

/-! ## Submitted proof consumption and dependency-qualified reuse -/

def dependenciesCurrent {Store Revision : Type} [DecidableEq Store] [DecidableEq Revision]
    (environment : RevisionEnvironment Store Revision)
    (dependencies : RevisionDependencySet Store Revision) : Bool :=
  decide (∀ occurrence ∈ dependencies,
    environment.current occurrence.read.storeId = occurrence.read.revision)

theorem dependenciesCurrent_iff {Store Revision : Type}
    [DecidableEq Store] [DecidableEq Revision]
    (environment : RevisionEnvironment Store Revision)
    (dependencies : RevisionDependencySet Store Revision) :
    dependenciesCurrent environment dependencies = true ↔
      RevisionDependencySet.ValidAt environment dependencies := by
  simp only [dependenciesCurrent, decide_eq_true_eq, RevisionDependencySet.ValidAt]

/-- These are the actual original cons-step premise occurrences. The full
source assumption list remains separately bound by the submitted claim. -/
def proofDependencies : RevisionDependencySet Nat Nat :=
  premiseDependencies (Induction.stepStore [] 0)

def recognized (fuel : Nat) (request : UniformListChartNIKService.ReplayRequest []) : Bool :=
  (reifyAssumptions (stepChart []) fuel request.stepPremises).isSome &&
    eligible (stepChart []) fuel (stepGoal [])

inductive Consumption where
  | generationMiss
  | sampleRejected
  | claimMismatch
  | recognitionMiss
  | proofRejected
  | current (proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject)
  | historical (proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject)

/-- Reconstruct the submitted chart leaves first. A historical result still
contains that admitted proof; invalidation changes its reuse status only. -/
def importStatus (environment : RevisionEnvironment Nat Nat)
    (request : UniformListChartNIKService.ReplayRequest []) : Consumption :=
  match UniformListChartNIKService.produce? [] request with
  | none => .proofRejected
  | some proof =>
      if dependenciesCurrent environment proofDependencies then .current proof else .historical proof

theorem importStatus_current_iff (environment : RevisionEnvironment Nat Nat)
    (request : UniformListChartNIKService.ReplayRequest [])
    (proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject) :
    importStatus environment request = .current proof ↔
      UniformListChartNIKService.produce? [] request = some proof ∧
      RevisionDependencySet.ValidAt environment proofDependencies := by
  rw [← dependenciesCurrent_iff]
  cases produced : UniformListChartNIKService.produce? [] request <;>
    by_cases current : dependenciesCurrent environment proofDependencies = true <;>
    simp [importStatus, produced, current]

theorem importStatus_historical_iff (environment : RevisionEnvironment Nat Nat)
    (request : UniformListChartNIKService.ReplayRequest [])
    (proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject) :
    importStatus environment request = .historical proof ↔
      UniformListChartNIKService.produce? [] request = some proof ∧
      ¬ RevisionDependencySet.ValidAt environment proofDependencies := by
  rw [← dependenciesCurrent_iff]
  cases produced : UniformListChartNIKService.produce? [] request <;>
    by_cases current : dependenciesCurrent environment proofDependencies = true <;>
    simp [importStatus, produced, current]

/-- Generation, observations, source binding, recognition, proof replay and
revision currentness are separate executable checks on this one request. -/
def consume (generationFuel recognitionFuel : Nat) (samples : List Sample)
    (expression : CountExpression) (assumptions : List (Sentence []))
    (request : UniformListChartNIKService.ReplayRequest [])
    (environment : RevisionEnvironment Nat Nat) : Consumption :=
  if expression ∈ CountExpression.enumerate generationFuel then
    if samples.all (fits expression) then
      if request.claim = (assumptions, hypothesis expression) then
        if recognized recognitionFuel request then importStatus environment request
        else .recognitionMiss
      else .claimMismatch
    else .sampleRejected
  else .generationMiss

/-- Enumerate and filter before attempting import for each surviving source
hypothesis. The same submitted proof request is independently bound each time. -/
def learnAndImport (generationFuel recognitionFuel : Nat) (samples : List Sample)
    (assumptions : List (Sentence [])) (request : UniformListChartNIKService.ReplayRequest [])
    (environment : RevisionEnvironment Nat Nat) : List (CountExpression × Consumption) :=
  (survivors generationFuel samples).map fun expression =>
    (expression, consume generationFuel recognitionFuel samples expression assumptions request environment)

theorem mem_learnAndImport (generationFuel recognitionFuel : Nat) (samples : List Sample)
    (assumptions : List (Sentence [])) (request : UniformListChartNIKService.ReplayRequest [])
    (environment : RevisionEnvironment Nat Nat) (expression : CountExpression) (result : Consumption) :
    (expression, result) ∈ learnAndImport generationFuel recognitionFuel samples assumptions request environment ↔
      expression ∈ survivors generationFuel samples ∧
      consume generationFuel recognitionFuel samples expression assumptions request environment = result := by
  simp only [learnAndImport, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨found, member, rfl, same⟩
    exact ⟨member, same⟩
  · rintro ⟨member, same⟩
    exact ⟨expression, member, rfl, same⟩

private theorem survivor_membership (fuel : Nat) (samples : List Sample)
    (expression : CountExpression) :
    expression ∈ survivors fuel samples ↔
      expression ∈ CountExpression.enumerate fuel ∧ samples.all (fits expression) = true :=
  List.mem_filter

theorem consume_current_iff (generationFuel recognitionFuel : Nat) (samples : List Sample)
    (expression : CountExpression) (assumptions : List (Sentence []))
    (request : UniformListChartNIKService.ReplayRequest [])
    (environment : RevisionEnvironment Nat Nat)
    (proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject) :
    consume generationFuel recognitionFuel samples expression assumptions request environment =
        .current proof ↔
      expression ∈ survivors generationFuel samples ∧
      request.claim = (assumptions, hypothesis expression) ∧
      recognized recognitionFuel request = true ∧
      UniformListChartNIKService.produce? [] request = some proof ∧
      RevisionDependencySet.ValidAt environment proofDependencies := by
  rw [survivor_membership]
  unfold consume
  split_ifs <;> simp_all [importStatus_current_iff]

theorem consume_historical_iff (generationFuel recognitionFuel : Nat) (samples : List Sample)
    (expression : CountExpression) (assumptions : List (Sentence []))
    (request : UniformListChartNIKService.ReplayRequest [])
    (environment : RevisionEnvironment Nat Nat)
    (proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject) :
    consume generationFuel recognitionFuel samples expression assumptions request environment =
        .historical proof ↔
      expression ∈ survivors generationFuel samples ∧
      request.claim = (assumptions, hypothesis expression) ∧
      recognized recognitionFuel request = true ∧
      UniformListChartNIKService.produce? [] request = some proof ∧
      ¬ RevisionDependencySet.ValidAt environment proofDependencies := by
  rw [survivor_membership]
  unfold consume
  split_ifs <;> simp_all [importStatus_historical_iff]

/-- Both imported statuses retain derivability of the generated formula
under its exact submitted assumptions; only currentness differs. -/
theorem consumed_proof_derivation {generationFuel recognitionFuel : Nat} {samples : List Sample}
    {expression : CountExpression} {assumptions : List (Sentence [])}
    {request : UniformListChartNIKService.ReplayRequest []}
    {environment : RevisionEnvironment Nat Nat}
    {proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject}
    (consumed : consume generationFuel recognitionFuel samples expression assumptions request environment =
        .current proof ∨
      consume generationFuel recognitionFuel samples expression assumptions request environment =
        .historical proof) :
    proof.1 = (assumptions, hypothesis expression) ∧
      ExtDerivation Symbol assumptions (hypothesis expression) := by
  have binding : request.claim = (assumptions, hypothesis expression) ∧
      UniformListChartNIKService.produce? [] request = some proof := by
    rcases consumed with current | historical
    · obtain ⟨_, bound, _, produced, _⟩ := (consume_current_iff _ _ _ _ _ _ _ _).mp current
      exact ⟨bound, produced⟩
    · obtain ⟨_, bound, _, produced, _⟩ := (consume_historical_iff _ _ _ _ _ _ _ _).mp historical
      exact ⟨bound, produced⟩
  have same := (UniformListChartNIKService.produce_binds_request [] request proof binding.2).trans binding.1
  exact ⟨same, by simpa only [same] using proof.property⟩

/-- Currentness connects the imported proof's step premises to the actual
live acquisition. Stale fallback is not substituted for current source data. -/
theorem current_import_live_premises {generationFuel recognitionFuel : Nat} {samples : List Sample}
    {expression : CountExpression} {assumptions : List (Sentence [])}
    {request : UniformListChartNIKService.ReplayRequest []}
    {environment : RevisionEnvironment Nat Nat}
    {proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject}
    (consumed : consume generationFuel recognitionFuel samples expression assumptions request environment =
      .current proof) :
    request.stepPremises =
      (Induction.currentAcquisition [] environment).lease.entries.map
        RevisionBoundProgramView.ProgramEntry.source := by
  obtain ⟨_, _, _, produced, valid⟩ := (consume_current_iff _ _ _ _ _ _ _ _).mp consumed
  have accepted := (UniformListChartNIKService.produce_isSome_iff [] request).mp
    (by rw [produced]; rfl)
  have binding := ((UniformListChartNIKService.replayAccepted_iff [] request).mp accepted).2.2.1
  have revision : environment.current 0 = 0 :=
    valid Induction.originalHypothesisOccurrence (Induction.original_hypothesis_dependency [])
  rw [Induction.current_acquisition_sources]
  simpa [Induction.stepPremisesAt, revision] using binding

theorem consumed_native_accepted {generationFuel recognitionFuel : Nat} {samples : List Sample}
    {expression : CountExpression} {assumptions : List (Sentence [])}
    {request : UniformListChartNIKService.ReplayRequest []}
    {environment : RevisionEnvironment Nat Nat}
    {proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject}
    (consumed : consume generationFuel recognitionFuel samples expression assumptions request environment =
        .current proof ∨
      consume generationFuel recognitionFuel samples expression assumptions request environment =
        .historical proof) :
    (UniformListChartNIKService.intrinsicKernel []).decide
      (assumptions, hypothesis expression) proof = true :=
  ((UniformListChartNIKService.intrinsicKernel []).correct _ _).mpr
    (consumed_proof_derivation consumed).1

/-- An actual output of the enumeration/import pipeline carries both its
finite generation/sample provenance and admission of the same source claim. -/
theorem learned_current_sound {generationFuel recognitionFuel : Nat} {samples : List Sample}
    {expression : CountExpression} {assumptions : List (Sentence [])}
    {request : UniformListChartNIKService.ReplayRequest []}
    {environment : RevisionEnvironment Nat Nat}
    {proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject}
    (returned : (expression, Consumption.current proof) ∈
      learnAndImport generationFuel recognitionFuel samples assumptions request environment) :
    expression.depth < generationFuel ∧
      (∀ sample ∈ samples, fits expression sample = true) ∧
      (UniformListChartNIKService.intrinsicKernel []).decide
        (assumptions, hypothesis expression) proof = true ∧
      ExtDerivation Symbol assumptions (hypothesis expression) ∧
      RevisionDependencySet.ValidAt environment proofDependencies := by
  obtain ⟨survived, consumed⟩ := (mem_learnAndImport _ _ _ _ _ _ _ _).mp returned
  obtain ⟨generated, tested⟩ := (mem_survivors _ _ _).mp survived
  have qualified := (consume_current_iff _ _ _ _ _ _ _ _).mp consumed
  exact ⟨generated, tested, consumed_native_accepted (Or.inl consumed),
    (consumed_proof_derivation (Or.inl consumed)).2, qualified.2.2.2.2⟩

/-! ## One connected induction workload and distinct outcomes -/

theorem uniform_import_current (fuel : Nat) (positive : 0 < fuel) (samples : List Sample) :
    consume fuel 2 samples .inputLength theory (UniformListChartNIKService.actualRequest [])
      Induction.initialEnvironment = .current (UniformListChartNIKService.actualNativeProof []) := by
  apply (consume_current_iff _ _ _ _ _ _ _ _).mpr
  exact ⟨inputLength_survives fuel positive samples, rfl, rfl,
    UniformListChartNIKService.actual_produced [], Induction.original_dependencies_current []⟩

theorem learning_imports_mapLength :
    learnAndImport 1 2 [emptySample, nonemptySample] theory
      (UniformListChartNIKService.actualRequest []) Induction.initialEnvironment =
      [(.inputLength, .current (UniformListChartNIKService.actualNativeProof []))] := by
  rw [learnAndImport, nonempty_sample_eliminates_zero]
  simp only [List.map_cons, List.map_nil, uniform_import_current 1 (by decide)]

theorem uniform_import_historical (fuel : Nat) (positive : 0 < fuel) (samples : List Sample) :
    consume fuel 2 samples .inputLength theory (UniformListChartNIKService.actualRequest [])
      (Induction.initialEnvironment.update 0 1) =
        .historical (UniformListChartNIKService.actualNativeProof []) := by
  apply (consume_historical_iff _ _ _ _ _ _ _ _).mpr
  exact ⟨inputLength_survives fuel positive samples, rfl, rfl,
    UniformListChartNIKService.actual_produced [], Induction.consulted_revision_invalidates_dependencies []⟩

theorem unrelated_revision_keeps_current (fuel : Nat) (positive : 0 < fuel)
    (samples : List Sample) (revision : Nat) :
    consume fuel 2 samples .inputLength theory (UniformListChartNIKService.actualRequest [])
      (Induction.initialEnvironment.update 1 revision) =
        .current (UniformListChartNIKService.actualNativeProof []) := by
  apply (consume_current_iff _ _ _ _ _ _ _ _).mpr
  exact ⟨inputLength_survives fuel positive samples, rfl, rfl,
    UniformListChartNIKService.actual_produced [],
    Induction.unrelated_revision_preserves_dependencies [] revision⟩

theorem generation_miss :
    consume 0 2 [emptySample, nonemptySample] .inputLength theory
      (UniformListChartNIKService.actualRequest []) Induction.initialEnvironment = .generationMiss := rfl

theorem recognition_miss :
    consume 1 1 [emptySample, nonemptySample] .inputLength theory
      (UniformListChartNIKService.actualRequest []) Induction.initialEnvironment = .recognitionMiss := rfl

theorem malformed_proof_rejected :
    consume 1 2 [emptySample, nonemptySample] .inputLength theory
      { UniformListChartNIKService.actualRequest [] with stepProof := malformedCertificate [] }
      Induction.initialEnvironment = .proofRejected := rfl

theorem nonempty_sample_rejects_zero :
    consume 1 2 [emptySample, nonemptySample] .zero theory
      { UniformListChartNIKService.actualRequest [] with claim := (theory, hypothesis .zero) }
      Induction.initialEnvironment = .sampleRejected := rfl

/-- Passing the empty-list sample does not import a proof for zero: the
same independent chart reconstruction rejects the changed source formula. -/
theorem overfit_is_not_imported :
    consume 1 2 [emptySample] .zero theory
      { UniformListChartNIKService.actualRequest [] with claim := (theory, hypothesis .zero) }
      Induction.initialEnvironment = .proofRejected := rfl

theorem changed_assumptions_rejected :
    consume 1 2 [emptySample, nonemptySample] .inputLength equations
      { UniformListChartNIKService.actualRequest [] with claim := (equations, mapLength) }
      Induction.initialEnvironment = .proofRejected := rfl

/-- This rules out every submitted proof and either admitted status under
the equations-only assumptions, not merely one unsuccessful proposal. -/
theorem equations_only_cannot_import {generationFuel recognitionFuel : Nat} {samples : List Sample}
    {request : UniformListChartNIKService.ReplayRequest []}
    {environment : RevisionEnvironment Nat Nat}
    (proof : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject) :
    ¬ (consume generationFuel recognitionFuel samples .inputLength equations request environment =
        .current proof ∨
      consume generationFuel recognitionFuel samples .inputLength equations request environment =
        .historical proof) :=
  fun consumed => equations_do_not_derive_mapLength (consumed_proof_derivation consumed).2

/-- Both failures concern the same proved uniform claim. Neither supplies
a countermodel of that claim under the full source theory. -/
theorem bounded_and_malformed_are_not_countermodels :
    consume 1 1 [emptySample, nonemptySample] .inputLength theory
        (UniformListChartNIKService.actualRequest []) Induction.initialEnvironment = .recognitionMiss ∧
      consume 1 2 [emptySample, nonemptySample] .inputLength theory
        { UniformListChartNIKService.actualRequest [] with stepProof := malformedCertificate [] }
        Induction.initialEnvironment = .proofRejected ∧
      ExtDerivation Symbol theory (hypothesis .inputLength) ∧
      ¬ Refutes StandardListModel.model (theory, hypothesis .inputLength) := by
  have imported := uniform_import_current 1 (by decide) [emptySample, nonemptySample]
  exact ⟨recognition_miss, malformed_proof_rejected,
    (consumed_proof_derivation (Or.inl imported)).2,
    fun countermodel => countermodel.2 StandardListModel.mapLength_valid⟩

/-- The exact same generated claim and actual imported proof survive as
historical mathematics. The consulted revision changes reuse status, and
the rebuilt live premise table rejects that proof's original step certificate. -/
theorem revision_connected_workload (fuel : Nat) (positive : 0 < fuel) (samples : List Sample) :
    let request := UniformListChartNIKService.actualRequest []
    let proof := UniformListChartNIKService.actualNativeProof []
    consume fuel 2 samples .inputLength theory request Induction.initialEnvironment = .current proof ∧
      consume fuel 2 samples .inputLength theory request
        (Induction.initialEnvironment.update 0 1) = .historical proof ∧
      (UniformListChartNIKService.intrinsicKernel []).decide (theory, hypothesis .inputLength) proof = true ∧
      ExtDerivation Symbol theory (hypothesis .inputLength) ∧
      ¬ RevisionDependencySet.ValidAt (Induction.initialEnvironment.update 0 1) proofDependencies ∧
      accepts (stepChart []) 2
        ((Induction.currentAcquisition [] (Induction.initialEnvironment.update 0 1)).lease.entries.map
          RevisionBoundProgramView.ProgramEntry.source)
        (stepGoal []) (stepSystem []) request.stepProof = false := by
  have current := uniform_import_current fuel positive samples
  have historical := uniform_import_historical fuel positive samples
  exact ⟨current, historical, consumed_native_accepted (Or.inr historical),
    (consumed_proof_derivation (Or.inr historical)).2,
    Induction.consulted_revision_invalidates_dependencies [], Induction.revised_live_replay_rejected []⟩

def Consumption.label : Consumption → String
  | .generationMiss => "generation-miss"
  | .sampleRejected => "sample-rejected"
  | .claimMismatch => "claim-mismatch"
  | .recognitionMiss => "recognition-miss"
  | .proofRejected => "proof-rejected"
  | .current _ => "current-proof"
  | .historical _ => "historical-proof"

-- Executable protocol observations supplement the general proof laws.
#eval survivors 1 [emptySample]
#eval survivors 1 [emptySample, nonemptySample]
#eval (learnAndImport 1 2 [emptySample, nonemptySample] theory
  (UniformListChartNIKService.actualRequest []) Induction.initialEnvironment).map
    (fun result => (result.1, result.2.label))
#eval (consume 1 2 [emptySample, nonemptySample] .inputLength theory
  (UniformListChartNIKService.actualRequest []) Induction.initialEnvironment).label
#eval (consume 1 2 [emptySample, nonemptySample] .inputLength theory
  (UniformListChartNIKService.actualRequest []) (Induction.initialEnvironment.update 0 1)).label
#eval (consume 1 1 [emptySample, nonemptySample] .inputLength theory
  (UniformListChartNIKService.actualRequest []) Induction.initialEnvironment).label
#eval (consume 1 2 [emptySample, nonemptySample] .inputLength theory
  { UniformListChartNIKService.actualRequest [] with stepProof := malformedCertificate [] }
  Induction.initialEnvironment).label

#print axioms CountExpression.mem_enumerate
#print axioms evaluate_denote
#print axioms fits_iff_denote
#print axioms samples_do_not_supply_induction
#print axioms junk_not_full_theory_countermodel
#print axioms consume_current_iff
#print axioms consume_historical_iff
#print axioms consumed_proof_derivation
#print axioms current_import_live_premises
#print axioms learned_current_sound
#print axioms learning_imports_mapLength
#print axioms standard_refutes_zero
#print axioms uniform_import_current
#print axioms uniform_import_historical
#print axioms unrelated_revision_keeps_current
#print axioms overfit_is_not_imported
#print axioms equations_only_cannot_import
#print axioms bounded_and_malformed_are_not_countermodels
#print axioms revision_connected_workload

end UniformListCognitiveWorkload
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
