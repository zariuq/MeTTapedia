import Mettapedia.Logic.HOL.UniformListInductionChart
import Mettapedia.GSLT.Dynamics.ReusableRevisionViewAuthority
import Mettapedia.Machines.RevisionDependencySet
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Revision-bound views of the uniform HOL induction workload

The existing partial equational chart reconstructs every accepted source
formula at its declared HOL context and equality type. An occurrence view
retains the complete source beside optional specialized payloads, including
declined formulas. Filtering out declines is different: it can remove the
induction principle needed by the same source theorem.

Revision validity uses conservatively enumerated premise occurrences, not a
claim of minimal proof dependency. Live acquisition rebuilds from the actual
premise snapshot; a stale entry's generic fallback only recovers its retained
old source. The depth budget bounds chart recognition, not HOL provability.
No modal syntax, evaluation policy, native proof admission, or runtime cache
implementation is selected here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.UniformListInductionRevisionViews

open GroundUnaryEquationalChart
open Mettapedia.GSLT.Dynamics
open RevisionBoundProgramView ReusableRevisionViewAuthority
open Mettapedia.Machines
open Mettapedia.GSLT.Core

universe u v

section PartialSpecialization

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {τ : Ty Base}
variable [DecidableEq Base] [∀ σ, DecidableEq (Const σ)]

/-- The executable reifier's payload, without changing its admitted grammar. -/
def compileEquation (chart : Chart Const Γ τ) (fuel : Nat) (source : Formula Const Γ) :
    Option (Equation chart) :=
  (reifyEquation chart fuel source).map ReifiedEquation.equation

/-- Accepted specialization reconstructs its original formula. This is a
partial left inverse, not an equivalence with arbitrary backend equations. -/
theorem compileEquation_roundtrip (chart : Chart Const Γ τ) (fuel : Nat)
    (source : Formula Const Γ) (equation : Equation chart)
    (compiled : compileEquation chart fuel source = some equation)
    (valuation : Nat → Term Const Γ τ) :
    formula chart valuation equation = source := by
  unfold compileEquation at compiled
  cases recognized : reifyEquation chart fuel source with
  | none => simp [recognized] at compiled
  | some result =>
      simp only [recognized, Option.map_some, Option.some.injEq] at compiled
      rw [← compiled]
      exact result.roundtrip valuation

/-- One accepted specialized payload cannot identify different formulas at
the same declared chart and context. -/
theorem compileEquation_reflects_source (chart : Chart Const Γ τ) (fuel : Nat)
    (left right : Formula Const Γ) (equation : Equation chart)
    (leftCompiled : compileEquation chart fuel left = some equation)
    (rightCompiled : compileEquation chart fuel right = some equation)
    (valuation : Nat → Term Const Γ τ) : left = right :=
  (compileEquation_roundtrip chart fuel left equation leftCompiled valuation).symm.trans
    (compileEquation_roundtrip chart fuel right equation rightCompiled valuation)

@[simp] theorem compileEquation_all (chart : Chart Const Γ τ) (fuel : Nat)
    {σ : Ty Base} (body : Formula Const (σ :: Γ)) :
    compileEquation chart fuel (.all body) = none := rfl

end PartialSpecialization

section RevisionViews

variable {Base : Type} {Const : Ty Base → Type} {Γ : Ctx Base} {τ : Ty Base}
variable {Store Revision : Type}
variable [DecidableEq Base] [∀ σ, DecidableEq (Const σ)]
variable [DecidableEq Store] [DecidableEq Revision]

/-- Use the store's actual revision-scoped occurrence enumeration. -/
def premiseSnapshot (view : RevisionedStoreView Store Revision (Formula Const Γ)) :
    Snapshot Store Revision (StoreOccurrenceId Store Revision) (Formula Const Γ) where
  key := ⟨view.storeId, view.revision⟩
  occurrences := view.occurrences.map fun occurrence => ⟨occurrence.1, occurrence.2⟩

/-- Every premise occurrence is conservatively retained as a dependency.
No dependency-minimality or certificate-slicing claim is made. -/
def premiseDependencies (view : RevisionedStoreView Store Revision (Formula Const Γ)) :
    RevisionDependencySet Store Revision :=
  (view.occurrences.map Prod.fst).toFinset

omit [DecidableEq Base] [∀ σ, DecidableEq (Const σ)] in
theorem premise_dependency_resolves
    (view : RevisionedStoreView Store Revision (Formula Const Γ))
    (occurrence : StoreOccurrenceId Store Revision)
    (member : occurrence ∈ premiseDependencies view) :
    ∃ source ∈ view.entries, view.resolve occurrence = some source := by
  simp only [premiseDependencies, List.mem_toFinset, List.mem_map] at member
  obtain ⟨⟨found, source⟩, present, equal⟩ := member
  dsimp only at equal
  subst found
  refine ⟨source, ?_, view.resolve_of_mem_occurrences present⟩
  have payload : source ∈ view.occurrences.map Prod.snd :=
    List.mem_map.mpr ⟨(_, source), present, rfl⟩
  simpa only [RevisionedStoreView.occurrences_payloads] using payload

omit [DecidableEq Base] [∀ σ, DecidableEq (Const σ)] in
theorem premise_dependencies_current
    (view : RevisionedStoreView Store Revision (Formula Const Γ))
    (environment : RevisionEnvironment Store Revision)
    (current : environment.current view.storeId = view.revision) :
    RevisionDependencySet.ValidAt environment (premiseDependencies view) := by
  intro occurrence member
  simp only [premiseDependencies, List.mem_toFinset, List.mem_map] at member
  obtain ⟨⟨found, source⟩, present, equal⟩ := member
  dsimp only at equal
  subst found
  simp only [RevisionedStoreView.occurrences, List.mem_map] at present
  obtain ⟨⟨payload, index⟩, _, equal⟩ := present
  cases equal
  exact current

omit [DecidableEq Store] [DecidableEq Revision] in
/-- Hiding derived payloads recovers the exact source occurrence list; it
does not drop the source of a declined specialization. -/
theorem retained_sources_exact (chart : Chart Const Γ τ) (fuel : Nat)
    (view : RevisionedStoreView Store Revision (Formula Const Γ)) :
    (build (compileEquation chart fuel) (premiseSnapshot view)).entries.map eraseEntry =
        (premiseSnapshot view).occurrences ∧
      (build (compileEquation chart fuel) (premiseSnapshot view)).entries.map
        ProgramEntry.source = view.entries := by
  constructor
  · exact erase_build _ _
  · simp [build, premiseSnapshot, compileEntry, Function.comp_def]

/-- Reconstruction through the current, declined, or stale route recovers
the entry's retained formula. It does not look up a newer premise. -/
theorem retained_row_reconstruction (chart : Chart Const Γ τ) (fuel : Nat)
    (viewKey liveKey : RevisionKey Store Revision)
    (occurrence : StableOccurrenceIdentityIndex.Occurrence
      (StoreOccurrenceId Store Revision) (Formula Const Γ))
    (valuation : Nat → Term Const Γ τ) :
    runEntry viewKey liveKey (fun source _ => source)
        (fun equation valuation => formula chart valuation equation)
        (compileEntry (compileEquation chart fuel) occurrence) valuation =
      occurrence.payload := by
  apply runEntry_exact
  intro equation compiled
  exact compileEquation_roundtrip chart fuel occurrence.payload equation compiled valuation

/-- Adapt an actual contextual premise table to the existing acquisition
contract. The table, context, chart and fuel stay parameters of soundness. -/
def premiseFamily
    (premisesAt : RevisionKey Store Revision → List (Formula Const Γ)) :
    SnapshotFamily Store Revision (StoreOccurrenceId Store Revision) (Formula Const Γ) where
  snapshotAt key := premiseSnapshot ⟨key.store, key.revision, premisesAt key⟩
  key_snapshotAt _ := rfl

theorem acquired_sources_exact (chart : Chart Const Γ τ) (fuel : Nat)
    (premisesAt : RevisionKey Store Revision → List (Formula Const Γ))
    (authority : Authority Store Revision (StoreOccurrenceId Store Revision)
      (Formula Const Γ) (Equation chart))
    (key : RevisionKey Store Revision)
    (sound : Sound (premiseFamily premisesAt) (compileEquation chart fuel) authority) :
    (acquire (premiseFamily premisesAt) (compileEquation chart fuel) authority key).lease.entries.map
      ProgramEntry.source = premisesAt key := by
  rw [acquire_exact _ _ _ _ sound]
  exact (retained_sources_exact chart fuel ⟨key.store, key.revision, premisesAt key⟩).2

/-- The accepted proof is reconstructed under the live contextual premise
table, and the conservatively enumerated source dependencies are current. -/
theorem live_acquisition_reconstruct (chart : Chart Const Γ τ) (fuel : Nat)
    (premisesAt : RevisionKey Store Revision → List (Formula Const Γ))
    (authority : Authority Store Revision (StoreOccurrenceId Store Revision)
      (Formula Const Γ) (Equation chart))
    (environment : RevisionEnvironment Store Revision) (store : Store)
    (sound : Sound (premiseFamily premisesAt) (compileEquation chart fuel) authority)
    (goal : Formula Const Γ) (system : UniversalAlgebra.EquationSystem chart.signature)
    (certificate : Certificate chart system)
    (accepted : accepts chart fuel
      ((acquire (premiseFamily premisesAt) (compileEquation chart fuel) authority
        ⟨store, environment.current store⟩).lease.entries.map ProgramEntry.source)
      goal system certificate = true)
    (valuation : Nat → Term Const Γ τ) :
    RevisionDependencySet.ValidAt environment
        (premiseDependencies (⟨store, environment.current store,
          premisesAt ⟨store, environment.current store⟩⟩ :
          RevisionedStoreView Store Revision (Formula Const Γ))) ∧
      ExtDerivation Const (premisesAt ⟨store, environment.current store⟩) goal := by
  constructor
  · exact premise_dependencies_current _ environment rfl
  · rw [acquired_sources_exact chart fuel premisesAt authority _ sound] at accepted
    exact accepts_reconstruct chart fuel _ goal system certificate accepted valuation

end RevisionViews

namespace Induction

open UniformListInduction UniformListInductionChart

local instance : DecidableEq BaseSort
  | .element, .element | .sequence, .sequence | .count, .count => .isTrue rfl
  | .element, .sequence | .element, .count | .sequence, .element
  | .sequence, .count | .count, .element | .count, .sequence =>
      .isFalse (by intro h; cases h)

local instance (τ : Ty BaseSort) : DecidableEq (Symbol τ) := by
  intro a b
  cases a <;> cases b <;> exact .isTrue rfl

/-- Store zero carries the actual cons-step premises. Revision zero is the
original induction hypothesis; later revisions use the existing altered one. -/
def stepPremisesAt (Γ : Ctx BaseSort) (key : RevisionKey Nat Nat) :
    List (Formula Symbol (stepContext Γ)) :=
  if key.store = 0 then
    if key.revision = 0 then stepAssumptions Γ else alteredStepAssumptions Γ
  else []

def stepStore (Γ : Ctx BaseSort) (revision : Nat) :
    RevisionedStoreView Nat Nat (Formula Symbol (stepContext Γ)) :=
  ⟨0, revision, stepPremisesAt Γ ⟨0, revision⟩⟩

def initialEnvironment : RevisionEnvironment Nat Nat := ⟨fun _ => 0⟩

/-- The changed premise is the third actual chart assumption. -/
def originalHypothesisOccurrence : StoreOccurrenceId Nat Nat := ⟨⟨0, 0⟩, 2⟩

theorem original_hypothesis_dependency (Γ : Ctx BaseSort) :
    originalHypothesisOccurrence ∈ premiseDependencies (stepStore Γ 0) := by
  simp [premiseDependencies, stepStore, stepPremisesAt, RevisionedStoreView.occurrences,
    RevisionedStoreView.occurrenceId, RevisionedStoreView.readToken,
    stepAssumptions, originalHypothesisOccurrence]

theorem original_dependencies_current (Γ : Ctx BaseSort) :
    RevisionDependencySet.ValidAt initialEnvironment (premiseDependencies (stepStore Γ 0)) :=
  premise_dependencies_current _ _ rfl

theorem unrelated_revision_preserves_dependencies (Γ : Ctx BaseSort) (revision : Nat) :
    RevisionDependencySet.ValidAt (initialEnvironment.update 1 revision)
      (premiseDependencies (stepStore Γ 0)) := by
  rw [RevisionDependencySet.validAt_update_iff_of_not_mem_storeSupport]
  · exact original_dependencies_current Γ
  · simp [RevisionDependencySet.storeSupport, premiseDependencies, stepStore,
      stepPremisesAt, RevisionedStoreView.occurrences, RevisionedStoreView.occurrenceId,
      RevisionedStoreView.readToken, stepAssumptions]

theorem consulted_revision_invalidates_dependencies (Γ : Ctx BaseSort) :
    ¬ RevisionDependencySet.ValidAt (initialEnvironment.update 0 1)
      (premiseDependencies (stepStore Γ 0)) :=
  RevisionDependencySet.not_validAt_update_of_mem initialEnvironment _
    originalHypothesisOccurrence (original_hypothesis_dependency Γ) 1 (by decide)

theorem revised_store_rejects_old_occurrence (Γ : Ctx BaseSort) :
    (stepStore Γ 1).resolve originalHypothesisOccurrence = none :=
  (stepStore Γ 1).resolve_stale originalHypothesisOccurrence (by change 0 ≠ 1; decide)

/-- The very same backend-valid certificate is source-bound: changing its
actual induction-hypothesis premise rejects reuse. -/
theorem revision_bound_certificate_control (Γ : Ctx BaseSort) :
    RevisionDependencySet.ValidAt initialEnvironment (premiseDependencies (stepStore Γ 0)) ∧
      ¬ RevisionDependencySet.ValidAt (initialEnvironment.update 0 1)
        (premiseDependencies (stepStore Γ 0)) ∧
      (stepStore Γ 1).resolve originalHypothesisOccurrence = none ∧
      (stepCertificate Γ).valid
        (UniversalAlgebra.equationalRuleInterface (stepSystem Γ)) = true ∧
      accepts (stepChart Γ) 2 (stepStore Γ 0).entries (stepGoal Γ)
        (stepSystem Γ) (stepCertificate Γ) = true ∧
      accepts (stepChart Γ) 2 (stepStore Γ 1).entries (stepGoal Γ)
        (stepSystem Γ) (stepCertificate Γ) = false :=
  ⟨original_dependencies_current Γ, consulted_revision_invalidates_dependencies Γ,
    revised_store_rejects_old_occurrence Γ, step_backend_valid Γ,
    step_accepted Γ, altered_assumption_rejected Γ⟩

/-- Build the first view from the actual original step-premise store. -/
def initialAcquisition (Γ : Ctx BaseSort) :
    Acquisition Nat Nat (StoreOccurrenceId Nat Nat)
      (Formula Symbol (stepContext Γ)) (Equation (stepChart Γ)) :=
  acquire (premiseFamily (stepPremisesAt Γ)) (compileEquation (stepChart Γ) 2)
    { cached := none } ⟨0, 0⟩

/-- Subsequent requests use the current revision of the same premise store,
not a retagged old entry. -/
def currentAcquisition (Γ : Ctx BaseSort) (environment : RevisionEnvironment Nat Nat) :
    Acquisition Nat Nat (StoreOccurrenceId Nat Nat)
      (Formula Symbol (stepContext Γ)) (Equation (stepChart Γ)) :=
  acquire (premiseFamily (stepPremisesAt Γ)) (compileEquation (stepChart Γ) 2)
    (initialAcquisition Γ).authority ⟨0, environment.current 0⟩

theorem initial_acquisition_sound (Γ : Ctx BaseSort) :
    Sound (premiseFamily (stepPremisesAt Γ)) (compileEquation (stepChart Γ) 2)
      (initialAcquisition Γ).authority := by
  apply acquire_sound
  intro entry impossible
  cases impossible

theorem current_acquisition_sources (Γ : Ctx BaseSort)
    (environment : RevisionEnvironment Nat Nat) :
    (currentAcquisition Γ environment).lease.entries.map ProgramEntry.source =
      stepPremisesAt Γ ⟨0, environment.current 0⟩ :=
  acquired_sources_exact (stepChart Γ) 2 (stepPremisesAt Γ)
    (initialAcquisition Γ).authority _ (initial_acquisition_sound Γ)

theorem unchanged_revision_reuses (Γ : Ctx BaseSort) :
    (currentAcquisition Γ initialEnvironment).kind = .reused ∧
      (currentAcquisition Γ initialEnvironment).buildCount = 0 ∧
      (currentAcquisition Γ initialEnvironment).lease = (initialAcquisition Γ).lease :=
  acquire_twice_reuses (premiseFamily (stepPremisesAt Γ))
    (compileEquation (stepChart Γ) 2) { cached := none } ⟨0, 0⟩

theorem consulted_revision_rebuilds (Γ : Ctx BaseSort) :
    (currentAcquisition Γ (initialEnvironment.update 0 1)).kind = .built ∧
      (currentAcquisition Γ (initialEnvironment.update 0 1)).buildCount = 1 :=
  changed_key_builds (premiseFamily (stepPremisesAt Γ))
    (compileEquation (stepChart Γ) 2) { cached := none } ⟨0, 0⟩ ⟨0, 1⟩ (by decide)

theorem unrelated_revision_reuses (Γ : Ctx BaseSort) (revision : Nat) :
    currentAcquisition Γ (initialEnvironment.update 1 revision) =
      currentAcquisition Γ initialEnvironment := by
  simp [currentAcquisition, RevisionEnvironment.update]

theorem original_live_replay_accepted (Γ : Ctx BaseSort) :
    accepts (stepChart Γ) 2
      ((currentAcquisition Γ initialEnvironment).lease.entries.map ProgramEntry.source)
      (stepGoal Γ) (stepSystem Γ) (stepCertificate Γ) = true := by
  rw [current_acquisition_sources]
  exact step_accepted Γ

/-- Live acquisition followed by the existing checker reconstructs the real
cons-step proof under precisely the stored original premises. -/
theorem original_live_reconstruction (Γ : Ctx BaseSort) :
    RevisionDependencySet.ValidAt initialEnvironment
        (premiseDependencies (stepStore Γ 0)) ∧
      ExtDerivation Symbol (stepAssumptions Γ) (stepGoal Γ) :=
  live_acquisition_reconstruct (stepChart Γ) 2 (stepPremisesAt Γ)
    (initialAcquisition Γ).authority initialEnvironment 0 (initial_acquisition_sound Γ)
    (stepGoal Γ) (stepSystem Γ) (stepCertificate Γ) (original_live_replay_accepted Γ)
    (fun _ => .const .zero)

/-- The rebuilt live view contains the changed premise, so the original
certificate is rejected even though its backend replay tree remains valid. -/
theorem revised_live_replay_rejected (Γ : Ctx BaseSort) :
    accepts (stepChart Γ) 2
      ((currentAcquisition Γ (initialEnvironment.update 0 1)).lease.entries.map
        ProgramEntry.source)
      (stepGoal Γ) (stepSystem Γ) (stepCertificate Γ) = false := by
  rw [current_acquisition_sources]
  exact altered_assumption_rejected Γ

/-- The new premise snapshot is itself current; rejecting the old
certificate is not a blanket rejection of every revised source. -/
theorem revised_dependencies_current (Γ : Ctx BaseSort) :
    RevisionDependencySet.ValidAt (initialEnvironment.update 0 1)
      (premiseDependencies (stepStore Γ 1)) :=
  premise_dependencies_current _ _ rfl

def originalHypothesisEntry (Γ : Ctx BaseSort) :
    ProgramEntry (StoreOccurrenceId Nat Nat) (Formula Symbol (stepContext Γ))
      (Equation (stepChart Γ)) :=
  compileEntry (compileEquation (stepChart Γ) 2)
    ⟨originalHypothesisOccurrence, .eq ((stepChart Γ).atoms 2) ((stepChart Γ).atoms 3)⟩

def revisedHypothesisEntry (Γ : Ctx BaseSort) :
    ProgramEntry (StoreOccurrenceId Nat Nat) (Formula Symbol (stepContext Γ))
      (Equation (stepChart Γ)) :=
  compileEntry (compileEquation (stepChart Γ) 2)
    ⟨⟨⟨0, 1⟩, 2⟩, .eq ((stepChart Γ).atoms 2) ((stepChart Γ).atoms 2)⟩

/-- These are the actual third entries of the acquired original and revised
views, rather than detached reconstruction examples. -/
theorem acquired_hypothesis_entries (Γ : Ctx BaseSort) :
    (initialAcquisition Γ).lease.entries[2]? = some (originalHypothesisEntry Γ) ∧
      (currentAcquisition Γ (initialEnvironment.update 0 1)).lease.entries[2]? =
        some (revisedHypothesisEntry Γ) := by
  exact ⟨rfl, rfl⟩

theorem hypothesis_sources_differ (Γ : Ctx BaseSort) :
    (originalHypothesisEntry Γ).source ≠ (revisedHypothesisEntry Γ).source := by
  intro equal
  cases equal

/-- Stale fallback reconstructs the old formula, not the formula now stored
at the same logical position in the newly acquired revision. -/
theorem stale_retained_source_is_not_live (Γ : Ctx BaseSort) :
    let retained := runEntry (⟨0, 0⟩ : RevisionKey Nat Nat) ⟨0, 1⟩
      (fun source _ => source)
      (fun equation valuation => formula (stepChart Γ) valuation equation)
      (originalHypothesisEntry Γ) (fun _ => .const .zero)
    retained = (originalHypothesisEntry Γ).source ∧
      retained ≠ (revisedHypothesisEntry Γ).source := by
  have oldSource := runEntry_stale (⟨0, 0⟩ : RevisionKey Nat Nat) ⟨0, 1⟩
    (fun source _ => source)
    (fun equation valuation => formula (stepChart Γ) valuation equation)
    (originalHypothesisEntry Γ) (fun _ => .const .zero) (by decide)
  dsimp only
  exact ⟨oldSource, oldSource ▸ hypothesis_sources_differ Γ⟩

/-- All four actual cons-step premises specialize and reconstruct, including
the registered successor spines. -/
theorem step_specializations_reconstruct (Γ : Ctx BaseSort)
    (source : Formula Symbol (stepContext Γ)) (member : source ∈ stepAssumptions Γ) :
    ∃ equation, compileEquation (stepChart Γ) 2 source = some equation ∧
      ∀ valuation, formula (stepChart Γ) valuation equation = source := by
  have recognized := step_assumptions_eligible Γ source member
  unfold eligible at recognized
  cases result : reifyEquation (stepChart Γ) 2 source with
  | none => simp [result] at recognized
  | some reified =>
      exact ⟨reified.equation, by simp [compileEquation, result], reified.roundtrip⟩

/-- The complete uniform theory, at its explicitly declared context and
revision, retains sources beside the chart's optional payloads. -/
def retainedTheory {Γ : Ctx BaseSort} {τ : Ty BaseSort}
    (chart : Chart Symbol Γ τ) (fuel revision : Nat) :
    ProgramView Nat Nat (StoreOccurrenceId Nat Nat) (Formula Symbol Γ) (Equation chart) :=
  build (compileEquation chart fuel)
    (premiseSnapshot (⟨0, revision, theory⟩ : RevisionedStoreView Nat Nat (Formula Symbol Γ)))

/-- Hiding the derived payload does not hide the source from later source
consumers: even the declined induction principle remains at its original
revision-scoped occurrence, in the original order. -/
theorem hiding_retains_induction {Γ : Ctx BaseSort} {τ : Ty BaseSort}
    (chart : Chart Symbol Γ τ) (fuel revision : Nat) :
    (retainedTheory chart fuel revision).key = ⟨0, revision⟩ ∧
      (retainedTheory chart fuel revision).entries.map eraseEntry =
        (premiseSnapshot (⟨0, revision, theory⟩ :
          RevisionedStoreView Nat Nat (Formula Symbol Γ))).occurrences ∧
      (retainedTheory chart fuel revision).entries.map ProgramEntry.source = theory ∧
      (retainedTheory chart fuel revision).entries.head?.map ProgramEntry.source =
        some inductionPrinciple ∧
      (retainedTheory chart fuel revision).entries.head?.bind ProgramEntry.code = none := by
  have retained := retained_sources_exact chart fuel
    (⟨0, revision, theory⟩ : RevisionedStoreView Nat Nat (Formula Symbol Γ))
  exact ⟨rfl, retained.1, retained.2, rfl, rfl⟩

/-- Destructively keeping only successful payloads is not source hiding. -/
def compiledOnly {Γ : Ctx BaseSort} {τ : Ty BaseSort}
    (chart : Chart Symbol Γ τ) (fuel : Nat) (sources : List (Formula Symbol Γ)) :
    List (Equation chart) := sources.filterMap (compileEquation chart fuel)

theorem compiled_only_identifies_theories {τ : Ty BaseSort}
    (chart : Chart Symbol [] τ) (fuel : Nat) :
    compiledOnly chart fuel theory = compiledOnly chart fuel equations := rfl

/-- Erasing declined formulas removes the actual induction licence. The
original HOL proof and its source countermodel refute reconstruction of
provability from this specialized-only view. -/
theorem compiled_only_cannot_license_mapLength {τ : Ty BaseSort}
    (chart : Chart Symbol [] τ) (fuel : Nat) :
    ¬ NonFactorization.Factors (compiledOnly chart fuel)
      (fun sources => ExtDerivation Symbol sources mapLength) :=
  (NonFactorization.NonTrivialFiber.ofProp
    (compiled_only_identifies_theories chart fuel)
    (mapLength_via_chart []) equations_do_not_derive_mapLength).not_factors

/-- Bounded recognition retains its positive reconstruction contract but a
miss at lower depth is compatible with the actual HOL proof. -/
theorem bounded_recognition_is_not_nonprovability (Γ : Ctx BaseSort) :
    accepts (stepChart Γ) 2 (stepAssumptions Γ) (stepGoal Γ)
        (stepSystem Γ) (stepCertificate Γ) = true ∧
      accepts (stepChart Γ) 1 (stepAssumptions Γ) (stepGoal Γ)
        (stepSystem Γ) (stepCertificate Γ) = false ∧
      ExtDerivation Symbol
        (preservesLength (stepFunction Γ) (stepSequence Γ) :: equations) (stepGoal Γ) :=
  ⟨step_accepted Γ, insufficient_budget_rejected Γ, step_reconstruction Γ⟩

/-- The four distinct contracts meet on the original induction workload:
source hiding retains the closed theory and its revision; actual contextual
step premises reconstruct from accepted specialization; destructive erasure
fails for the source theorem; bounded recognition has a proved false miss.
The live cache transition then reconstructs under the original premises but
rejects their old certificate under the current changed premises. The erasure
countermodel is deliberately scoped to the closed theory, while `Γ` remains
the actual ambient context of the cons-step proof. -/
theorem four_view_contracts (Γ : Ctx BaseSort) {τ : Ty BaseSort}
    (closedChart : Chart Symbol [] τ) (fuel theoryRevision : Nat) :
    let retained := retainedTheory closedChart fuel theoryRevision
    let original := currentAcquisition Γ initialEnvironment
    let revised := currentAcquisition Γ (initialEnvironment.update 0 1)
    (retained.key = ⟨0, theoryRevision⟩ ∧
      retained.entries.map ProgramEntry.source = theory ∧
      retained.entries.head?.map ProgramEntry.source = some inductionPrinciple ∧
      retained.entries.head?.bind ProgramEntry.code = none) ∧
    (∀ source ∈ original.lease.entries.map ProgramEntry.source,
      ∃ equation, compileEquation (stepChart Γ) 2 source = some equation ∧
        ∀ valuation, formula (stepChart Γ) valuation equation = source) ∧
    (¬ NonFactorization.Factors (compiledOnly closedChart fuel)
      (fun sources => ExtDerivation Symbol sources mapLength)) ∧
    (accepts (stepChart Γ) 1 (original.lease.entries.map ProgramEntry.source)
        (stepGoal Γ) (stepSystem Γ) (stepCertificate Γ) = false ∧
      accepts (stepChart Γ) 2 (original.lease.entries.map ProgramEntry.source)
        (stepGoal Γ) (stepSystem Γ) (stepCertificate Γ) = true ∧
      ExtDerivation Symbol (original.lease.entries.map ProgramEntry.source) (stepGoal Γ)) ∧
    (original.kind = .reused ∧ revised.kind = .built ∧
      accepts (stepChart Γ) 2 (revised.lease.entries.map ProgramEntry.source)
        (stepGoal Γ) (stepSystem Γ) (stepCertificate Γ) = false) ∧
    (RevisionDependencySet.ValidAt initialEnvironment
        (premiseDependencies (stepStore Γ 0)) ∧
      ¬ RevisionDependencySet.ValidAt (initialEnvironment.update 0 1)
        (premiseDependencies (stepStore Γ 0)) ∧
      RevisionDependencySet.ValidAt (initialEnvironment.update 0 1)
        (premiseDependencies (stepStore Γ 1))) := by
  dsimp only
  have hidden := hiding_retains_induction closedChart fuel theoryRevision
  refine ⟨⟨hidden.1, hidden.2.2.1, hidden.2.2.2.1, hidden.2.2.2.2⟩,
    ?_, compiled_only_cannot_license_mapLength closedChart fuel,
    ?_, ⟨(unchanged_revision_reuses Γ).1, (consulted_revision_rebuilds Γ).1,
      revised_live_replay_rejected Γ⟩,
    ⟨(original_live_reconstruction Γ).1, consulted_revision_invalidates_dependencies Γ,
      revised_dependencies_current Γ⟩⟩
  · rw [current_acquisition_sources]
    exact step_specializations_reconstruct Γ
  · rw [current_acquisition_sources]
    exact ⟨insufficient_budget_rejected Γ, step_accepted Γ,
      (original_live_reconstruction Γ).2⟩

end Induction

#print axioms compileEquation_roundtrip
#print axioms compileEquation_reflects_source
#print axioms premise_dependency_resolves
#print axioms premise_dependencies_current
#print axioms retained_sources_exact
#print axioms retained_row_reconstruction
#print axioms acquired_sources_exact
#print axioms live_acquisition_reconstruct
#print axioms Induction.unrelated_revision_preserves_dependencies
#print axioms Induction.revision_bound_certificate_control
#print axioms Induction.unchanged_revision_reuses
#print axioms Induction.consulted_revision_rebuilds
#print axioms Induction.unrelated_revision_reuses
#print axioms Induction.original_live_reconstruction
#print axioms Induction.revised_live_replay_rejected
#print axioms Induction.revised_dependencies_current
#print axioms Induction.acquired_hypothesis_entries
#print axioms Induction.stale_retained_source_is_not_live
#print axioms Induction.step_specializations_reconstruct
#print axioms Induction.hiding_retains_induction
#print axioms Induction.compiled_only_cannot_license_mapLength
#print axioms Induction.bounded_recognition_is_not_nonprovability
#print axioms Induction.four_view_contracts

end Mettapedia.Logic.HOL.UniformListInductionRevisionViews
