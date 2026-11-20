import Mettapedia.UniversalAI.UniversalPrediction.BitProgramJointLaw
import Mettapedia.PLN.WorldModel.BayesianObservationLedger
import Mettapedia.Logic.WorldModel.Basic

/-!
# Indexed observations of a probabilistic program run

A report fixes a position of the emitted stream. Positions need not arrive
in order. Each report is interpreted on the same program and tape, and an
inconsistent set of reports has zero evidence mass.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.PLN.WorldModel.BitProgramObservationLedger

open MeasureTheory
open Mettapedia.UniversalAI.UniversalPrediction.BitProgramJointLaw
open Mettapedia.UniversalAI.UniversalPrediction.BitProgramMixture
open Mettapedia.PLN.WorldModel.BayesianObservationLedger
open scoped ENNReal

abbrev Report := Nat × Bool

/-- The event that the run ever emits the specified bit at this position. -/
def emission (report : Report) : Set World :=
  ⋃ h : {h : List Bool // h.length = report.1}, observed (h.val ++ [report.2])

theorem measurable_emission (report : Report) : MeasurableSet (emission report) :=
  MeasurableSet.iUnion fun h => measurable_observed (h.val ++ [report.2])

theorem emission_disjoint (i : Nat) {b c : Bool} (different : b ≠ c) :
    Disjoint (emission (i, b)) (emission (i, c)) := by
  refine Set.disjoint_left.mpr fun world left right => ?_
  obtain ⟨h, hh⟩ := Set.mem_iUnion.mp left
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp right
  have length : (h.val ++ [b]).length = (k.val ++ [c]).length := by simp [h.property, k.property]
  have distinct : h.val ++ [b] ≠ k.val ++ [c] := by
    intro same
    apply different
    simpa using congrArg List.getLast? same
  exact Set.disjoint_left.mp (observed_disjoint length distinct) hh hk

theorem observed_inter_emission (h : List Bool) (b : Bool) :
    observed h ∩ emission (h.length, b) = observed (h ++ [b]) := by
  ext world
  constructor
  · rintro ⟨past, latest⟩
    obtain ⟨k, seen⟩ := Set.mem_iUnion.mp latest
    have earlier := observed_extension k.val b seen
    have same : k.val = h := by
      by_contra different
      exact Set.disjoint_left.mp (observed_disjoint k.property different) earlier past
    simpa only [same] using seen
  · intro seen
    exact ⟨observed_extension h b seen, Set.mem_iUnion.mpr ⟨⟨h, rfl⟩, seen⟩⟩

def model : ObservationModel World Report where
  likelihood _ report := (emission report).indicator 1
  measurable _ report := measurable_const.indicator (measurable_emission report)

def compatible : List Report → Set World
  | [] => Set.univ
  | report :: history => emission report ∩ compatible history

theorem compatible_each (history : List Report) (world : World) :
    world ∈ compatible history ↔ ∀ report ∈ history, world ∈ emission report := by
  induction history with
  | nil => simp [compatible]
  | cons report history ih => simp [compatible, ih]

theorem compatible_append (first second : List Report) :
    compatible (first ++ second) = compatible first ∩ compatible second := by
  ext world
  simp only [Set.mem_inter_iff, compatible_each, List.mem_append]
  constructor
  · intro both
    exact ⟨fun r present => both r (Or.inl present), fun r present => both r (Or.inr present)⟩
  · rintro ⟨left, right⟩ report (inLeft | inRight)
    · exact left report inLeft
    · exact right report inRight

theorem measurable_compatible (history : List Report) : MeasurableSet (compatible history) := by
  induction history with
  | nil => exact MeasurableSet.univ
  | cons report history ih => exact (measurable_emission report).inter ih

/-- Intersecting the observation events is the denotation of ledger scoring. -/
theorem denote_eq_restrict (history : List Report) :
    model.denote worldPrior history = worldPrior.restrict (compatible history) := by
  induction history with
  | nil =>
    rw [ObservationModel.denote]
    exact (withDensity_one (μ := worldPrior)).trans Measure.restrict_univ.symm
  | cons report history ih =>
    change worldPrior.withDensity (model.density history * model.likelihood history report) =
      worldPrior.restrict (emission report ∩ compatible history)
    rw [withDensity_mul worldPrior (model.density_measurable history)
      (model.measurable history report)]
    change (model.denote worldPrior history).withDensity ((emission report).indicator 1) = _
    rw [ih, withDensity_indicator_one (measurable_emission report),
      Measure.restrict_restrict (measurable_emission report)]

/-- A replay is absorbed even if the caller keeps the unfiltered history. -/
theorem denote_replay (history : List Report) (report : Report) (seen : report ∈ history) :
    model.denote worldPrior (report :: history) = model.denote worldPrior history := by
  rw [denote_eq_restrict, denote_eq_restrict, compatible, Set.inter_eq_right.mpr]
  exact fun world consistent => (compatible_each history world).mp consistent report seen

def prefixHistory (history : List Bool) : List Report :=
  history.zipIdx.reverse.map Prod.swap

theorem prefixHistory_append (history : List Bool) (b : Bool) :
    prefixHistory (history ++ [b]) = (history.length, b) :: prefixHistory history := by
  simp [prefixHistory, List.zipIdx_append]

theorem compatible_prefixHistory (history : List Bool) :
    compatible (prefixHistory history) = observed history := by
  induction history using List.reverseRecOn with
  | nil =>
    ext world
    simp [compatible, prefixHistory]
  | append_singleton history b ih =>
    rw [prefixHistory_append, compatible, ih, Set.inter_comm, observed_inter_emission]

theorem denotes_prefix (history : List Bool) :
    model.denote worldPrior (prefixHistory history) = worldPrior.restrict (observed history) := by
  rw [denote_eq_restrict, compatible_prefixHistory]

theorem posterior_prefix (history : List Bool) :
    posterior? (model.denote worldPrior (prefixHistory history)) = some (posterior history) := by
  rw [denotes_prefix]
  have mass : (worldPrior.restrict (observed history)) Set.univ = mixture history := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, observed_mass]
  have positive : mixture history ≠ 0 := fun zero => by
    have hp := mixture_pos history
    rw [zero, ENNReal.toReal_zero] at hp
    exact (lt_irrefl 0) hp
  have finite := mixture.ne_top history
  simp only [posterior?, mass, positive, finite, or_self, if_false]
  rw [BayesianObservationLedger.normalize, mass, posterior, observed_mass]

theorem posterior_next_report (history : List Bool) (b : Bool) :
    posterior history (emission (history.length, b)) = mixture (history ++ [b]) / mixture history := by
  rw [posterior, Measure.smul_apply, Measure.restrict_apply (measurable_emission _),
    Set.inter_comm, observed_inter_emission, observed_mass, observed_mass,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Contradictory values for an observed position exhaust the support. -/
theorem conflicting_reports (i : Nat) {b c : Bool} (different : b ≠ c) :
    posterior? (model.denote worldPrior [(i, b), (i, c)]) = none := by
  rw [denote_eq_restrict]
  have empty : compatible [(i, b), (i, c)] = ∅ := by
    simpa [compatible, Set.inter_univ] using Set.disjoint_iff_inter_eq_empty.mp
      (emission_disjoint i different)
  simp [empty, posterior?]

/-- Exact evidence has a world model with conjunction as revision and mass as
extraction. Its query carrier consists of measurable events. -/
@[instance_reducible]
def indexedWorldModel :
    MonoidalWorldModel
      (List Report) {event : Set World // MeasurableSet event} ℝ≥0∞ where
  revise first second := second ++ first
  empty := []
  extract history event := model.denote worldPrior history event.val
  revise_assoc first second third := (List.append_assoc third second first).symm
  revise_empty_left history := List.append_nil history
  revise_empty_right _ := rfl

end Mettapedia.PLN.WorldModel.BitProgramObservationLedger
