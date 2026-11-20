import Mettapedia.PLN.WorldModel.BayesianObservationLedger

/-!
# Bayesian observation through a measurable view

A context that retains the likelihoods and query can use the corresponding
pushforward of the prior. Conditioning commutes with this change of context
for an entire observation history, including histories of zero or infinite mass.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.PLN.WorldModel.BayesianObservationLedger

open MeasureTheory
open scoped ENNReal

variable {Ω V Q Event : Type*} [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSpace Q]

/-- A likelihood on the view induces a likelihood on the original world. -/
theorem map_withDensity_pullback (prior : Measure Ω) {view : Ω → V} (hv : Measurable view)
    {likelihood : V → ℝ≥0∞} (hl : Measurable likelihood) :
    (prior.withDensity (likelihood ∘ view)).map view =
      (prior.map view).withDensity likelihood := by
  apply Measure.ext
  intro event he
  rw [Measure.map_apply hv he, withDensity_apply _ (hv he), withDensity_apply _ he]
  exact (setLIntegral_map he hl hv).symm

def ObservationModel.pullback (model : ObservationModel V Event)
    (view : Ω → V) (hv : Measurable view) : ObservationModel Ω Event where
  likelihood history event := model.likelihood history event ∘ view
  measurable history event := (model.measurable history event).comp hv

theorem ObservationModel.density_pullback (model : ObservationModel V Event)
    (view : Ω → V) (hv : Measurable view) (history : List Event) :
    (model.pullback view hv).density history = model.density history ∘ view := by
  induction history with
  | nil => rfl
  | cons event history ih =>
    rw [ObservationModel.density, ih]
    rfl

/-- The entire unnormalized ledger commutes with the observation view. -/
theorem ObservationModel.denote_map (model : ObservationModel V Event)
    (prior : Measure Ω) {view : Ω → V} (hv : Measurable view) (history : List Event) :
    ((model.pullback view hv).denote prior history).map view =
      model.denote (prior.map view) history := by
  simp only [ObservationModel.denote, ObservationModel.density_pullback]
  exact map_withDensity_pullback prior hv (model.density_measurable history)

private theorem map_univ (measure : Measure Ω) {view : Ω → V} (hv : Measurable view) :
    measure.map view Set.univ = measure Set.univ := by
  rw [Measure.map_apply hv MeasurableSet.univ, Set.preimage_univ]

theorem posterior_map (measure : Measure Ω) {view : Ω → V} (hv : Measurable view) :
    (posterior? measure).map (fun updated => updated.map view) =
      posterior? (measure.map view) := by
  simp only [posterior?, map_univ measure hv]
  split
  · rfl
  · simp [normalize, map_univ measure hv]

/-- Read any measurable query of the view from the posterior on that view. -/
theorem ObservationModel.query_from_view (model : ObservationModel V Event)
    (prior : Measure Ω) {view : Ω → V} (hv : Measurable view) (history : List Event)
    {query : V → Q} (hq : Measurable query) :
    (posterior? ((model.pullback view hv).denote prior history)).map
        (fun updated => updated.map (query ∘ view)) =
      (posterior? (model.denote (prior.map view) history)).map
        (fun updated => updated.map query) := by
  rw [← model.denote_map prior hv history, ← posterior_map _ hv, Option.map_map]
  congr 1
  funext updated
  exact (Measure.map_map hq hv).symm

/-- Shared query and evidence views suffice even when the underlying worlds
have unrelated representations. The conclusion holds for every future history
whose likelihoods factor through the view. -/
theorem ObservationModel.covering_contexts_agree {World' : Type*} [MeasurableSpace World']
    (model : ObservationModel V Event) (prior : Measure Ω) (other : Measure World')
    {view : Ω → V} {view' : World' → V} (hv : Measurable view) (hv' : Measurable view')
    (same : prior.map view = other.map view') (history : List Event)
    {query : V → Q} (hq : Measurable query) :
    (posterior? ((model.pullback view hv).denote prior history)).map
        (fun updated => updated.map (query ∘ view)) =
      (posterior? ((model.pullback view' hv').denote other history)).map
        (fun updated => updated.map (query ∘ view')) := by
  rw [model.query_from_view prior hv history hq, model.query_from_view other hv' history hq, same]

end Mettapedia.PLN.WorldModel.BayesianObservationLedger
