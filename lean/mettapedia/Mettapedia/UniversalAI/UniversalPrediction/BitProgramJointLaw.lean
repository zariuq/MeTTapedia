import Mettapedia.UniversalAI.UniversalPrediction.BitProgramTape

/-!
# The joint law of the program and its random tape

A world contains a description index and a fair input tape. Conditioning this
probability measure on an emitted prefix gives the exact posterior over both.
The output projection can lose continuation mass without losing worlds from
the underlying sample space.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.UniversalPrediction.BitProgramJointLaw

open Filter MeasureTheory Mettapedia.Computability
open Mettapedia.UniversalAI.UniversalPrediction.BitProgramMixture
open scoped ENNReal

abbrev World := Nat × CantorSpace

noncomputable def worldPrior : Measure World :=
  Measure.sum fun i : Nat => descriptionWeight i • coinMeasure.map (Prod.mk i)

private theorem measurable_section (i : Nat) : Measurable (Prod.mk i : CantorSpace → World) :=
  measurable_const.prodMk measurable_id

theorem worldPrior_apply {s : Set World} (hs : MeasurableSet s) :
    worldPrior s = ∑' i : Nat, descriptionWeight i * coinMeasure ((Prod.mk i) ⁻¹' s) := by
  rw [worldPrior, Measure.sum_apply _ hs]
  apply tsum_congr
  intro i
  rw [Measure.smul_apply, Measure.map_apply (measurable_section i) hs, smul_eq_mul]

instance probability_worldPrior : IsProbabilityMeasure worldPrior := by
  constructor
  rw [worldPrior_apply MeasurableSet.univ]
  simpa only [Set.preimage_univ, measure_univ, mul_one] using descriptionWeight_total

def observed (h : List Bool) : Set World :=
  ⋃ i : Nat, ({i} : Set Nat) ×ˢ (programAt i).event h

@[simp] theorem mem_observed (x : World) (h : List Bool) :
    x ∈ observed h ↔ x.2 ∈ (programAt x.1).event h := by
  simp [observed]

theorem measurable_observed (h : List Bool) : MeasurableSet (observed h) :=
  MeasurableSet.iUnion fun i =>
    (measurableSet_singleton i).prod ((programAt i).measurable_event h)

theorem observed_mass (h : List Bool) : worldPrior (observed h) = mixture h := by
  rw [worldPrior_apply (measurable_observed h), mixture_apply]
  apply tsum_congr
  intro i
  have slice : Prod.mk i ⁻¹' observed h = (programAt i).event h := by
    ext tape
    exact mem_observed (i, tape) h
  rw [slice, BitGenerator.Generator.semimeasure_apply]

def modelEvent (i : Nat) : Set World :=
  Prod.fst ⁻¹' ({i} : Set Nat)

theorem model_observed_mass (i : Nat) (h : List Bool) :
    worldPrior (modelEvent i ∩ observed h) = descriptionWeight i * (programAt i).semimeasure h := by
  have measurable_model : MeasurableSet (modelEvent i) :=
    measurable_fst (measurableSet_singleton i)
  rw [worldPrior_apply (measurable_model.inter (measurable_observed h))]
  have slice (j : Nat) : Prod.mk j ⁻¹' (modelEvent i ∩ observed h) =
      if j = i then (programAt i).event h else ∅ := by
    ext tape
    by_cases same : j = i
    · subst j
      simp [modelEvent]
    · simp [modelEvent, same]
  simp_rw [slice]
  rw [tsum_eq_single i]
  · simp [BitGenerator.Generator.semimeasure_apply]
  · intro j distinct
    simp [distinct]

theorem observed_mono {h k : List Bool} (included : h <+: k) : observed k ⊆ observed h := by
  intro x later
  exact (mem_observed x h).mpr ((programAt x.1).event_mono included
    ((mem_observed x k).mp later))

theorem observed_extension (h : List Bool) (b : Bool) : observed (h ++ [b]) ⊆ observed h :=
  observed_mono (List.prefix_append h [b])

theorem observed_disjoint {h k : List Bool} (length : h.length = k.length) (distinct : h ≠ k) :
    Disjoint (observed h) (observed k) := by
  refine Set.disjoint_left.mpr fun world left right => ?_
  have apart := (programAt world.1).event_disjoint length distinct
  exact Set.disjoint_left.mp apart ((mem_observed world h).mp left) ((mem_observed world k).mp right)

noncomputable def posterior (h : List Bool) : Measure World :=
  (worldPrior (observed h))⁻¹ • worldPrior.restrict (observed h)

theorem posterior_probability (h : List Bool) : IsProbabilityMeasure (posterior h) := by
  constructor
  rw [posterior, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, observed_mass]
  have positive : mixture h ≠ 0 := by
    intro zero
    have hp := mixture_pos h
    rw [zero, ENNReal.toReal_zero] at hp
    exact (lt_irrefl 0) hp
  exact ENNReal.inv_mul_cancel positive (mixture.ne_top h)

theorem posterior_model (i : Nat) (h : List Bool) :
    posterior h (modelEvent i) = descriptionWeight i * (programAt i).semimeasure h / mixture h := by
  have measurable_model : MeasurableSet (modelEvent i) :=
    measurable_fst (measurableSet_singleton i)
  rw [posterior, Measure.smul_apply, Measure.restrict_apply measurable_model,
    model_observed_mass, observed_mass, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem posterior_predict (h : List Bool) (b : Bool) :
    posterior h (observed (h ++ [b])) = mixture (h ++ [b]) / mixture h := by
  rw [posterior, Measure.smul_apply, Measure.restrict_apply (measurable_observed _),
    Set.inter_eq_left.mpr (observed_extension h b), observed_mass, observed_mass, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

theorem predictAt_converges (h : List Bool) (b : Bool) :
    (∀ᶠ stage in atTop, (predictAt h stage b).isSome) ∧
    Tendsto (fun stage => ((predictAt h stage b).getD 0 : ℝ)) atTop
      (nhds (posterior h (observed (h ++ [b]))).toReal) := by
  simpa only [posterior_predict, ENNReal.toReal_div] using predictAt_tendsto h b

theorem posteriorAt_converges (h : List Bool) (i : Nat) :
    (∀ᶠ stage in atTop, (posteriorAt h stage i).isSome) ∧
    Tendsto (fun stage => ((posteriorAt h stage i).getD 0 : ℝ)) atTop
      (nhds (posterior h (modelEvent i)).toReal) := by
  simpa only [posterior_model, ENNReal.toReal_div] using posteriorAt_tendsto h i

theorem witnessed_update (h : List Bool) (b : Bool) :
    (worldPrior.restrict (observed h)).restrict (observed (h ++ [b])) =
      worldPrior.restrict (observed (h ++ [b])) := by
  rw [Measure.restrict_restrict (measurable_observed (h ++ [b]))]
  congr 1
  exact Set.inter_eq_left.mpr (observed_extension h b)

end Mettapedia.UniversalAI.UniversalPrediction.BitProgramJointLaw
