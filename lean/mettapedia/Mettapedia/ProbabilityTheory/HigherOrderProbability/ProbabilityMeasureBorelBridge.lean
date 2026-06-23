import Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Defs.Filter
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# ProbabilityMeasure Borel Bridge

Local bridge lemmas to derive `BorelSpace (ProbabilityMeasure Ω)` from
`BorelSpace (FiniteMeasure Ω)` via `ProbabilityMeasure.toFiniteMeasure`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability

open MeasureTheory
open Filter
open scoped NNReal ENNReal

namespace ProbabilityMeasureBorelBridge

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Generic compact-embedding Borel bridge -/

/-- Reusable compact/T2 embedding pattern:
if `f : α → β` is continuous and injective from a compact space into a
Hausdorff codomain, and `f` is measurable with respect to the ambient measurable
space on `α` and the Borel measurable space on `β`, then
`borel α ≤` the ambient measurable space on `α`. -/
theorem borel_le_of_continuous_injective_compact_t2_measurable
    {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [CompactSpace α] [T2Space β]
    {f : α → β}
    (hcont : Continuous f)
    (hinj : Function.Injective f)
    (hmeas : Measurable f) :
    borel α ≤ (inferInstance : MeasurableSpace α) := by
  have hEmbTop : Topology.IsEmbedding f :=
    (hcont.isClosedEmbedding hinj).isEmbedding
  have htop :
      (inferInstance : TopologicalSpace α) =
        TopologicalSpace.induced f (inferInstance : TopologicalSpace β) :=
    hEmbTop.eq_induced
  have hmeasBorel :
      @Measurable α β
        (inferInstance : MeasurableSpace α)
        (borel β)
        f :=
    ‹BorelSpace β›.measurable_eq ▸ hmeas
  calc
    borel α = MeasurableSpace.comap f (borel β) :=
      hEmbTop.eq_induced ▸ borel_comap
    _ ≤ (inferInstance : MeasurableSpace α) :=
      hmeasBorel.comap_le

/-! ## Measurability of weak-dual coordinates -/

private theorem measurable_toWeakDualBCNN_apply
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (f : BoundedContinuousFunction Ω ℝ≥0) :
    Measurable (fun μ : FiniteMeasure Ω => μ.toWeakDualBCNN f) := by
  -- The coordinate is a nonnegative integral; measurability follows from the Giry measurable space.
  have hmeas :
      Measurable (fun μ : Measure Ω => ∫⁻ x, (f x : ℝ≥0∞) ∂μ) :=
    Measure.measurable_lintegral
      (f := fun x => (f x : ℝ≥0∞)) f.continuous.measurable.coe_nnreal_ennreal
  have hmeas' :
      Measurable (fun μ : FiniteMeasure Ω => ∫⁻ x, (f x : ℝ≥0∞) ∂(μ : Measure Ω)) :=
    hmeas.comp measurable_subtype_coe
  simpa using hmeas'.ennreal_toNNReal


private theorem upperSemicontinuous_apply_closed
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    (F : Set Ω) (hF : IsClosed F) :
    UpperSemicontinuous (fun μ : FiniteMeasure Ω => (μ : Measure Ω) F) := by
  refine (upperSemicontinuous_iff_limsup_le).2 ?_
  intro μ
  simpa using
    (FiniteMeasure.limsup_measure_closed_le_of_tendsto
      (Ω := Ω) (L := nhds μ) (μ := μ)
      (μs := fun ν : FiniteMeasure Ω => ν)
      (μs_lim := (tendsto_id : Tendsto (fun ν : FiniteMeasure Ω => ν) (nhds μ) (nhds μ)))
      hF)

private theorem measurable_apply_closed
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    (F : Set Ω) (hF : IsClosed F) :
    @Measurable (FiniteMeasure Ω) ℝ≥0∞ (borel (FiniteMeasure Ω)) _
      (fun μ : FiniteMeasure Ω => (μ : Measure Ω) F) := by
  -- Work with the Borel measurable space on `FiniteMeasure Ω`.
  letI : MeasurableSpace (FiniteMeasure Ω) := borel (FiniteMeasure Ω)
  haveI : BorelSpace (FiniteMeasure Ω) := ⟨rfl⟩
  haveI : OpensMeasurableSpace (FiniteMeasure Ω) := inferInstance
  exact (UpperSemicontinuous.measurable
    (f := fun μ : FiniteMeasure Ω => (μ : Measure Ω) F)
    (upperSemicontinuous_apply_closed (Ω := Ω) F hF))

private theorem measurable_coe_finiteMeasure_of_closed
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω] :
    @Measurable (FiniteMeasure Ω) (Measure Ω) (borel (FiniteMeasure Ω)) _
      (fun μ : FiniteMeasure Ω => (μ : Measure Ω)) := by
  -- Work with the Borel measurable space on `FiniteMeasure Ω`.
  letI : MeasurableSpace (FiniteMeasure Ω) := borel (FiniteMeasure Ω)
  haveI : BorelSpace (FiniteMeasure Ω) := ⟨rfl⟩
  haveI : OpensMeasurableSpace (FiniteMeasure Ω) := inferInstance
  refine (Measurable.measure_of_isPiSystem
    (μ := fun μ : FiniteMeasure Ω => (μ : Measure Ω))
    (S := {s : Set Ω | IsClosed s})
    ?hgen ?hpi ?h_basic ?h_univ)
  · simpa [BorelSpace.measurable_eq] using (borel_eq_generateFrom_isClosed (α := Ω))
  · exact isPiSystem_isClosed
  · intro s hs
    exact measurable_apply_closed (Ω := Ω) s hs
  · -- `univ` is closed, so this follows from the closed-set case.
    simpa using (measurable_apply_closed (Ω := Ω) Set.univ isClosed_univ)

/-- Portmanteau/closed-set direction:
the Giry measurable structure on `FiniteMeasure Ω` is contained in the weak-topology
Borel σ-algebra. -/
theorem instMeasurable_le_borel_finiteMeasure
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω] :
    (inferInstance : MeasurableSpace (FiniteMeasure Ω)) ≤ borel (FiniteMeasure Ω) := by
  -- The Giry measurable space is the comap of `Measure.instMeasurableSpace` by coercion.
  have hcoe :
      @Measurable (FiniteMeasure Ω) (Measure Ω) (borel (FiniteMeasure Ω)) _
        (fun μ : FiniteMeasure Ω => (μ : Measure Ω)) :=
    measurable_coe_finiteMeasure_of_closed (Ω := Ω)
  -- Rewrite the comap into the Borel space.
  exact hcoe.comap_le

/-- Portmanteau/closed-set direction transported to probability measures:
the Giry measurable structure on `ProbabilityMeasure Ω` is contained in the
convergence-in-distribution Borel σ-algebra. -/
theorem instMeasurable_le_borel_probabilityMeasure
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω] :
    (inferInstance : MeasurableSpace (ProbabilityMeasure Ω)) ≤ borel (ProbabilityMeasure Ω) := by
  have htoFin :
      @Measurable (ProbabilityMeasure Ω) (FiniteMeasure Ω)
        (borel (ProbabilityMeasure Ω))
        (borel (FiniteMeasure Ω))
        ProbabilityMeasure.toFiniteMeasure :=
    ProbabilityMeasure.toFiniteMeasure_continuous.borel_measurable
  have hcoeFin :
      @Measurable (FiniteMeasure Ω) (Measure Ω)
        (borel (FiniteMeasure Ω))
        (inferInstance : MeasurableSpace (Measure Ω))
        (fun μ : FiniteMeasure Ω => (μ : Measure Ω)) :=
    measurable_coe_finiteMeasure_of_closed (Ω := Ω)
  have hcoe :
      @Measurable (ProbabilityMeasure Ω) (Measure Ω)
        (borel (ProbabilityMeasure Ω))
        (inferInstance : MeasurableSpace (Measure Ω))
        (fun μ : ProbabilityMeasure Ω => (μ : Measure Ω)) :=
    hcoeFin.comp htoFin
  exact hcoe.comap_le

/-- Abstract Lévy–Prokhorov bridge:
if `LevyProkhorov.ofMeasure` is measurable from the Giry measurable space on
`ProbabilityMeasure Ω` to the LP-Borel measurable space, then
`ProbabilityMeasure Ω` carries the convergence-in-distribution Borel measurable structure.

This theorem isolates the remaining measurable-transport crux cleanly. -/
theorem borelSpace_probabilityMeasure_of_levyProkhorov_ofMeasure_measurable
    [PseudoMetricSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
    (hOfMeasure :
      @Measurable (ProbabilityMeasure Ω) (LevyProkhorov (ProbabilityMeasure Ω))
        (inferInstance : MeasurableSpace (ProbabilityMeasure Ω))
        (borel (LevyProkhorov (ProbabilityMeasure Ω)))
        LevyProkhorov.ofMeasure) :
    BorelSpace (ProbabilityMeasure Ω) := by
  let X := LevyProkhorov (ProbabilityMeasure Ω)
  letI : PseudoMetricSpace X :=
    MeasureTheory.LevyProkhorov.instPseudoMetricSpaceProbabilityMeasure
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  let e : ProbabilityMeasure Ω → X := LevyProkhorov.ofMeasure
  have hinst_le_borel :
      (inferInstance : MeasurableSpace (ProbabilityMeasure Ω)) ≤
        borel (ProbabilityMeasure Ω) :=
    instMeasurable_le_borel_probabilityMeasure (Ω := Ω)
  have hset_range : MeasurableSet (Set.range e) := by
    have hrange : Set.range e = Set.univ := by
      ext x
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨LevyProkhorov.toMeasure x, rfl⟩
    simp [hrange]
  let g : Set.range e → ProbabilityMeasure Ω := fun x => LevyProkhorov.toMeasure x.1
  have hg_meas_borel :
      @Measurable (Set.range e) (ProbabilityMeasure Ω)
        (Subtype.instMeasurableSpace : MeasurableSpace (Set.range e))
        (borel (ProbabilityMeasure Ω)) g := by
    refine
      (LevyProkhorov.continuous_toMeasure_probabilityMeasure
        (Ω := Ω)).borel_measurable.comp ?_
    exact
      (measurable_subtype_coe :
        @Measurable (Set.range e) X
          (Subtype.instMeasurableSpace : MeasurableSpace (Set.range e))
          (borel X) Subtype.val)
  have hg_meas :
      @Measurable (Set.range e) (ProbabilityMeasure Ω)
        (Subtype.instMeasurableSpace : MeasurableSpace (Set.range e))
        (inferInstance : MeasurableSpace (ProbabilityMeasure Ω)) g :=
    hg_meas_borel.mono le_rfl hinst_le_borel
  have hleft : Function.LeftInverse g (Set.rangeFactorization e) := by
    intro μ
    rfl
  have hEmb : MeasurableEmbedding e :=
    MeasurableEmbedding.of_measurable_inverse_on_range
      (hf₁ := hOfMeasure) (hf₂ := hset_range) (hg := hg_meas) (H := hleft)
  exact hEmb.borelSpace (LevyProkhorov.probabilityMeasureHomeomorph (Ω := Ω)).isInducing

/-- Alias of the abstract LP bridge (kept as the primary theorem name used by
downstream files). -/
theorem borelSpace_probabilityMeasure_of_levyProkhorov
    [PseudoMetricSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
    (hOfMeasure :
      @Measurable (ProbabilityMeasure Ω) (LevyProkhorov (ProbabilityMeasure Ω))
        (inferInstance : MeasurableSpace (ProbabilityMeasure Ω))
        (borel (LevyProkhorov (ProbabilityMeasure Ω)))
        LevyProkhorov.ofMeasure) :
    BorelSpace (ProbabilityMeasure Ω) := by
  exact borelSpace_probabilityMeasure_of_levyProkhorov_ofMeasure_measurable
    (Ω := Ω) hOfMeasure

/-- Reduction lemma for the LP bridge:
if the weak-topology Borel σ-algebra on `ProbabilityMeasure Ω` is already known
to be contained in the Giry measurable structure, continuity of `ofMeasure`
upgrades to the measurable transport hypothesis required by the LP bridge. -/
theorem borelSpace_probabilityMeasure_of_borel_le_inst
    [PseudoMetricSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
    (hborel : borel (ProbabilityMeasure Ω) ≤
      (inferInstance : MeasurableSpace (ProbabilityMeasure Ω))) :
    BorelSpace (ProbabilityMeasure Ω) := by
  have hOfMeasure :
      @Measurable (ProbabilityMeasure Ω) (LevyProkhorov (ProbabilityMeasure Ω))
        (inferInstance : MeasurableSpace (ProbabilityMeasure Ω))
        (borel (LevyProkhorov (ProbabilityMeasure Ω)))
        LevyProkhorov.ofMeasure :=
    ((LevyProkhorov.continuous_ofMeasure_probabilityMeasure (Ω := Ω)).borel_measurable).mono
      hborel le_rfl
  exact borelSpace_probabilityMeasure_of_levyProkhorov (Ω := Ω) hOfMeasure

/-- Standard-Borel corollary of the abstract LP bridge. -/
theorem standardBorelSpace_probabilityMeasure_of_levyProkhorov_ofMeasure_measurable
    [PseudoMetricSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
    [PolishSpace (ProbabilityMeasure Ω)]
    (hOfMeasure :
      @Measurable (ProbabilityMeasure Ω) (LevyProkhorov (ProbabilityMeasure Ω))
        (inferInstance : MeasurableSpace (ProbabilityMeasure Ω))
        (borel (LevyProkhorov (ProbabilityMeasure Ω)))
        LevyProkhorov.ofMeasure) :
    StandardBorelSpace (ProbabilityMeasure Ω) := by
  letI : BorelSpace (ProbabilityMeasure Ω) :=
    borelSpace_probabilityMeasure_of_levyProkhorov_ofMeasure_measurable
      (Ω := Ω) hOfMeasure
  infer_instance

/-- Alias of the standard-Borel corollary of the abstract LP bridge. -/
theorem standardBorelSpace_probabilityMeasure_of_levyProkhorov
    [PseudoMetricSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
    [PolishSpace (ProbabilityMeasure Ω)]
    (hOfMeasure :
      @Measurable (ProbabilityMeasure Ω) (LevyProkhorov (ProbabilityMeasure Ω))
        (inferInstance : MeasurableSpace (ProbabilityMeasure Ω))
        (borel (LevyProkhorov (ProbabilityMeasure Ω)))
        LevyProkhorov.ofMeasure) :
    StandardBorelSpace (ProbabilityMeasure Ω) := by
  exact
    standardBorelSpace_probabilityMeasure_of_levyProkhorov_ofMeasure_measurable
      (Ω := Ω) hOfMeasure

/-- Standard-Borel corollary of `borelSpace_probabilityMeasure_of_borel_le_inst`. -/
theorem standardBorelSpace_probabilityMeasure_of_borel_le_inst
    [PseudoMetricSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
    [PolishSpace (ProbabilityMeasure Ω)]
    (hborel : borel (ProbabilityMeasure Ω) ≤
      (inferInstance : MeasurableSpace (ProbabilityMeasure Ω))) :
    StandardBorelSpace (ProbabilityMeasure Ω) := by
  letI : BorelSpace (ProbabilityMeasure Ω) :=
    borelSpace_probabilityMeasure_of_borel_le_inst (Ω := Ω) hborel
  infer_instance

/-- Reverse inclusion for finite-measure weak Borel:
`borel (FiniteMeasure Ω)` is contained in the Giry measurable structure. -/
-- NOTE: The reverse inclusion `borel (FiniteMeasure Ω) ≤ instMeasurableSpace` is the
-- remaining crux. It likely needs a direct measurability proof using `isOpen_pi_iff` or a
-- countable-basis reduction for the weak-* topology. We keep the Portmanteau direction above
-- (instMeasurable ≤ borel) intact.

private theorem measurable_toFiniteMeasure :
    Measurable (ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) := by
  have hfin :
      ∀ x : ProbabilityMeasure Ω,
        IsFiniteMeasure ((fun μ : ProbabilityMeasure Ω => (μ : Measure Ω)) x) := by
    intro x
    infer_instance
  exact
    (Measurable.subtype_mk
      (hf := (measurable_subtype_coe :
        Measurable (fun μ : ProbabilityMeasure Ω => (μ : Measure Ω))))
      (h := hfin))

private theorem measurableSet_range_toFiniteMeasure :
    MeasurableSet
      (Set.range (ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω)) := by
  rw [ProbabilityMeasure.range_toFiniteMeasure]
  have hmassENN :
      Measurable (fun μ : FiniteMeasure Ω => (μ : Measure Ω) Set.univ) :=
    (Measure.measurable_coe (α := Ω) MeasurableSet.univ).comp measurable_subtype_coe
  have hmass : Measurable (fun μ : FiniteMeasure Ω => μ.mass) :=
    hmassENN.ennreal_toNNReal
  exact hmass (measurableSet_singleton (1 : NNReal))

private def fromRangeToProbabilityMeasure
    (x : Set.range (ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω)) :
    ProbabilityMeasure Ω := by
  refine ⟨(x.1 : Measure Ω), ?_⟩
  rcases x.2 with ⟨μ, hμ⟩
  have hcoe : ((x.1 : FiniteMeasure Ω) : Measure Ω) = (μ : Measure Ω) := by
    simpa [ProbabilityMeasure.toFiniteMeasure] using
      congrArg (fun ν : FiniteMeasure Ω => (ν : Measure Ω)) hμ.symm
  simpa [hcoe] using (inferInstance : IsProbabilityMeasure (μ : Measure Ω))

private theorem measurable_fromRangeToProbabilityMeasure :
    Measurable
      (fromRangeToProbabilityMeasure
        (Ω := Ω)
        : Set.range (ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) →
            ProbabilityMeasure Ω) := by
  have hprob :
      ∀ x :
        Set.range (ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω),
        IsProbabilityMeasure
          ((fun x :
            Set.range (ProbabilityMeasure.toFiniteMeasure :
              ProbabilityMeasure Ω → FiniteMeasure Ω) =>
                ((x.1 : FiniteMeasure Ω) : Measure Ω)) x) := by
    intro x
    rcases x.2 with ⟨μ, hμ⟩
    have hcoe : ((x.1 : FiniteMeasure Ω) : Measure Ω) = (μ : Measure Ω) := by
      simpa [ProbabilityMeasure.toFiniteMeasure] using
        congrArg (fun ν : FiniteMeasure Ω => (ν : Measure Ω)) hμ.symm
    simpa [hcoe] using (inferInstance : IsProbabilityMeasure (μ : Measure Ω))
  exact
    (Measurable.subtype_mk
      (hf := (measurable_subtype_coe.comp measurable_subtype_coe :
        Measurable (fun x :
          Set.range (ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) =>
            ((x.1 : FiniteMeasure Ω) : Measure Ω))))
      (h := hprob))

private theorem leftInverse_fromRangeToProbabilityMeasure :
    Function.LeftInverse
      (fromRangeToProbabilityMeasure
        (Ω := Ω))
      (Set.rangeFactorization
        (ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω)) := by
  intro μ
  apply Subtype.ext
  rfl

/-- Measurable embedding of `ProbabilityMeasure.toFiniteMeasure`. -/
theorem measurableEmbedding_toFiniteMeasure :
    MeasurableEmbedding
      (ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) := by
  refine MeasurableEmbedding.of_measurable_inverse_on_range
    (hf₁ := measurable_toFiniteMeasure (Ω := Ω))
    (hf₂ := measurableSet_range_toFiniteMeasure (Ω := Ω))
    (hg := measurable_fromRangeToProbabilityMeasure (Ω := Ω))
    (H := leftInverse_fromRangeToProbabilityMeasure (Ω := Ω))

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- Bridge theorem:
if the weak-topology measurable structure on `FiniteMeasure Ω` is Borel,
then the same holds for `ProbabilityMeasure Ω`. -/
theorem borelSpace_probabilityMeasure_of_finiteMeasure
    [BorelSpace (FiniteMeasure Ω)] :
    BorelSpace (ProbabilityMeasure Ω) := by
  exact
    (measurableEmbedding_toFiniteMeasure (Ω := Ω)).borelSpace
      (ProbabilityMeasure.toFiniteMeasure_isEmbedding Ω).isInducing

/-- Theorem-level standard-Borel bridge:
if `ProbabilityMeasure Ω` is Polish and finite-measure weak Borel is available,
then `ProbabilityMeasure Ω` is standard Borel via the finite→probability Borel bridge. -/
theorem standardBorelSpace_probabilityMeasure_of_finiteMeasure
    [BorelSpace (FiniteMeasure Ω)] [PolishSpace (ProbabilityMeasure Ω)] :
    StandardBorelSpace (ProbabilityMeasure Ω) := by
  letI : BorelSpace (ProbabilityMeasure Ω) :=
    borelSpace_probabilityMeasure_of_finiteMeasure (Ω := Ω)
  infer_instance

/-- Latent-Theta specialization used by the Giry de Finetti route. -/
instance latentTheta_borelSpace_probabilityMeasure
    [BorelSpace (FiniteMeasure DeFinettiConnection.Theta)] :
    BorelSpace (ProbabilityMeasure DeFinettiConnection.Theta) := by
  simpa using
    (borelSpace_probabilityMeasure_of_finiteMeasure
      (Ω := DeFinettiConnection.Theta))

end ProbabilityMeasureBorelBridge

end Mettapedia.ProbabilityTheory.HigherOrderProbability
