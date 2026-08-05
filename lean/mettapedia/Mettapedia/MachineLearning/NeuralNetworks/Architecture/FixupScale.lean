import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ResidualTransport

/-!
# Fixup scale and the first live residual update

Zhang, Dauphin, and Ma, *Fixup Initialization: Residual Learning Without
Normalization* (2019), isolate two algebraic requirements for a residual
network with `L` coherently updating branches:

* the product of all but the zero-initialized final scalar in an `m`-layer
  branch has scale `1 / sqrt L`; and
* each branch contributes at scale `1 / L`, because aligned branch changes
  add rather than cancel.

This file formalizes the scalar model behind their Equation (5), but states
the main result for heterogeneous leading coefficients rather than only a
common layer scale.  It also records the first-update boundary that is easy
to miss: zeroing the final coefficient preserves the residual identity
endpoint while keeping its first update live, whereas zeroing an earlier
coefficient as well makes that update vanish.

The positive-homogeneity definition and composition theorem recover
Definition 1 and Proposition 1 of the source independently of the scalar
branch calculation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace FixupScale

noncomputable section

/-! ## Positive homogeneity -/

variable {Input Hidden Output : Type*}
  [SMul ℝ Input] [SMul ℝ Hidden] [SMul ℝ Output]

/-- Positive homogeneity of first degree, restricted to positive scales as
in the source definition. -/
def IsPositiveHomogeneous (f : Input → Output) : Prop :=
  ∀ scale : ℝ, 0 < scale → ∀ input,
    f (scale • input) = scale • f input

/-- Source Proposition 1: composition preserves positive homogeneity. -/
theorem IsPositiveHomogeneous.comp
    {outer : Hidden → Output} {inner : Input → Hidden}
    (outerHomogeneous : IsPositiveHomogeneous outer)
    (innerHomogeneous : IsPositiveHomogeneous inner) :
    IsPositiveHomogeneous (outer ∘ inner) := by
  intro scale scalePositive input
  simp only [Function.comp_apply]
  rw [innerHomogeneous scale scalePositive input]
  exact outerHomogeneous scale scalePositive (inner input)

/-- Identity is the neutral positively homogeneous map. -/
theorem isPositiveHomogeneous_id :
    IsPositiveHomogeneous (id : Input → Input) := by
  intro scale _ input
  rfl

/-- Positive homogeneity is a real restriction: squaring is degree two, not
degree one. -/
theorem square_is_not_positiveHomogeneous :
    ¬ IsPositiveHomogeneous (fun input : ℝ => input ^ 2) := by
  intro homogeneous
  have contradiction := homogeneous 2 (by norm_num) 1
  norm_num at contradiction

/-! ## The scalar residual branch of source Equation (5) -/

/-- An `m`-layer scalar branch, split into its first `m - 1` coefficients and
its final coefficient. -/
def scalarBranch
    (leading : List ℝ) (last input : ℝ) : ℝ :=
  leading.prod * last * input

/-- Zeroing only the last coefficient makes the residual branch initially
zero, independently of the preceding coefficients. -/
@[simp]
theorem scalarBranch_zero_last
    (leading : List ℝ) (input : ℝ) :
    scalarBranch leading 0 input = 0 := by
  simp [scalarBranch]

/-- Exact finite update in the final coefficient.  In this scalar model the
first-order calculation has no remainder. -/
theorem scalarBranch_last_increment
    (leading : List ℝ) (last delta input : ℝ) :
    scalarBranch leading (last + delta) input -
        scalarBranch leading last input =
      leading.prod * delta * input := by
  simp only [scalarBranch]
  ring

/-- In particular, the first update from the zero-last-layer endpoint is
controlled exactly by the product of the preceding layers. -/
theorem scalarBranch_first_live_update
    (leading : List ℝ) (delta input : ℝ) :
    scalarBranch leading delta input -
        scalarBranch leading 0 input =
      leading.prod * delta * input := by
  simpa using
    scalarBranch_last_increment leading 0 delta input

/-- The source scaling condition on all layers before the zero-initialized
last layer.  It is stated as an exact product condition, so heterogeneous
layer scales are covered too. -/
def LeadingScaleCondition
    (branches : ℕ) (leading : List ℝ) : Prop :=
  leading.prod = (Real.sqrt (branches : ℝ))⁻¹

/-- Under the Fixup leading condition, the first live update has the claimed
inverse-square-root branch-count scale. -/
theorem scalarBranch_first_update_of_leadingScale
    {branches : ℕ} {leading : List ℝ}
    (condition : LeadingScaleCondition branches leading)
    (delta input : ℝ) :
    scalarBranch leading delta input -
        scalarBranch leading 0 input =
      (Real.sqrt (branches : ℝ))⁻¹ * delta * input := by
  rw [scalarBranch_first_live_update, condition]

/-- The source's common layer-rescaling choice is recovered whenever its
`m - 1`-st power has the required product scale. -/
theorem replicate_leadingScaleCondition
    (branches depth : ℕ) (scale : ℝ)
    (powerCondition :
      scale ^ depth = (Real.sqrt (branches : ℝ))⁻¹) :
    LeadingScaleCondition branches
      (List.replicate depth scale) := by
  simpa [LeadingScaleCondition] using powerCondition

/-- The final layer can be zero while its first update remains nonzero,
provided the preceding product, proposed update, and input are nonzero. -/
theorem scalarBranch_zero_endpoint_but_live
    {leading : List ℝ} {delta input : ℝ}
    (prefixNonzero : leading.prod ≠ 0)
    (deltaNonzero : delta ≠ 0)
    (inputNonzero : input ≠ 0) :
    scalarBranch leading 0 input = 0 ∧
      scalarBranch leading delta input ≠ 0 := by
  constructor
  · exact scalarBranch_zero_last leading input
  · simp only [scalarBranch]
    exact mul_ne_zero (mul_ne_zero prefixNonzero deltaNonzero)
      inputNonzero

/-- Negative boundary: if any preceding layer is also zero, updating only
the final coefficient cannot move the branch. -/
theorem scalarBranch_dead_if_prefix_contains_zero
    (left right : List ℝ) (delta input : ℝ) :
    scalarBranch (left ++ 0 :: right) delta input = 0 := by
  simp [scalarBranch]

/-! ## Coherent aggregation across residual branches -/

/-- The scalar model of coherently aligned residual-branch changes. -/
def coherentResidualUpdate (updates : List ℝ) : ℝ :=
  updates.sum

/-- Equal coherent branch changes accumulate linearly in the branch count. -/
theorem coherentResidualUpdate_replicate
    (branches : ℕ) (perBranch : ℝ) :
    coherentResidualUpdate
        (List.replicate branches perBranch) =
      (branches : ℝ) * perBranch := by
  simp [coherentResidualUpdate]

/-- Dividing a desired total update equally among a positive number of
coherently aligned branches recovers that total exactly. -/
theorem coherentResidualUpdate_divided
    (branches : ℕ) (branchesPositive : 0 < branches)
    (total : ℝ) :
    coherentResidualUpdate
        (List.replicate branches
          (total / (branches : ℝ))) =
      total := by
  rw [coherentResidualUpdate_replicate]
  exact mul_div_cancel₀ total
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt branchesPositive))

/-- Negative fixture: a per-branch unit update is not depth independent. -/
theorem unscaled_coherent_updates_grow :
    coherentResidualUpdate (List.replicate 4 (1 : ℝ)) = 4 := by
  norm_num [coherentResidualUpdate]

/-- Positive fixture combining the source choices: a zero final coefficient
gives a zero branch output, while the next final-coefficient update is scaled
by the certified leading product. -/
theorem two_layer_fixup :
    let leading := [(1 / 2 : ℝ)]
    LeadingScaleCondition 4 leading ∧
      scalarBranch leading 0 3 = 0 ∧
      scalarBranch leading 2 3 = 3 := by
  norm_num [LeadingScaleCondition, scalarBranch]

#print axioms IsPositiveHomogeneous.comp
#print axioms square_is_not_positiveHomogeneous
#print axioms scalarBranch_last_increment
#print axioms scalarBranch_first_update_of_leadingScale
#print axioms replicate_leadingScaleCondition
#print axioms scalarBranch_zero_endpoint_but_live
#print axioms scalarBranch_dead_if_prefix_contains_zero
#print axioms coherentResidualUpdate_divided
#print axioms unscaled_coherent_updates_grow
#print axioms two_layer_fixup

end

end FixupScale

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
