import Mathlib.Tactic

/-!
# Hidden-neuron permutation symmetry

Navon et al., *Equivariant Architectures for Learning in Deep Weight Spaces*
(ICML 2023, arXiv:2301.12780), Equation (5), act on an MLP parameter
sequence by simultaneously permuting the rows entering an intermediate layer,
its bias coordinates, and the columns leaving that layer.  The transformed
parameters represent the same function.

This file formalizes the two-layer semantic core for arbitrary finite input,
hidden, and output index types:

* hidden permutation is a genuine action on both incoming and outgoing
  parameters;
* every pointwise hidden activation gives exactly the same represented output
  after the action;
* every output-only evaluator is therefore invariant;
* an equivariant weight processor maps equivalent parameterizations to
  equivalent outputs;
* pooling across hidden coordinates is invariant;
* probing or editing one distinguished hidden coordinate need not be
  invariant or equivariant.

The results do not characterize every affine equivariant map as in the
source's Theorem 5.1, prove its universal-approximation results, cover scaling
symmetries, or establish the reported empirical performance.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

namespace HiddenNeuronPermutationSymmetry

noncomputable section

open scoped BigOperators

/-- Parameters of a two-layer network with a pointwise hidden activation.
Weights are functions so the result applies to arbitrary finite index types,
not only `Fin n` matrices. -/
structure TwoLayerParams
    (Input Hidden Output : Type*) where
  firstWeight : Hidden → Input → ℝ
  hiddenBias : Hidden → ℝ
  secondWeight : Output → Hidden → ℝ
  outputBias : Output → ℝ

/-- Activity of one hidden coordinate. -/
def hiddenActivation
    {Input Hidden Output : Type*}
    [Fintype Input]
    (params : TwoLayerParams Input Hidden Output)
    (activation : ℝ → ℝ)
    (input : Input → ℝ)
    (hidden : Hidden) : ℝ :=
  activation
    ((∑ index, params.firstWeight hidden index * input index) +
      params.hiddenBias hidden)

/-- The represented two-layer function, with a linear output layer.  An
output activation may be postcomposed without changing any invariance result
below. -/
def twoLayerOutput
    {Input Hidden Output : Type*}
    [Fintype Input] [Fintype Hidden]
    (params : TwoLayerParams Input Hidden Output)
    (activation : ℝ → ℝ)
    (input : Input → ℝ) :
    Output → ℝ :=
  fun output =>
    (∑ hidden,
      params.secondWeight output hidden *
        hiddenActivation params activation input hidden) +
      params.outputBias output

/-- Equation (5), specialized to one hidden layer: rename the incoming
weight rows, bias coordinates, and outgoing weight columns together. -/
def permuteHidden
    {Input Hidden Output : Type*}
    (permutation : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output) :
    TwoLayerParams Input Hidden Output where
  firstWeight hidden input :=
    params.firstWeight (permutation hidden) input
  hiddenBias hidden :=
    params.hiddenBias (permutation hidden)
  secondWeight output hidden :=
    params.secondWeight output (permutation hidden)
  outputBias := params.outputBias

/-- The identity renaming changes no parameter. -/
@[simp]
theorem permuteHidden_refl
    {Input Hidden Output : Type*}
    (params : TwoLayerParams Input Hidden Output) :
    permuteHidden (Equiv.refl Hidden) params = params := by
  rfl

/-- Successive hidden renamings compose as permutations. -/
theorem permuteHidden_comp
    {Input Hidden Output : Type*}
    (first second : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output) :
    permuteHidden first (permuteHidden second params) =
      permuteHidden (first.trans second) params := by
  rfl

/-- Hidden activities are equivariant: the renamed coordinate carries the
activity of the corresponding original coordinate. -/
@[simp]
theorem hiddenActivation_permuteHidden
    {Input Hidden Output : Type*}
    [Fintype Input]
    (permutation : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output)
    (activation : ℝ → ℝ)
    (input : Input → ℝ)
    (hidden : Hidden) :
    hiddenActivation (permuteHidden permutation params)
        activation input hidden =
      hiddenActivation params activation input
        (permutation hidden) := by
  rfl

/-- The source's semantic crown: simultaneous incoming/bias/outgoing
permutation preserves the represented function for every pointwise
activation and every input. -/
theorem twoLayerOutput_permuteHidden
    {Input Hidden Output : Type*}
    [Fintype Input] [Fintype Hidden]
    (permutation : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output)
    (activation : ℝ → ℝ)
    (input : Input → ℝ) :
    twoLayerOutput (permuteHidden permutation params)
        activation input =
      twoLayerOutput params activation input := by
  funext output
  simp only [twoLayerOutput, hiddenActivation, permuteHidden]
  congr 1
  simpa only [] using
    Equiv.sum_comp
      (permutation : Hidden ≃ Hidden)
      (fun hidden =>
        params.secondWeight output hidden *
          activation
            ((∑ index,
              params.firstWeight hidden index * input index) +
              params.hiddenBias hidden))

/-- Any evaluator that observes only the represented output is invariant to
the hidden-coordinate naming convention. -/
theorem outputFunctional_permuteHidden
    {Input Hidden Output Result : Type*}
    [Fintype Input] [Fintype Hidden]
    (functional : (Output → ℝ) → Result)
    (permutation : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output)
    (activation : ℝ → ℝ)
    (input : Input → ℝ) :
    functional
        (twoLayerOutput (permuteHidden permutation params)
          activation input) =
      functional (twoLayerOutput params activation input) := by
  rw [twoLayerOutput_permuteHidden]

/-- A raw-parameter statistic is hidden-permutation invariant when it is
constant on every parameter orbit. -/
def IsHiddenPermutationInvariant
    {Input Hidden Output Result : Type*}
    (processor : TwoLayerParams Input Hidden Output → Result) :
    Prop :=
  ∀ (permutation : Equiv.Perm Hidden) params,
    processor (permuteHidden permutation params) = processor params

/-- A weight-space processor is hidden-permutation equivariant when applying
it before or after a hidden renaming gives the same renamed parameters. -/
def IsHiddenPermutationEquivariant
    {Input Hidden Output : Type*}
    (processor :
      TwoLayerParams Input Hidden Output →
        TwoLayerParams Input Hidden Output) :
    Prop :=
  ∀ (permutation : Equiv.Perm Hidden) params,
    processor (permuteHidden permutation params) =
      permuteHidden permutation (processor params)

/-- The represented output is an invariant raw-parameter evaluator. -/
theorem representedOutput_isHiddenPermutationInvariant
    {Input Hidden Output : Type*}
    [Fintype Input] [Fintype Hidden]
    (activation : ℝ → ℝ)
    (input : Input → ℝ) :
    IsHiddenPermutationInvariant
      (fun params : TwoLayerParams Input Hidden Output =>
        twoLayerOutput params activation input) := by
  intro permutation params
  exact
    twoLayerOutput_permuteHidden
      permutation params activation input

/-- An equivariant learned weight processor is well-defined on functional
parameter orbits: equivalent inputs remain equivalent after processing. -/
theorem equivariantProcessor_preserves_output_orbits
    {Input Hidden Output : Type*}
    [Fintype Input] [Fintype Hidden]
    (processor :
      TwoLayerParams Input Hidden Output →
        TwoLayerParams Input Hidden Output)
    (processor_equivariant :
      IsHiddenPermutationEquivariant processor)
    (permutation : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output)
    (activation : ℝ → ℝ)
    (input : Input → ℝ) :
    twoLayerOutput
        (processor (permuteHidden permutation params))
        activation input =
      twoLayerOutput (processor params) activation input := by
  rw [processor_equivariant permutation params]
  exact
    twoLayerOutput_permuteHidden
      permutation (processor params) activation input

/-- Pooling all incoming weights across hidden coordinates is an invariant
operation of the kind used by deep-weight-space architectures. -/
def pooledFirstWeight
    {Input Hidden Output : Type*}
    [Fintype Input] [Fintype Hidden]
    (params : TwoLayerParams Input Hidden Output) :
    ℝ :=
  ∑ hidden, ∑ input, params.firstWeight hidden input

/-- Hidden-coordinate pooling is permutation invariant. -/
theorem pooledFirstWeight_isHiddenPermutationInvariant
    {Input Hidden Output : Type*}
    [Fintype Input] [Fintype Hidden] :
    IsHiddenPermutationInvariant
      (pooledFirstWeight
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro permutation params
  simp only [pooledFirstWeight, permuteHidden]
  exact
    Equiv.sum_comp
      (permutation : Hidden ≃ Hidden)
      (fun hidden => ∑ input, params.firstWeight hidden input)

/-- A coordinate-sensitive diagnostic that reads one named hidden bias. -/
def hiddenBiasProbe
    {Input Hidden Output : Type*}
    (chosen : Hidden)
    (params : TwoLayerParams Input Hidden Output) :
    ℝ :=
  params.hiddenBias chosen

/-- The coordinate-sensitive probe follows the coordinate renaming. -/
@[simp]
theorem hiddenBiasProbe_permuteHidden
    {Input Hidden Output : Type*}
    (chosen : Hidden)
    (permutation : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output) :
    hiddenBiasProbe chosen (permuteHidden permutation params) =
      params.hiddenBias (permutation chosen) := by
  rfl

/-- A coordinate-sensitive processor that zeroes one named hidden bias. -/
def zeroHiddenBias
    {Input Hidden Output : Type*}
    [DecidableEq Hidden]
    (chosen : Hidden)
    (params : TwoLayerParams Input Hidden Output) :
    TwoLayerParams Input Hidden Output :=
  { params with
    hiddenBias := Function.update params.hiddenBias chosen 0 }

section Fixtures

/-- Swap the two hidden coordinates in the executable fixture. -/
def finTwoSwap :
    Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

/-- Nondegenerate two-hidden-unit fixture: every weight and bias is nonzero. -/
def permutationFixture :
    TwoLayerParams (Fin 1) (Fin 2) (Fin 1) where
  firstWeight hidden _ :=
    if hidden = 0 then 2 else 3
  hiddenBias hidden :=
    if hidden = 0 then 5 else 7
  secondWeight _ hidden :=
    if hidden = 0 then 11 else 13
  outputBias _ := 17

/-- The original fixture evaluates to a nontrivial output. -/
theorem permutationFixture_output :
    twoLayerOutput permutationFixture id (fun _ => 1) 0 =
      224 := by
  norm_num
    [twoLayerOutput, hiddenActivation, permutationFixture]

/-- Swapping the two hidden units preserves that same nontrivial output. -/
theorem permutationFixture_permuted_output :
    twoLayerOutput
        (permuteHidden finTwoSwap permutationFixture)
        id (fun _ => 1) 0 =
      224 := by
  rw [twoLayerOutput_permuteHidden]
  exact permutationFixture_output

/-- Negative boundary: a raw coordinate probe distinguishes two parameter
vectors representing exactly the same function. -/
theorem hiddenBiasProbe_not_invariant :
    hiddenBiasProbe 0
        (permuteHidden finTwoSwap permutationFixture) ≠
      hiddenBiasProbe 0 permutationFixture := by
  norm_num
    [hiddenBiasProbe, permuteHidden, finTwoSwap,
      permutationFixture, Equiv.swap_apply_def]

/-- Negative boundary: editing a fixed raw coordinate is not an equivariant
weight-space processor. -/
theorem zeroFirstHiddenBias_not_equivariant :
    ¬ IsHiddenPermutationEquivariant
      (zeroHiddenBias
        (Input := Fin 1) (Output := Fin 1) (0 : Fin 2)) := by
  intro supposedly_equivariant
  have parameter_equality :=
    supposedly_equivariant finTwoSwap permutationFixture
  have bias_equality :=
    congrArg
      (fun params : TwoLayerParams (Fin 1) (Fin 2) (Fin 1) =>
        params.hiddenBias 0)
      parameter_equality
  norm_num
    [zeroHiddenBias, permuteHidden, finTwoSwap,
      permutationFixture, Equiv.swap_apply_def]
    at bias_equality

end Fixtures

end

end HiddenNeuronPermutationSymmetry

end Mettapedia.MachineLearning.NeuralNetworks

#print axioms
  Mettapedia.MachineLearning.NeuralNetworks.HiddenNeuronPermutationSymmetry.twoLayerOutput_permuteHidden
#print axioms
  Mettapedia.MachineLearning.NeuralNetworks.HiddenNeuronPermutationSymmetry.equivariantProcessor_preserves_output_orbits
#print axioms
  Mettapedia.MachineLearning.NeuralNetworks.HiddenNeuronPermutationSymmetry.zeroFirstHiddenBias_not_equivariant
