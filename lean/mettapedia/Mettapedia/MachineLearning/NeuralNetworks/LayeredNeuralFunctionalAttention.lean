import Mettapedia.MachineLearning.NeuralNetworks.LayeredWeightSpace

/-!
# Boundary-aware arbitrary-depth neural-functional attention

This module assembles the local Neural Functional Transformer attention
equations over the heterogeneous arbitrary-depth weight space.

The recursion carries the preceding weight matrix as context.  At the first
matrix that context has an empty source type; at the last matrix the
following target type is empty.  Internal recursive calls pass the current
matrix as the next step's preceding matrix.  The global point-attention head
continues to range over the complete network at every depth.

This construction contains no padded neurons or weights.  Every row and
column in every local head belongs to an actual adjacent layer.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

open Architecture

noncomputable section

universe u uGlobal uChannel

/-- The unique matrix whose column type is empty. -/
def emptyPreviousWeight
    {Middle : Type*} {Channel : Type*} :
    Middle → PEmpty → Channel → ℝ :=
  fun _ empty => nomatch empty

/-- The unique matrix whose row type is empty. -/
def emptyNextWeight
    {Current : Type*} {Channel : Type*} :
    PEmpty → Current → Channel → ℝ :=
  fun empty => nomatch empty

/-- Recursive implementation with a preceding-matrix context and an
embedding of the current tail's coordinates into the complete weight space.
-/
def layeredNeuralFunctionalAttentionFrom
    {GlobalCoordinate : Type uGlobal}
    {Previous : Type u}
    {Channel : Type uChannel}
    [Fintype GlobalCoordinate] [Fintype Previous] [Fintype Channel]
    (globalQueries globalKeys globalValues :
      GlobalCoordinate → Channel → ℝ)
    (input : FiniteNeuronLayer.{u})
    (tail : List (FiniteNeuronLayer.{u}))
    (embed :
      LayeredWeightCoordinate (input :: tail) → GlobalCoordinate)
    (keyPrevious valuePrevious :
      input.carrier → Previous → Channel → ℝ)
    (queries keys values :
      LayeredWeightFeatures (input :: tail) Channel) :
    LayeredWeightFeatures (input :: tail) Channel :=
  match tail with
  | [] =>
      fun coordinate => nomatch coordinate
  | [output] =>
      fun coordinate channel =>
        match coordinate with
        | Sum.inl (row, column) =>
            neuralFunctionalAttentionEntry
              (firstWeightMatrix queries)
              keyPrevious
              (firstWeightMatrix keys)
              (emptyNextWeight
                (Current := output.carrier) (Channel := Channel) :
                  PEmpty.{u + 1} → output.carrier → Channel → ℝ)
              valuePrevious
              (firstWeightMatrix values)
              (emptyNextWeight
                (Current := output.carrier) (Channel := Channel) :
                  PEmpty.{u + 1} → output.carrier → Channel → ℝ)
              globalQueries globalKeys globalValues
              row column (embed coordinate) channel
        | Sum.inr empty => nomatch empty
  | output :: next :: rest =>
      fun coordinate channel =>
        match coordinate with
        | Sum.inl (row, column) =>
            neuralFunctionalAttentionEntry
              (firstWeightMatrix queries)
              keyPrevious
              (firstWeightMatrix keys)
              (firstWeightMatrix (tailWeightFeatures keys))
              valuePrevious
              (firstWeightMatrix values)
              (firstWeightMatrix (tailWeightFeatures values))
              globalQueries globalKeys globalValues
              row column (embed coordinate) channel
        | Sum.inr later =>
            layeredNeuralFunctionalAttentionFrom
              (Previous := input.carrier)
              globalQueries globalKeys globalValues
              output (next :: rest)
              (fun coordinate => embed (Sum.inr coordinate))
              (firstWeightMatrix keys)
              (firstWeightMatrix values)
              (tailWeightFeatures queries)
              (tailWeightFeatures keys)
              (tailWeightFeatures values)
              later channel
termination_by tail.length

/-- Full boundary-aware neural-functional self-attention over all matrices in
a heterogeneous feed-forward network. -/
def layeredNeuralFunctionalAttention
    {Channel : Type uChannel} [Fintype Channel]
    (layers : List (FiniteNeuronLayer.{u}))
    (queries keys values : LayeredWeightFeatures layers Channel) :
    LayeredWeightFeatures layers Channel :=
  match layers with
  | [] => fun coordinate => nomatch coordinate
  | input :: tail =>
      layeredNeuralFunctionalAttentionFrom
        (Previous := PEmpty.{u + 1})
        queries keys values input tail
        id
        (emptyPreviousWeight
          (Middle := input.carrier) (Channel := Channel))
        (emptyPreviousWeight
          (Middle := input.carrier) (Channel := Channel))
        queries keys values

/-! ## Exact transport at the terminal matrix -/

/-- Relabeling a missing preceding matrix leaves its unique function
unchanged. -/
theorem transportMatrix_emptyPreviousWeight
    {Middle : Type u} {Channel : Type uChannel}
    [Fintype Channel]
    (middleRelabel : Equiv.Perm Middle) :
    transportMatrix middleRelabel (Equiv.refl PEmpty.{u + 1})
        (emptyPreviousWeight
          (Middle := Middle) (Channel := Channel) :
            Middle → PEmpty.{u + 1} → Channel → ℝ) =
      emptyPreviousWeight := by
  funext _ empty
  exact nomatch empty

/-- Relabeling a missing following matrix leaves its unique function
unchanged. -/
theorem transportMatrix_emptyNextWeight
    {Current : Type u} {Channel : Type uChannel}
    [Fintype Channel]
    (currentRelabel : Equiv.Perm Current) :
    transportMatrix (Equiv.refl PEmpty.{u + 1}) currentRelabel
        (emptyNextWeight
          (Current := Current) (Channel := Channel) :
            PEmpty.{u + 1} → Current → Channel → ℝ) =
      emptyNextWeight := by
  funext empty
  exact nomatch empty

/-- At the final weight matrix, the executable boundary-aware layer commutes
with independent relabelings of the preceding, source, target, and global
weight-coordinate types.  The absent following layer is represented by the
unique equivalence of empty types. -/
theorem layeredNeuralFunctionalAttentionFrom_last_transport
    {GlobalCoordinate : Type uGlobal}
    {Previous : Type u}
    {Channel : Type uChannel}
    [Fintype GlobalCoordinate] [Fintype Previous] [Fintype Channel]
    (globalRelabel : Equiv.Perm GlobalCoordinate)
    (previousRelabel : Equiv.Perm Previous)
    (input output : FiniteNeuronLayer.{u})
    (inputRelabel : Equiv.Perm input.carrier)
    (outputRelabel : Equiv.Perm output.carrier)
    (embedLeft embedRight :
      LayeredWeightCoordinate [input, output] → GlobalCoordinate)
    (embedTransport :
      ∀ coordinate,
        embedRight
            (genuineLayerWeightEquiv [input, output]
              (inputRelabel,
                (outputRelabel, PUnit.unit)) coordinate) =
          globalRelabel (embedLeft coordinate))
    (globalQueries globalKeys globalValues :
      GlobalCoordinate → Channel → ℝ)
    (keyPrevious valuePrevious :
      input.carrier → Previous → Channel → ℝ)
    (queries keys values :
      LayeredWeightFeatures [input, output] Channel)
    (coordinate : LayeredWeightCoordinate [input, output])
    (channel : Channel) :
    layeredNeuralFunctionalAttentionFrom
        (transportRows globalRelabel globalQueries)
        (transportRows globalRelabel globalKeys)
        (transportRows globalRelabel globalValues)
        input [output] embedRight
        (transportMatrix inputRelabel previousRelabel keyPrevious)
        (transportMatrix inputRelabel previousRelabel valuePrevious)
        (transportRows
          (genuineLayerWeightEquiv [input, output]
            (inputRelabel, (outputRelabel, PUnit.unit)))
          queries)
        (transportRows
          (genuineLayerWeightEquiv [input, output]
            (inputRelabel, (outputRelabel, PUnit.unit)))
          keys)
        (transportRows
          (genuineLayerWeightEquiv [input, output]
            (inputRelabel, (outputRelabel, PUnit.unit)))
          values)
        (genuineLayerWeightEquiv [input, output]
          (inputRelabel, (outputRelabel, PUnit.unit)) coordinate)
        channel =
      layeredNeuralFunctionalAttentionFrom
        globalQueries globalKeys globalValues input [output] embedLeft
        keyPrevious valuePrevious queries keys values
        coordinate channel := by
  let permutation :
      LayerNeuronPermutation [input, output] :=
    (inputRelabel, (outputRelabel, PUnit.unit))
  cases coordinate with
  | inl pair =>
      rcases pair with ⟨row, column⟩
      have coordinateTransport :
          genuineLayerWeightEquiv [input, output] permutation
              (Sum.inl (row, column)) =
            Sum.inl (outputRelabel row, inputRelabel column) := by
        rfl
      have embedAt :
          embedRight
              (Sum.inl (outputRelabel row, inputRelabel column)) =
            globalRelabel (embedLeft (Sum.inl (row, column))) := by
        rw [← coordinateTransport]
        exact embedTransport (Sum.inl (row, column))
      unfold layeredNeuralFunctionalAttentionFrom
      rw [coordinateTransport]
      rw [firstWeightMatrix_transport permutation queries]
      rw [firstWeightMatrix_transport permutation keys]
      rw [firstWeightMatrix_transport permutation values]
      rw [embedAt]
      simpa [permutation,
        transportMatrix_emptyNextWeight outputRelabel] using
        neuralFunctionalAttentionEntry_transport
          previousRelabel inputRelabel outputRelabel
          (Equiv.refl PEmpty.{u + 1}) globalRelabel
          (firstWeightMatrix queries)
          keyPrevious
          (firstWeightMatrix keys)
          (emptyNextWeight
            (Current := output.carrier) (Channel := Channel) :
              PEmpty.{u + 1} → output.carrier → Channel → ℝ)
          valuePrevious
          (firstWeightMatrix values)
          (emptyNextWeight
            (Current := output.carrier) (Channel := Channel) :
              PEmpty.{u + 1} → output.carrier → Channel → ℝ)
          globalQueries globalKeys globalValues
          row column (embedLeft (Sum.inl (row, column))) channel
  | inr empty =>
      exact nomatch empty

/-- At a nonterminal weight matrix, the executable local branch commutes
with the same relabeling of the shared hidden layer on the current matrix's
rows and the following matrix's columns. -/
theorem layeredNeuralFunctionalAttentionFrom_head_transport
    {GlobalCoordinate : Type uGlobal}
    {Previous : Type u}
    {Channel : Type uChannel}
    [Fintype GlobalCoordinate] [Fintype Previous] [Fintype Channel]
    (globalRelabel : Equiv.Perm GlobalCoordinate)
    (previousRelabel : Equiv.Perm Previous)
    (input output next : FiniteNeuronLayer.{u})
    (rest : List (FiniteNeuronLayer.{u}))
    (inputRelabel : Equiv.Perm input.carrier)
    (outputRelabel : Equiv.Perm output.carrier)
    (nextRelabel : Equiv.Perm next.carrier)
    (restPermutation : LayerNeuronPermutation rest)
    (embedLeft embedRight :
      LayeredWeightCoordinate (input :: output :: next :: rest) →
        GlobalCoordinate)
    (embedTransport :
      ∀ coordinate,
        embedRight
            (genuineLayerWeightEquiv
              (input :: output :: next :: rest)
              (inputRelabel,
                (outputRelabel,
                  (nextRelabel, restPermutation)))
              coordinate) =
          globalRelabel (embedLeft coordinate))
    (globalQueries globalKeys globalValues :
      GlobalCoordinate → Channel → ℝ)
    (keyPrevious valuePrevious :
      input.carrier → Previous → Channel → ℝ)
    (queries keys values :
      LayeredWeightFeatures
        (input :: output :: next :: rest) Channel)
    (row : output.carrier) (column : input.carrier)
    (channel : Channel) :
    layeredNeuralFunctionalAttentionFrom
        (transportRows globalRelabel globalQueries)
        (transportRows globalRelabel globalKeys)
        (transportRows globalRelabel globalValues)
        input (output :: next :: rest) embedRight
        (transportMatrix inputRelabel previousRelabel keyPrevious)
        (transportMatrix inputRelabel previousRelabel valuePrevious)
        (transportRows
          (genuineLayerWeightEquiv
            (input :: output :: next :: rest)
            (inputRelabel,
              (outputRelabel, (nextRelabel, restPermutation))))
          queries)
        (transportRows
          (genuineLayerWeightEquiv
            (input :: output :: next :: rest)
            (inputRelabel,
              (outputRelabel, (nextRelabel, restPermutation))))
          keys)
        (transportRows
          (genuineLayerWeightEquiv
            (input :: output :: next :: rest)
            (inputRelabel,
              (outputRelabel, (nextRelabel, restPermutation))))
          values)
        (genuineLayerWeightEquiv
          (input :: output :: next :: rest)
          (inputRelabel,
            (outputRelabel, (nextRelabel, restPermutation)))
          (Sum.inl (row, column)))
        channel =
      layeredNeuralFunctionalAttentionFrom
        globalQueries globalKeys globalValues
        input (output :: next :: rest) embedLeft
        keyPrevious valuePrevious queries keys values
        (Sum.inl (row, column)) channel := by
  let permutation :
      LayerNeuronPermutation (input :: output :: next :: rest) :=
    (inputRelabel,
      (outputRelabel, (nextRelabel, restPermutation)))
  have coordinateTransport :
      genuineLayerWeightEquiv
          (input :: output :: next :: rest) permutation
          (Sum.inl (row, column)) =
        Sum.inl (outputRelabel row, inputRelabel column) := by
    rfl
  have embedAt :
      embedRight
          (Sum.inl (outputRelabel row, inputRelabel column)) =
        globalRelabel (embedLeft (Sum.inl (row, column))) := by
    rw [← coordinateTransport]
    exact embedTransport (Sum.inl (row, column))
  unfold layeredNeuralFunctionalAttentionFrom
  rw [coordinateTransport]
  rw [firstWeightMatrix_transport permutation queries]
  rw [firstWeightMatrix_transport permutation keys]
  rw [firstWeightMatrix_transport permutation values]
  rw [tailWeightFeatures_transport permutation keys]
  rw [tailWeightFeatures_transport permutation values]
  rw [firstWeightMatrix_transport permutation.2
    (tailWeightFeatures keys)]
  rw [firstWeightMatrix_transport permutation.2
    (tailWeightFeatures values)]
  rw [embedAt]
  simpa [permutation] using
    neuralFunctionalAttentionEntry_transport
      previousRelabel inputRelabel outputRelabel nextRelabel
      globalRelabel
      (firstWeightMatrix queries)
      keyPrevious
      (firstWeightMatrix keys)
      (firstWeightMatrix (tailWeightFeatures keys))
      valuePrevious
      (firstWeightMatrix values)
      (firstWeightMatrix (tailWeightFeatures values))
      globalQueries globalKeys globalValues
      row column (embedLeft (Sum.inl (row, column))) channel

/-! ## Arbitrary-depth equivariance -/

/-- The complete recursive implementation commutes with every compatible
global coordinate relabeling and every genuine layerwise neuron
relabeling, at arbitrary heterogeneous depth. -/
theorem layeredNeuralFunctionalAttentionFrom_transport
    {GlobalCoordinate : Type uGlobal}
    {Previous : Type u}
    {Channel : Type uChannel}
    [Fintype GlobalCoordinate] [Fintype Previous] [Fintype Channel]
    (globalRelabel : Equiv.Perm GlobalCoordinate)
    (previousRelabel : Equiv.Perm Previous)
    (input : FiniteNeuronLayer.{u})
    (tail : List (FiniteNeuronLayer.{u}))
    (permutation : LayerNeuronPermutation (input :: tail))
    (embedLeft embedRight :
      LayeredWeightCoordinate (input :: tail) → GlobalCoordinate)
    (embedTransport :
      ∀ coordinate,
        embedRight
            (genuineLayerWeightEquiv (input :: tail)
              permutation coordinate) =
          globalRelabel (embedLeft coordinate))
    (globalQueries globalKeys globalValues :
      GlobalCoordinate → Channel → ℝ)
    (keyPrevious valuePrevious :
      input.carrier → Previous → Channel → ℝ)
    (queries keys values :
      LayeredWeightFeatures (input :: tail) Channel)
    (coordinate : LayeredWeightCoordinate (input :: tail))
    (channel : Channel) :
    layeredNeuralFunctionalAttentionFrom
        (transportRows globalRelabel globalQueries)
        (transportRows globalRelabel globalKeys)
        (transportRows globalRelabel globalValues)
        input tail embedRight
        (transportMatrix permutation.1 previousRelabel keyPrevious)
        (transportMatrix permutation.1 previousRelabel valuePrevious)
        (transportRows
          (genuineLayerWeightEquiv (input :: tail) permutation)
          queries)
        (transportRows
          (genuineLayerWeightEquiv (input :: tail) permutation)
          keys)
        (transportRows
          (genuineLayerWeightEquiv (input :: tail) permutation)
          values)
        (genuineLayerWeightEquiv (input :: tail)
          permutation coordinate)
        channel =
      layeredNeuralFunctionalAttentionFrom
        globalQueries globalKeys globalValues
        input tail embedLeft
        keyPrevious valuePrevious queries keys values
        coordinate channel := by
  induction tail generalizing input Previous with
  | nil =>
      exact nomatch coordinate
  | cons output rest ih =>
      cases rest with
      | nil =>
          rcases permutation with
            ⟨inputRelabel, outputRelabel, terminal⟩
          cases terminal
          exact
            layeredNeuralFunctionalAttentionFrom_last_transport
              globalRelabel previousRelabel input output
              inputRelabel outputRelabel
              embedLeft embedRight embedTransport
              globalQueries globalKeys globalValues
              keyPrevious valuePrevious queries keys values
              coordinate channel
      | cons next rest =>
          rcases permutation with
            ⟨inputRelabel, outputRelabel,
              nextRelabel, restPermutation⟩
          cases coordinate with
          | inl pair =>
              rcases pair with ⟨row, column⟩
              exact
                layeredNeuralFunctionalAttentionFrom_head_transport
                  globalRelabel previousRelabel
                  input output next rest
                  inputRelabel outputRelabel nextRelabel
                  restPermutation
                  embedLeft embedRight embedTransport
                  globalQueries globalKeys globalValues
                  keyPrevious valuePrevious queries keys values
                  row column channel
          | inr later =>
              have tailEmbedTransport :
                  ∀ tailCoordinate,
                    (fun coordinate =>
                        embedRight (Sum.inr coordinate))
                        (genuineLayerWeightEquiv
                          (output :: next :: rest)
                          (outputRelabel,
                            (nextRelabel, restPermutation))
                          tailCoordinate) =
                      globalRelabel
                        ((fun coordinate =>
                            embedLeft (Sum.inr coordinate))
                          tailCoordinate) := by
                intro tailCoordinate
                exact embedTransport (Sum.inr tailCoordinate)
              unfold layeredNeuralFunctionalAttentionFrom
              rw [firstWeightMatrix_transport
                (input := input) (output := output)
                (rest := next :: rest)
                (inputRelabel,
                  (outputRelabel,
                    (nextRelabel, restPermutation))) keys]
              rw [firstWeightMatrix_transport
                (input := input) (output := output)
                (rest := next :: rest)
                (inputRelabel,
                  (outputRelabel,
                    (nextRelabel, restPermutation))) values]
              rw [tailWeightFeatures_transport
                (input := input) (output := output)
                (rest := next :: rest)
                (inputRelabel,
                  (outputRelabel,
                    (nextRelabel, restPermutation))) queries]
              rw [tailWeightFeatures_transport
                (input := input) (output := output)
                (rest := next :: rest)
                (inputRelabel,
                  (outputRelabel,
                    (nextRelabel, restPermutation))) keys]
              rw [tailWeightFeatures_transport
                (input := input) (output := output)
                (rest := next :: rest)
                (inputRelabel,
                  (outputRelabel,
                    (nextRelabel, restPermutation))) values]
              exact
                ih inputRelabel output
                  (outputRelabel,
                    (nextRelabel, restPermutation))
                  (fun coordinate => embedLeft (Sum.inr coordinate))
                  (fun coordinate => embedRight (Sum.inr coordinate))
                  tailEmbedTransport
                  (firstWeightMatrix keys)
                  (firstWeightMatrix values)
                  (tailWeightFeatures queries)
                  (tailWeightFeatures keys)
                  (tailWeightFeatures values)
                  later

/-- Crown theorem: the actual boundary-aware arbitrary-depth
neural-functional attention implementation is equivariant under the genuine
layerwise neuron-permutation action. -/
theorem layeredNeuralFunctionalAttention_transport
    {Channel : Type uChannel} [Fintype Channel]
    (layers : List (FiniteNeuronLayer.{u}))
    (permutation : LayerNeuronPermutation layers)
    (queries keys values : LayeredWeightFeatures layers Channel)
    (coordinate : LayeredWeightCoordinate layers)
    (channel : Channel) :
    layeredNeuralFunctionalAttention layers
        (transportRows
          (genuineLayerWeightEquiv layers permutation) queries)
        (transportRows
          (genuineLayerWeightEquiv layers permutation) keys)
        (transportRows
          (genuineLayerWeightEquiv layers permutation) values)
        (genuineLayerWeightEquiv layers permutation coordinate)
        channel =
      layeredNeuralFunctionalAttention layers
        queries keys values coordinate channel := by
  cases layers with
  | nil =>
      exact nomatch coordinate
  | cons input tail =>
      unfold layeredNeuralFunctionalAttention
      simpa [transportMatrix_emptyPreviousWeight permutation.1] using
        layeredNeuralFunctionalAttentionFrom_transport
          (genuineLayerWeightEquiv (input :: tail) permutation)
          (Equiv.refl PEmpty.{u + 1})
          input tail permutation id id
          (fun _ => rfl)
          queries keys values
          (emptyPreviousWeight
            (Middle := input.carrier) (Channel := Channel) :
              input.carrier → PEmpty.{u + 1} → Channel → ℝ)
          (emptyPreviousWeight
            (Middle := input.carrier) (Channel := Channel) :
              input.carrier → PEmpty.{u + 1} → Channel → ℝ)
          queries keys values coordinate channel

namespace LayeredNeuralFunctionalAttentionFixtures

abbrev oneMatrixShape : List FiniteNeuronLayer :=
  [LayeredWeightSpaceFixtures.finLayer 1,
    LayeredWeightSpaceFixtures.finLayer 1]

def oneMatrixFeature :
    LayeredWeightFeatures oneMatrixShape (Fin 1) :=
  fun _ _ => 1

/-- On a one-matrix network both absent neighbors are represented by empty
types, while the global point head still sees the real matrix coordinate. -/
theorem oneMatrix_uses_real_coordinate :
    layeredNeuralFunctionalAttention oneMatrixShape
        oneMatrixFeature oneMatrixFeature oneMatrixFeature
        (Sum.inl (0, 0)) 0 =
      neuralFunctionalAttentionEntry
        (firstWeightMatrix oneMatrixFeature)
        (emptyPreviousWeight
          (Middle := Fin 1) (Channel := Fin 1))
        (firstWeightMatrix oneMatrixFeature)
        (emptyNextWeight
          (Current := Fin 1) (Channel := Fin 1))
        (emptyPreviousWeight
          (Middle := Fin 1) (Channel := Fin 1))
        (firstWeightMatrix oneMatrixFeature)
        (emptyNextWeight
          (Current := Fin 1) (Channel := Fin 1))
        oneMatrixFeature oneMatrixFeature oneMatrixFeature
        0 0 (Sum.inl (0, 0)) 0 := by
  unfold layeredNeuralFunctionalAttention
    layeredNeuralFunctionalAttentionFrom
  rfl

/-- The global point-head coordinate is not replaced by an empty boundary
coordinate. -/
theorem oneMatrix_global_point_head_is_one :
    pointWeightAttention
      oneMatrixFeature oneMatrixFeature oneMatrixFeature
        (Sum.inl (0, 0)) 0 = 1 := by
  letI : Nonempty (LayeredWeightCoordinate oneMatrixShape) :=
    ⟨Sum.inl (0, 0)⟩
  unfold pointWeightAttention scaledDotProductAttention
  change
    softmaxAttention
        (fun key : LayeredWeightCoordinate oneMatrixShape =>
          scaledAttentionDotScore
            (oneMatrixFeature (Sum.inl (0, 0)))
            (oneMatrixFeature key))
        (fun _ : LayeredWeightCoordinate oneMatrixShape =>
          fun _ : Fin 1 => (1 : ℝ))
        0 =
      1
  simpa using
    congrFun
      (softmaxAttention_const
        (fun key : LayeredWeightCoordinate oneMatrixShape =>
          scaledAttentionDotScore
            (oneMatrixFeature (Sum.inl (0, 0)))
            (oneMatrixFeature key))
        (fun _ : Fin 1 => (1 : ℝ)))
      0

/-- A cross-matrix coordinate swap cannot be represented by any genuine
layerwise neuron relabeling, so it lies outside the crown theorem's exact
symmetry group. -/
theorem crossLayerCoordinateSwap_is_not_genuine :
    ¬ ∃ permutation :
        LayerNeuronPermutation
          LayeredWeightSpaceFixtures.tinyThreeLayerShape,
      genuineLayerWeightEquiv
          LayeredWeightSpaceFixtures.tinyThreeLayerShape
          permutation =
        LayeredWeightSpaceFixtures.crossLayerSwap := by
  rintro ⟨permutation, equality⟩
  have preserves :=
    genuineLayerWeightEquiv_preserves_layer
      LayeredWeightSpaceFixtures.tinyThreeLayerShape
      permutation
      LayeredWeightSpaceFixtures.firstIncoming
  rw [equality] at preserves
  obtain ⟨changed, original⟩ :=
    LayeredWeightSpaceFixtures.crossLayerSwap_changes_layer
  omega

end LayeredNeuralFunctionalAttentionFixtures

#print axioms
  layeredNeuralFunctionalAttentionFrom_last_transport
#print axioms
  layeredNeuralFunctionalAttentionFrom_head_transport
#print axioms
  layeredNeuralFunctionalAttentionFrom_transport
#print axioms
  layeredNeuralFunctionalAttention_transport
#print axioms
  LayeredNeuralFunctionalAttentionFixtures.oneMatrix_uses_real_coordinate
#print axioms
  LayeredNeuralFunctionalAttentionFixtures.oneMatrix_global_point_head_is_one
#print axioms
  LayeredNeuralFunctionalAttentionFixtures.crossLayerCoordinateSwap_is_not_genuine

end

end Mettapedia.MachineLearning.NeuralNetworks
