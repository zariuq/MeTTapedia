import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.Core

/-!
# Linear attention as a fast-weight memory

Schlag, Irie, and Schmidhuber (2021), *Linear Transformers Are Secretly Fast
Weight Programmers*, identify unnormalized linear self-attention with a
sequential fast-weight program:

* Equations (8)--(11) accumulate value/key outer products and read the
  resulting matrix at a query;
* Equations (20)--(25) replace pure accumulation by a delta-rule instruction
  that first reads the old key association and then corrects it.

This file proves the recursive/batch equivalence for arbitrary finite key and
value coordinates.  It then isolates the editability boundary: additive
writes accumulate at a repeated unit key, whereas a unit-rate delta write
replaces that key's value exactly.  A delta write leaves every orthogonal
query unchanged, while nonorthogonal keys produce an explicit crosstalk term.

Normalization and learned key/value generation are separate from this memory
algebra.  No capacity or empirical retrieval claim is inferred merely from
the finite identities below.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace FastWeightMemory

noncomputable section

open scoped BigOperators

variable {Key Value : Type*} [Fintype Key]

/-- A finite fast-weight matrix mapping key coordinates to value
coordinates. -/
abbrev Memory (Value Key : Type*) :=
  Matrix Value Key ℝ

/-- One self-invented key/value programming instruction. -/
structure Association (Key Value : Type*) where
  key : Key → ℝ
  value : Value → ℝ

/-- Read a fast-weight matrix at a query. -/
def read
    (memory : Memory Value Key) (query : Key → ℝ) : Value → ℝ :=
  Matrix.mulVec memory query

/-- The additive outer-product instruction in Equations (9)--(10). -/
def additiveWrite
    (memory : Memory Value Key)
    (value : Value → ℝ) (key : Key → ℝ) :
    Memory Value Key :=
  memory + Matrix.vecMulVec value key

/-- Contribution of one association to the unnormalized attention read. -/
def contribution
    (association : Association Key Value)
    (query : Key → ℝ) : Value → ℝ :=
  (association.key ⬝ᵥ query) • association.value

/-- Execute additive programming instructions in stream order. -/
def writeAll :
    List (Association Key Value) →
      Memory Value Key → Memory Value Key
  | [], memory => memory
  | association :: associations, memory =>
      writeAll associations
        (additiveWrite memory association.value association.key)

/-- One outer-product write contributes its value scaled by key/query
similarity. -/
theorem read_additiveWrite
    (memory : Memory Value Key)
    (value : Value → ℝ) (key query : Key → ℝ) :
    read (additiveWrite memory value key) query =
      read memory query + (key ⬝ᵥ query) • value := by
  simp only [read, additiveWrite, Matrix.add_mulVec,
    Matrix.vecMulVec_mulVec]
  simp

/-- Exact streamed form of the linear-attention numerator: recursively
programming the matrix equals adding every batch key/value contribution. -/
theorem read_writeAll
    (associations : List (Association Key Value))
    (memory : Memory Value Key) (query : Key → ℝ) :
    read (writeAll associations memory) query =
      read memory query +
        (associations.map (fun association =>
          contribution association query)).sum := by
  induction associations generalizing memory with
  | nil =>
      simp [writeAll]
  | cons association associations ih =>
      rw [writeAll, ih, read_additiveWrite]
      simp only [List.map_cons, List.sum_cons, contribution]
      abel

/-- Equations (8)--(11): from zero memory, a recursive fast-weight program
and unnormalized linear self-attention give exactly the same output. -/
theorem zeroMemory_writeAll_eq_linearAttention
    (associations : List (Association Key Value))
    (query : Key → ℝ) :
    read (writeAll associations 0) query =
      (associations.map (fun association =>
        contribution association query)).sum := by
  rw [read_writeAll]
  simp [read]

/-- Exact two-association crosstalk formula at the first unit key. -/
theorem read_twoAssociations_at_first
    (firstValue secondValue : Value → ℝ)
    (firstKey secondKey : Key → ℝ)
    (firstUnit : firstKey ⬝ᵥ firstKey = 1) :
    read
        (writeAll
          [⟨firstKey, firstValue⟩, ⟨secondKey, secondValue⟩] 0)
        firstKey =
      firstValue + (secondKey ⬝ᵥ firstKey) • secondValue := by
  rw [read_writeAll]
  simp [read, contribution, firstUnit]

/-- Orthogonal keys eliminate the second association's retrieval
interference exactly. -/
theorem read_twoAssociations_eq_first_of_orthogonal
    (firstValue secondValue : Value → ℝ)
    (firstKey secondKey : Key → ℝ)
    (firstUnit : firstKey ⬝ᵥ firstKey = 1)
    (orthogonal : secondKey ⬝ᵥ firstKey = 0) :
    read
        (writeAll
          [⟨firstKey, firstValue⟩, ⟨secondKey, secondValue⟩] 0)
        firstKey =
      firstValue := by
  rw [read_twoAssociations_at_first firstValue secondValue
    firstKey secondKey firstUnit, orthogonal]
  simp

/-- For nonorthogonal keys, the exact deviation from the first stored value
is the cross-key similarity times the second value. -/
theorem read_twoAssociations_crosstalk_exact
    (firstValue secondValue : Value → ℝ)
    (firstKey secondKey : Key → ℝ)
    (firstUnit : firstKey ⬝ᵥ firstKey = 1) :
    read
          (writeAll
            [⟨firstKey, firstValue⟩, ⟨secondKey, secondValue⟩] 0)
          firstKey -
        firstValue =
      (secondKey ⬝ᵥ firstKey) • secondValue := by
  rw [read_twoAssociations_at_first firstValue secondValue
    firstKey secondKey firstUnit]
  abel

/-! ## Delta-rule editing -/

/-- The source's delta-rule instruction: read the old association, write a
rate-scaled value error at the same key, and leave the rest of the matrix
unchanged. -/
def deltaWrite
    (memory : Memory Value Key) (rate : ℝ)
    (value : Value → ℝ) (key : Key → ℝ) :
    Memory Value Key :=
  memory +
    rate • Matrix.vecMulVec (value - read memory key) key

/-- Exact effect of a delta write at an arbitrary query. -/
theorem read_deltaWrite
    (memory : Memory Value Key) (rate : ℝ)
    (value : Value → ℝ) (key query : Key → ℝ) :
    read (deltaWrite memory rate value key) query =
      read memory query +
        (rate * (key ⬝ᵥ query)) •
          (value - read memory key) := by
  simp only [read, deltaWrite, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp
  module

/-- At a unit key, the delta rule interpolates exactly between the old and
new values, recovering Equation (22). -/
theorem read_deltaWrite_at_unitKey
    (memory : Memory Value Key) (rate : ℝ)
    (value : Value → ℝ) (key : Key → ℝ)
    (unitKey : key ⬝ᵥ key = 1) :
    read (deltaWrite memory rate value key) key =
      (1 - rate) • read memory key + rate • value := by
  rw [read_deltaWrite, unitKey]
  module

/-- Unit-rate delta programming replaces a unit key's association exactly. -/
theorem read_deltaWrite_rateOne
    (memory : Memory Value Key)
    (value : Value → ℝ) (key : Key → ℝ)
    (unitKey : key ⬝ᵥ key = 1) :
    read (deltaWrite memory 1 value key) key = value := by
  rw [read_deltaWrite_at_unitKey memory 1 value key unitKey]
  simp

/-- A delta correction at one key cannot change the read at an orthogonal
query. -/
theorem deltaWrite_preserves_orthogonalQuery
    (memory : Memory Value Key) (rate : ℝ)
    (value : Value → ℝ) (key query : Key → ℝ)
    (orthogonal : key ⬝ᵥ query = 0) :
    read (deltaWrite memory rate value key) query =
      read memory query := by
  rw [read_deltaWrite, orthogonal]
  simp

/-- In contrast, an additive write at a unit key adds the new value to the
old read rather than replacing it. -/
theorem read_additiveWrite_at_unitKey
    (memory : Memory Value Key)
    (value : Value → ℝ) (key : Key → ℝ)
    (unitKey : key ⬝ᵥ key = 1) :
    read (additiveWrite memory value key) key =
      read memory key + value := by
  rw [read_additiveWrite, unitKey]
  simp

/-! ## Executable repeated-key boundary -/

abbrev ScalarIndex := Fin 1

noncomputable def scalarKey : ScalarIndex → ℝ :=
  fun _ => 1

noncomputable def scalarValue (value : ℝ) : ScalarIndex → ℝ :=
  fun _ => value

noncomputable def scalarMemory
    (value : ℝ) : Memory ScalarIndex ScalarIndex :=
  Matrix.vecMulVec (scalarValue value) scalarKey

theorem scalarKey_unit :
    scalarKey ⬝ᵥ scalarKey = 1 := by
  simp [scalarKey, dotProduct]

/-- Starting from the association `key ↦ 3`, an additive write of `5` at
the same key returns `8`: accumulation is not replacement. -/
theorem additive_repeatedKey_accumulates :
    read
        (additiveWrite (scalarMemory 3) (scalarValue 5) scalarKey)
        scalarKey 0 =
      8 := by
  norm_num [read, additiveWrite, scalarMemory, scalarValue, scalarKey,
    Matrix.mulVec, Matrix.vecMulVec, dotProduct]

/-- The unit-rate delta instruction updates the same memory to return the
requested replacement value `5`. -/
theorem delta_repeatedKey_replaces :
    read
        (deltaWrite (scalarMemory 3) 1 (scalarValue 5) scalarKey)
        scalarKey 0 =
      5 := by
  have replacement :=
    read_deltaWrite_rateOne
      (scalarMemory 3) (scalarValue 5) scalarKey scalarKey_unit
  exact congrFun replacement 0

#print axioms read_writeAll
#print axioms zeroMemory_writeAll_eq_linearAttention
#print axioms read_twoAssociations_crosstalk_exact
#print axioms read_deltaWrite
#print axioms read_deltaWrite_at_unitKey
#print axioms read_deltaWrite_rateOne
#print axioms deltaWrite_preserves_orthogonalQuery
#print axioms additive_repeatedKey_accumulates
#print axioms delta_repeatedKey_replaces

end

end FastWeightMemory

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
