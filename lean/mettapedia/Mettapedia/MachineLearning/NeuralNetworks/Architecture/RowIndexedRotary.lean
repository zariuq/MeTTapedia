import Mathlib.Data.Int.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.NormNum

/-!
# Row-indexed positional actions and relabeling

This module states the exact symmetry boundary of row-indexed rotary attention.
A graph relabeling transports content, but the positional action remains tied
to serialized rows.  Equivariance therefore requires preservation of every
pairwise positional kernel; ordinary graph isomorphism alone is insufficient.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

universe uNode uVector uScalar

/-- Transport node-indexed content along a permutation. -/
def transportContent {Node : Type uNode} {Vector : Type uVector}
    (permutation : Node ≃ Node) (content : Node → Vector) : Node → Vector :=
  fun node => content (permutation.symm node)

/-- One raw positional query-key score. -/
def positionalScore {Node : Type uNode} {Vector : Type uVector}
    {Scalar : Type uScalar}
    (positionAction : Node → Vector → Vector)
    (pairing : Vector → Vector → Scalar)
    (query key : Node → Vector) (source target : Node) : Scalar :=
  pairing (positionAction source (query source))
    (positionAction target (key target))

/-- A permutation preserves the pairwise positional kernel for every possible
query and key vector. -/
def RelativePositionCompatible {Node : Type uNode} {Vector : Type uVector}
    {Scalar : Type uScalar}
    (positionAction : Node → Vector → Vector)
    (pairing : Vector → Vector → Scalar)
    (permutation : Node ≃ Node) : Prop :=
  ∀ source target query key,
    pairing (positionAction (permutation source) query)
        (positionAction (permutation target) key) =
      pairing (positionAction source query) (positionAction target key)

/-- Pairwise compatibility is sufficient for exact raw-score equivariance
after transporting content. -/
theorem positionalScore_relabel
    {Node : Type uNode} {Vector : Type uVector} {Scalar : Type uScalar}
    (positionAction : Node → Vector → Vector)
    (pairing : Vector → Vector → Scalar)
    (permutation : Node ≃ Node)
    (compatible : RelativePositionCompatible positionAction pairing permutation)
    (query key : Node → Vector) (source target : Node) :
    positionalScore positionAction pairing
        (transportContent permutation query)
        (transportContent permutation key)
        (permutation source) (permutation target) =
      positionalScore positionAction pairing query key source target := by
  simpa [positionalScore, transportContent] using
    compatible source target (query source) (key target)

/-- Commuting pointwise with every positional action is a stronger sufficient
condition for pairwise compatibility. -/
theorem relativePositionCompatible_of_pointwise
    {Node : Type uNode} {Vector : Type uVector} {Scalar : Type uScalar}
    (positionAction : Node → Vector → Vector)
    (pairing : Vector → Vector → Scalar)
    (permutation : Node ≃ Node)
    (commutes : ∀ node vector,
      positionAction (permutation node) vector = positionAction node vector) :
    RelativePositionCompatible positionAction pairing permutation := by
  intro source target query key
  rw [commutes source query, commutes target key]

/-- The branch with no positional action is equivariant under every
permutation. -/
theorem identityPosition_relativePositionCompatible
    {Node : Type uNode} {Vector : Type uVector} {Scalar : Type uScalar}
    (pairing : Vector → Vector → Scalar) (permutation : Node ≃ Node) :
    RelativePositionCompatible (fun _ vector => vector) pairing permutation := by
  intro source target query key
  rfl

/-- Adding an equal transported relation bias preserves score equality. -/
theorem relationAwareScore_eq
    {Scalar : Type uScalar} [Add Scalar]
    {leftRaw rightRaw leftBias rightBias : Scalar}
    (rawEq : leftRaw = rightRaw) (biasEq : leftBias = rightBias) :
    leftRaw + leftBias = rightRaw + rightBias := by
  rw [rawEq, biasEq]

/-! ## A concrete even-width counterexample -/

abbrev IntVec2 := Int × Int

def dotIntVec2 (left right : IntVec2) : Int :=
  left.1 * right.1 + left.2 * right.2

/-- Row zero is unrotated; row one receives a quarter turn. -/
def twoRowQuarterTurn : Bool → IntVec2 → IntVec2
  | false, vector => vector
  | true, vector => (-vector.2, vector.1)

def boolSwap : Bool ≃ Bool :=
  Equiv.swap false true

/-- Swapping two rows reverses their relative phase, so row-indexed rotary
scores need not commute with a graph relabeling. -/
theorem boolSwap_not_relativePositionCompatible :
    ¬RelativePositionCompatible twoRowQuarterTurn dotIntVec2 boolSwap := by
  intro compatible
  have scoreEq := compatible false true (1, 0) (0, 1)
  norm_num [twoRowQuarterTurn, dotIntVec2, boolSwap] at scoreEq

/-- The same witness computes unequal scores after and before relabeling. -/
theorem boolSwap_changes_positionalScore :
    let query : Bool → IntVec2 := fun _ => (1, 0)
    let key : Bool → IntVec2 := fun _ => (0, 1)
    positionalScore twoRowQuarterTurn dotIntVec2
        (transportContent boolSwap query) (transportContent boolSwap key)
        (boolSwap false) (boolSwap true) = 1 ∧
      positionalScore twoRowQuarterTurn dotIntVec2 query key false true = -1 := by
  norm_num [positionalScore, transportContent, twoRowQuarterTurn,
    dotIntVec2, boolSwap]

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
