import Mathlib

/-!
# Task-vector arithmetic

Ilharco et al., *Editing Models with Task Arithmetic* (arXiv:2212.04089),
Section 2, define a task vector as the coordinatewise difference between a
fine-tuned model and its pre-trained anchor.  They edit a compatible model by
adding a scaled task vector and study negation, addition, and analogies of the
form

`task C + (task B - task A)`.

This file gives exact finite- or infinite-coordinate real semantics for those
operations.  Applying a unit task vector to its own anchor recovers the
fine-tuned weights.  Negation extrapolates to `2 * anchor - fineTuned`.
Adding two task vectors at their shared anchor yields
`fineA + fineB - anchor`.  Applying the analogy expression at that anchor
cancels the anchor completely and yields `fineC + fineB - fineA`.

The shared-anchor condition is load-bearing.  A concrete one-coordinate
fixture shows that forming the three component vectors from different anchors
does not recover the common-anchor analogy result.  Parameter-shape
compatibility is represented structurally by requiring every model in an
expression to share the same coordinate type.

No theorem here claims that arithmetic edits improve task performance,
preserve control-task behavior, identify causal mechanisms, or establish the
source's empirical results.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace TaskVectorArithmetic

noncomputable section

variable {Coordinate : Type*}

/-- A parameter vector over one fixed architecture's coordinate type. -/
abbrev Parameters (Coordinate : Type*) :=
  Coordinate → ℝ

/-- Section 2's task vector: fine-tuned weights minus their pre-trained
anchor. -/
def taskVector
    (anchor fineTuned : Parameters Coordinate) :
    Parameters Coordinate :=
  fun coordinate => fineTuned coordinate - anchor coordinate

/-- Apply a scaled edit vector to compatible model parameters. -/
def applyVector
    (parameters : Parameters Coordinate) (scale : ℝ)
    (vector : Parameters Coordinate) :
    Parameters Coordinate :=
  fun coordinate =>
    parameters coordinate + scale * vector coordinate

/-- Pointwise addition of compatible edit vectors. -/
def add
    (first second : Parameters Coordinate) :
    Parameters Coordinate :=
  fun coordinate => first coordinate + second coordinate

/-- Pointwise subtraction of compatible edit vectors. -/
def sub
    (first second : Parameters Coordinate) :
    Parameters Coordinate :=
  fun coordinate => first coordinate - second coordinate

/-- A unit task-vector edit applied to its own anchor exactly recovers the
fine-tuned checkpoint. -/
@[simp] theorem applyVector_taskVector_one
    (anchor fineTuned : Parameters Coordinate) :
    applyVector anchor 1 (taskVector anchor fineTuned) =
      fineTuned := by
  funext coordinate
  simp [applyVector, taskVector]

/-- A zero-scale edit preserves the model exactly. -/
@[simp] theorem applyVector_zero
    (parameters vector : Parameters Coordinate) :
    applyVector parameters 0 vector = parameters := by
  funext coordinate
  simp [applyVector]

/-- Negating a task vector at its anchor is extrapolation through the anchor,
not recovery of either endpoint. -/
theorem applyVector_neg_taskVector
    (anchor fineTuned : Parameters Coordinate) :
    applyVector anchor 1
        (fun coordinate => -taskVector anchor fineTuned coordinate) =
      fun coordinate => 2 * anchor coordinate - fineTuned coordinate := by
  funext coordinate
  simp [applyVector, taskVector]
  ring

/-- Adding two task vectors at their common anchor subtracts that anchor once
after combining the two fine-tuned checkpoints. -/
theorem applyVector_add_two_taskVectors
    (anchor fineA fineB : Parameters Coordinate) :
    applyVector anchor 1
        (add (taskVector anchor fineA) (taskVector anchor fineB)) =
      fun coordinate =>
        fineA coordinate + fineB coordinate - anchor coordinate := by
  funext coordinate
  simp [applyVector, add, taskVector]
  ring

/-- The source analogy edit vector `task C + (task B - task A)`. -/
def analogyVector
    (anchor fineA fineB fineC : Parameters Coordinate) :
    Parameters Coordinate :=
  add (taskVector anchor fineC)
    (sub (taskVector anchor fineB) (taskVector anchor fineA))

/-- Applying the analogy vector at the shared anchor cancels the anchor and
recovers the affine combination `fineC + fineB - fineA`. -/
theorem applyVector_analogyVector
    (anchor fineA fineB fineC : Parameters Coordinate) :
    applyVector anchor 1
        (analogyVector anchor fineA fineB fineC) =
      fun coordinate =>
        fineC coordinate + fineB coordinate - fineA coordinate := by
  funext coordinate
  simp [applyVector, analogyVector, add, sub, taskVector]
  ring

/-- Analogy construction when each component task vector is formed from a
potentially different anchor. -/
def mixedAnchorAnalogyVector
    (anchorA anchorB anchorC fineA fineB fineC :
      Parameters Coordinate) :
    Parameters Coordinate :=
  add (taskVector anchorC fineC)
    (sub (taskVector anchorB fineB) (taskVector anchorA fineA))

/-- Exact mixed-anchor expansion.  The uncancelled anchor offsets exhibit the
boundary hidden by the common-anchor notation. -/
theorem applyVector_mixedAnchorAnalogyVector
    (base anchorA anchorB anchorC fineA fineB fineC :
      Parameters Coordinate) :
    applyVector base 1
        (mixedAnchorAnalogyVector
          anchorA anchorB anchorC fineA fineB fineC) =
      fun coordinate =>
        base coordinate +
          (fineC coordinate - anchorC coordinate) +
          ((fineB coordinate - anchorB coordinate) -
            (fineA coordinate - anchorA coordinate)) := by
  funext coordinate
  simp [applyVector, mixedAnchorAnalogyVector, add, sub, taskVector]
  ring

/-! ## Executable positive and negative fixtures -/

def scalarParameters (value : ℝ) : Parameters (Fin 1) :=
  fun _ => value

theorem scalar_task_vector_recovery :
    applyVector (scalarParameters 10) 1
        (taskVector (scalarParameters 10) (scalarParameters 14)) =
      scalarParameters 14 := by
  exact applyVector_taskVector_one _ _

theorem scalar_addition_and_negation :
    applyVector (scalarParameters 10) 1
        (add
          (taskVector (scalarParameters 10) (scalarParameters 14))
          (taskVector (scalarParameters 10) (scalarParameters 17))) =
        scalarParameters 21 ∧
      applyVector (scalarParameters 10) 1
        (fun coordinate =>
          -taskVector
            (scalarParameters 10) (scalarParameters 14) coordinate) =
        scalarParameters 6 := by
  constructor <;>
    funext coordinate <;>
    fin_cases coordinate <;>
    norm_num [applyVector, add, taskVector, scalarParameters]

theorem common_anchor_analogy :
    applyVector (scalarParameters 10) 1
        (analogyVector
          (scalarParameters 10)
          (scalarParameters 12)
          (scalarParameters 15)
          (scalarParameters 20)) =
      scalarParameters 23 := by
  funext coordinate
  fin_cases coordinate
  norm_num [applyVector, analogyVector, add, sub, taskVector,
    scalarParameters]

/-- Different component anchors leave residual offsets: the mixed construction
evaluates to `20`, not the common-anchor result `23`. -/
theorem mixed_anchors_break_analogy :
    applyVector (scalarParameters 10) 1
        (mixedAnchorAnalogyVector
          (scalarParameters 10)
          (scalarParameters 11)
          (scalarParameters 12)
          (scalarParameters 12)
          (scalarParameters 15)
          (scalarParameters 20)) =
        scalarParameters 20 ∧
      applyVector (scalarParameters 10) 1
        (mixedAnchorAnalogyVector
          (scalarParameters 10)
          (scalarParameters 11)
          (scalarParameters 12)
          (scalarParameters 12)
          (scalarParameters 15)
          (scalarParameters 20)) ≠
        scalarParameters 23 := by
  constructor
  · funext coordinate
    fin_cases coordinate
    norm_num [applyVector, mixedAnchorAnalogyVector, add, sub, taskVector,
      scalarParameters]
  · intro equality
    have atCoordinate := congrFun equality 0
    norm_num [applyVector, mixedAnchorAnalogyVector, add, sub, taskVector,
      scalarParameters] at atCoordinate

#print axioms applyVector_taskVector_one
#print axioms applyVector_zero
#print axioms applyVector_neg_taskVector
#print axioms applyVector_add_two_taskVectors
#print axioms applyVector_analogyVector
#print axioms applyVector_mixedAnchorAnalogyVector
#print axioms scalar_task_vector_recovery
#print axioms scalar_addition_and_negation
#print axioms common_anchor_analogy
#print axioms mixed_anchors_break_analogy

end

end TaskVectorArithmetic

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
